import check,search,problem,syntax,solver,logic,rep_graph,re
from rep_graph import vc_num, vc_offs, pc_true_hyp, Hyp, eq_hyp
from target_objects import functions, trace
from check import restr_others,split_visit_one_visit
from problem import inline_at_point
from syntax import mk_not, true_term, false_term, mk_implies, Expr, Type, unspecified_precond_term,mk_and
from rep_graph import mk_graph_slice, VisitCount, to_smt_expr
from search import eval_model_expr
import target_objects
import trace_refute
import stack_logic
import time

#tryFun must take exactly 1 argument
def downBinSearch(minimum, maximum, tryFun):
    upperBound = maximum 
    lowerBound = minimum
    while upperBound > lowerBound:
      print 'searching in %d - %d' % (lowerBound,upperBound)
      cur = (lowerBound + upperBound) / 2
      if tryFun(cur):
          upperBound = cur
      else:
          lowerBound = cur + 1
    assert upperBound == lowerBound
    ret = lowerBound
    return ret

def upDownBinSearch (minimum, maximum, tryFun):
    """performs a binary search between minimum and maximum, but does not start
    in the middle. instead it does a binary escalation up from the minimum
    first. this makes sense for ranges e.g. 2 - 1000000 where the bound is
    likely to be near the bottom of the range. it also avoids testing values
    more than twice as high as the bound, which may avoid some issues."""
    upperBound = 2 * minimum
    while upperBound < maximum:
      if tryFun (upperBound):
        return downBinSearch (minimum, upperBound, tryFun)
      else:
        upperBound *= 2
    if tryFun (maximum):
      return downBinSearch (minimum, maximum, tryFun)
    else:
      return None

def addr_of_node (preds, n):
  while not trace_refute.is_addr (n):
    [n] = preds[n]
  return n

def all_asm_functions ():
    ss = stack_logic.get_functions_with_tag ('ASM')
    return [s for s in ss if not stack_logic.is_instruction (s)]

call_site_set = {}

def build_call_site_set ():
    for f in all_asm_functions ():
      preds = logic.compute_preds (functions[f].nodes)
      for (n, node) in functions[f].nodes.iteritems ():
        if node.kind == 'Call':
          s = call_site_set.setdefault (node.fname, set ())
          s.add (addr_of_node (preds, n))
    call_site_set[('IsLoaded', None)] = True

def all_call_sites (f):
    if not call_site_set:
      build_call_site_set ()
    return list (call_site_set.get (f, []))

#naive binary search to find loop bounds
def findLoopBoundBS(p_n, p, restrs=None, hyps=None, try_seq=None):
    if hyps == None:
      hyps = []
    #print 'restrs: %s' % str(restrs)
    if try_seq == None:
        #bound_try_seq = [1,2,3,4,5,10,50,130,200,260]
        #bound_try_seq = [0,1,2,3,4,5,10,50,260]
        calls = [n for n in p.loop_body (p_n) if p.nodes[n].kind == 'Call']
        if calls:
          bound_try_seq = [0,1,20]
        else:
          bound_try_seq = [0,1,20,34]
    else:
        bound_try_seq = try_seq
    rep = mk_graph_slice (p, fast = True)
    #get the head
    #print 'Binary addr: %s' % toHexs(self.toPhyAddrs(p_loop_heads))
    loop_bound = None
    p_loop_heads = [n for n in p.loop_data if p.loop_data[n][0] == 'Head']
    print 'p_loop_heads: %s' % p_loop_heads
    
    if restrs == None: 
        others = [x for x in p_loop_heads if not x == p_n]
        #vc_options([concrete numbers], [offsets])
        restrs = tuple( [(n2, rep_graph.vc_options([0],[1])) for n2 in others] )
        
    print 'getting the initial bound'
    #try:
    index = tryLoopBound(p_n,p,bound_try_seq,rep,restrs = restrs, hyps=hyps)
    if index == -1:
        return None
    print 'got the initial bound %d' % bound_try_seq[index]
    
    #do a downward binary search to find the concrete loop bound
    if index == 0:
      loop_bound = bound_try_seq[0]
      print 'bound = %d' % loop_bound
      return loop_bound
    loop_bound = downBinSearch(bound_try_seq[index-1], bound_try_seq[index], lambda x: tryLoopBound(p_n,p,[x],rep,restrs=restrs, hyps=hyps, bin_return=True))
    print 'bound = %d' % loop_bound
    return loop_bound

def default_n_vc_cases (p, n):
  head = p.loop_id (n)
  general = [(n2, rep_graph.vc_options ([0], [1]))
  for n2 in p.loop_heads ()
  if n2 != head]

  if head:
    return [(n, tuple (general + [(head, rep_graph.vc_num (1))])),
         (n, tuple (general + [(head, rep_graph.vc_offs (1))]))]
  specific = [(head, rep_graph.vc_offs (1)) for _ in [1] if head]
  return [(n, tuple (general + specific))]

def callNodes(p, fs= None):
  ns = [n for n in p.nodes if p.nodes[n].kind == 'Call']
  if fs != None:
    ns = [n for n in ns if p.nodes[n].fname in fs]
  return ns

def noHaltHyps(split,p):
    ret = []
    all_halts = callNodes(p,fs=['halt'])
    for x in all_halts:
       ret += [rep_graph.pc_false_hyp((n_vc, p.node_tags[x][0]))
         for n_vc in default_n_vc_cases (p, x)]
    return ret

def tryLoopBound(p_n, p, bounds,rep,restrs =None, hints =None,kind = 'Number',bin_return = False,hyps = None):
    if restrs == None:
        restrs = ()
    if hints == None:
        hints = []
    if hyps == None:
      hyps = []
    tag = p.node_tags[p_n][0]
    from stack_logic import default_n_vc
    print 'trying bound: %s' % bounds
    ret_bounds = []
    for (index,i) in enumerate(bounds):
            print 'testing %d' % i
            restrs2 = restrs + ((p_n, VisitCount (kind, i)), )
            try:
                pc = rep.get_pc ((p_n, restrs2))
            except:
                print 'get_pc failed'
                if bin_return:
                    return False
                else: 
                    return -1
            #print 'got rep_.get_pc'
            restrs3 = restr_others (p, restrs2, 2)
            epc = rep.get_pc (('Err', restrs3), tag = tag)
            hyp = mk_implies (mk_not (epc), mk_not (pc))
            hyps = hyps + noHaltHyps(p_n,p)
            
            #hyps = [] 
            #print 'calling test_hyp_whyps'
            if rep.test_hyp_whyps (hyp, hyps):
                    print 'p_n %d: split limit found: %d' % (p_n, i)
                    if bin_return:
                      return True
                    return index
    if bin_return:
      return False
    print 'loop bound not found!'
    return -1
    assert False, 'failed to find loop bound for p_n %d' % p_n


def linear_eq_hyps_at_visit (tag, split, eqs, restrs, visit_num):
    details = (split, (0, 1), eqs)
    visit = split_visit_one_visit (tag, details, restrs, visit_num)
    start = split_visit_one_visit (tag, details, restrs, vc_num (0))
    from syntax import mk_word32, mk_plus, mk_var, word32T

    def mksub (v):
            return lambda exp: logic.var_subst (exp, {('%i', word32T) : v},
                    must_subst = False)
    zsub = mksub (mk_word32 (0))
    if visit_num.kind == 'Number':
            isub = mksub (mk_word32 (visit_num.n))
    else:
            isub = mksub (mk_plus (mk_var ('%n', word32T),
                    mk_word32 (visit_num.n)))

    hyps = [(Hyp ('PCImp', visit, start), '%s pc imp' % tag)]
    hyps += [(eq_hyp ((zsub (exp), start), (isub (exp), visit),
                            (split, 0)), '%s const' % tag)
                    for exp in eqs if logic.inst_eq_at_visit (exp, visit_num)]

    return hyps

def linear_eq_induct_base_checks (p, restrs, hyps, tag, split, eqs):
    tests = []
    details = (split, (0, 1), eqs)
    for i in [0, 1]:
        reach = split_visit_one_visit (tag, details, restrs, vc_num (i))
        nhyps = [pc_true_hyp (reach)]
        tests.extend ([(hyps + nhyps, hyp,
            'Base check (%s, %d) at induct step for %d' % (desc,
                i, split)) for (hyp, desc) in
            linear_eq_hyps_at_visit (tag, split, eqs,
                restrs, vc_num (i))])
    return tests

def linear_eq_induct_step_checks (p, restrs, hyps, tag, split,
                eqs_assume, eqs):
    details = (split, (0, 1), eqs_assume + eqs)
    cont = split_visit_one_visit (tag, details, restrs, vc_offs (1))
    hyps = ([pc_true_hyp (cont)] + hyps
            + [h for (h, _) in linear_eq_hyps_at_visit (tag, split,
                    eqs_assume + eqs, restrs, vc_offs (0))])

    return [(hyps, hyp, 'Induct check (%s) at inductive step for %d'
            % (desc, split))
        for (hyp, desc) in linear_eq_hyps_at_visit (tag, split, eqs,
            restrs, vc_offs (1))]

def get_linear_series_eqs (p, split, restrs, hyps, omit_standard = False):

    k = ('linear_series_eqs', split, restrs, tuple (hyps))
    if k in p.cached_analysis:
        if omit_standard:
          standard = set (search.mk_seq_eqs (p, split, 1, with_rodata = False))
          return set (p.cached_analysis[k]) - standard
        return p.cached_analysis[k]

    cands = search.mk_seq_eqs (p, split, 1, with_rodata = False)
    cands += candidate_additional_eqs (p, split)
    (tag, _) = p.node_tags[split]

    rep = rep_graph.mk_graph_slice (p, fast = True)

    def do_checks (eqs_assume, eqs):
        checks = (linear_eq_induct_step_checks (p, restrs, hyps, tag, split,
                eqs_assume, eqs)
            + linear_eq_induct_base_checks (p, restrs, hyps, tag, split, eqs))

        groups = check.proof_check_groups (checks)
        for group in groups:
            (res, _) = check.test_hyp_group (rep, group)
            if not res:
                return False
        return True

    eqs = []
    failed = []
    while cands:
        cand = cands.pop ()
        if do_checks (eqs, [cand]):
            eqs.append (cand)
            failed.reverse ()
            cands = failed + cands
            failed = []
        else:
            failed.append (cand)

    assert do_checks ([], eqs)
    p.cached_analysis[k] = eqs
    if omit_standard:
      standard = set (search.mk_seq_eqs (p, split, 1, with_rodata = False))
      return set (eqs) - standard
    return eqs

def get_linear_series_hyps (p, split, restrs, hyps):
    eqs = get_linear_series_eqs (p, split, restrs, hyps)
    (tag, _) = p.node_tags[split]
    hyps = [h for (h, _) in linear_eq_hyps_at_visit (tag, split, eqs,
             restrs, vc_offs (0))]
    return hyps

def get_induct_eq_hyp (p, split, restrs, n):
    details = (split, (0, 1), [])
    (tag, _) = p.node_tags[split]
    visit = split_visit_one_visit (tag, details, restrs, vc_offs (0))
    from syntax import mk_var, word32T, mk_word32
    return eq_hyp ((mk_var ('%n', word32T), visit),
        (mk_word32 (n), visit), (split, 0))

def is_zero (expr):
    return expr.kind == 'Num' and expr.val & ((1 << expr.typ.num) - 1) == 0

def candidate_additional_eqs (p, split):
    eq_vals = set ()
    def visitor (expr):
      if expr.is_op ('Equals') and expr.vals[0].typ.kind == 'Word':
        [x, y] = expr.vals
        eq_vals.update ([(x, y), (y, x)])
    for n in p.loop_body (split):
      p.nodes[n].visit (lambda x: (), visitor)
    for (x, y) in list (eq_vals):
        if is_zero (x) and y.is_op ('Plus'):
          [x, y] = y.vals
          eq_vals.add ((x, syntax.mk_uminus (y)))
          eq_vals.add ((y, syntax.mk_uminus (x)))
        elif is_zero (x) and y.is_op ('Minus'):
          [x, y] = y.vals
          eq_vals.add ((x, y))
          eq_vals.add ((y, x))

    loop = syntax.mk_var ('%i', syntax.word32T)
    minus_loop_step = syntax.mk_uminus (loop)

    vas = search.get_loop_var_analysis_at(p, split)
    ls_vas = dict ([(var, [data]) for (var, data) in vas
        if data[0] == 'LoopLinearSeries'])
    cmp_series = [(x, y, rew, offs) for (x, y) in eq_vals
        for (_, rew, offs) in ls_vas.get (x, [])]
    odd_eqs = []
    for (x, y, rew, offs) in cmp_series:
        x_init_cmp1 = syntax.mk_less_eq (x, rew (x, minus_loop_step))
        x_init_cmp2 = syntax.mk_less_eq (rew (x, minus_loop_step), x)
        fin_cmp1 = syntax.mk_less (x, y)
        fin_cmp2 = syntax.mk_less (y, x)
        odd_eqs.append (syntax.mk_eq (x_init_cmp1, fin_cmp1))
        odd_eqs.append (syntax.mk_eq (x_init_cmp2, fin_cmp1))
        odd_eqs.append (syntax.mk_eq (x_init_cmp1, fin_cmp2))
        odd_eqs.append (syntax.mk_eq (x_init_cmp2, fin_cmp2))

    ass_eqs = []
    var_deps = p.compute_var_dependencies ()
    for hook in target_objects.hooks ('extra_wcet_assertions'):
        for assn in hook (var_deps[split]):
            ass_eqs.append (assn)

    return odd_eqs + ass_eqs

extra_loop_consts = [2 ** 16]

call_ctxt_problems = []

avoid_C_information = [False]

def get_call_ctxt_problem (split, call_ctxt, timing = True):
    # time this for diagnostic reasons
    start = time.time ()
    from trace_refute import identify_function, build_compound_problem_with_links
    f = identify_function (call_ctxt, [split])
    for (ctxt2, p, hyps, addr_map) in call_ctxt_problems:
      if ctxt2 == (call_ctxt, f):
        return (p, hyps, addr_map)

    (p, hyps, addr_map) = build_compound_problem_with_links (call_ctxt, f)
    if avoid_C_information[0]:
      hyps = [h for h in hyps if not has_C_information (p, h)]
    call_ctxt_problems.append(((call_ctxt, f), p, hyps, addr_map))
    del call_ctxt_problems[: -20]

    end = time.time ()
    if timing:
      save_extra_timing ('GetProblem', call_ctxt + [split], end - start)

    return (p, hyps, addr_map)

def has_C_information (p, hyp):
    for (n_vc, tag) in hyp.visits ():
      if not p.hook_tag_hints.get (tag, None) == 'ASM':
        return True

known_bound_restr_hyps = {}

known_bounds = {}

def serialise_bound (addr, bound_info):
    if bound_info == None:
      return [hex(addr), "None", "None"]
    else:
      (bound, kind) = bound_info
      assert logic.is_int (bound)
      assert str (kind) == kind
      return [hex (addr), str (bound), kind]

def save_bound (glob, split_bin_addr, call_ctxt, prob_hash, prev_bounds, bound,
        time = None):
    f_names = [trace_refute.get_body_addrs_fun (x)
      for x in call_ctxt + [split_bin_addr]]
    loop_name = '<%s>' % ' -> '.join (f_names)
    comment = '# bound for loop in %s:' % loop_name
    ss = ['LoopBound'] + serialise_bound (split_bin_addr, bound)
    if glob:
      ss[0] = 'GlobalLoopBound'
    ss += [str (len (call_ctxt))] + map (hex, call_ctxt)
    ss += [str (prob_hash)]
    if glob:
      assert prev_bounds == None
    else:
      ss += [str (len (prev_bounds))]
      for (split, bound) in prev_bounds:
        ss += serialise_bound (split, bound)
    s = ' '.join (ss)
    f = open ('%s/LoopBounds.txt' % target_objects.target_dir, 'a')
    f.write (comment + '\n')
    f.write (s + '\n')
    if time != None:
      ctxt2 = call_ctxt + [split_bin_addr]
      ctxt2 = ' '.join ([str (len (ctxt2))] + map (hex, ctxt2))
      f.write ('LoopBoundTiming %s %s\n' % (ctxt2, time))
    f.close ()
    trace ('Found bound %s for 0x%x in %s.' % (bound, split_bin_addr,
      loop_name))

def save_extra_timing (nm, ctxt, time):
    ss = ['ExtraTiming', nm, str (len (ctxt))] + map (hex, ctxt) + [str(time)]
    f = open ('%s/LoopBounds.txt' % target_objects.target_dir, 'a')
    f.write (' '.join (ss) + '\n')
    f.close ()

def parse_bound (ss, n):
    addr = syntax.parse_int (ss[n])
    bound = ss[n + 1]
    if bound == 'None':
      bound = None
      return (n + 3, (addr, None))
    else:
      bound = syntax.parse_int (bound)
      kind = ss[n + 2]
      return (n + 3, (addr, (bound, kind)))

def parse_ctxt_id (bits, n):
    return (n + 1, syntax.parse_int (bits[n]))

def parse_ctxt (bits, n):
    return syntax.parse_list (parse_ctxt_id, bits, n)

def load_bounds ():
    try:
      f = open ('%s/LoopBounds.txt' % target_objects.target_dir)
      ls = list (f)
      f.close ()
    except IOError, e:
      ls = []
    from syntax import parse_int, parse_list
    for l in ls:
      bits = l.split ()
      if bits[:1] not in [['LoopBound'], ['GlobalLoopBound']]:
        continue
      (n, (addr, bound)) = parse_bound (bits, 1)
      (n, ctxt) = parse_ctxt (bits, n)
      prob_hash = parse_int (bits[n])
      n += 1
      if bits[0] == 'LoopBound':
        (n, prev_bounds) = parse_list (parse_bound, bits, n)
        assert n == len (bits), bits
        known = known_bounds.setdefault (addr, [])
        known.append ((ctxt, prob_hash, prev_bounds, bound))
      else:
        assert n == len (bits), bits
        known = known_bounds.setdefault ((addr, 'Global'), [])
        known.append ((ctxt, prob_hash, bound))
    known_bounds['Loaded'] = True

def get_bound_ctxt (split, call_ctxt):
    trace ('Getting bound for 0x%x in context %s.' % (split, call_ctxt))
    (p, hyps, addr_map) = get_call_ctxt_problem (split, call_ctxt)

    orig_split = split
    split = p.loop_id (addr_map[split])
    assert split, (orig_split, call_ctxt)
    split_bin_addr = min ([addr for addr in addr_map
        if p.loop_id (addr_map[addr]) == split])

    prior = get_prior_loop_heads (p, split)
    restrs = ()
    prev_bounds = []
    for split2 in prior:
      # recursion!
      split2 = p.loop_id (split2)
      assert split2
      addr = min ([addr for addr in addr_map
        if p.loop_id (addr_map[addr]) == split2])
      bound = get_bound_ctxt (addr, call_ctxt)
      prev_bounds.append ((addr, bound))
      k = (p.name, split2, bound, restrs, tuple (hyps))
      if k in known_bound_restr_hyps:
        (restrs, hyps) = known_bound_restr_hyps[k]
      else:
        (restrs, hyps) = add_loop_bound_restrs_hyps (p, restrs, hyps,
          split2, bound, call_ctxt + [orig_split])
        known_bound_restr_hyps[k] = (restrs, hyps)

    # start timing now. we miss some setup time, but it avoids double counting
    # the recursive searches.
    start = time.time ()

    p_h = problem_hash (p)
    prev_bounds = sorted (prev_bounds)
    if not known_bounds:
      load_bounds ()
    known = known_bounds.get (split_bin_addr, [])
    for (call_ctxt2, h, prev_bounds2, bound) in known:
      match = (not call_ctxt2 or call_ctxt[- len (call_ctxt2):] == call_ctxt2)
      if match and h == p_h and prev_bounds2 == prev_bounds:
        return bound
    bound = search_bin_bound (p, restrs, hyps, split)
    known = known_bounds.setdefault (split_bin_addr, [])
    known.append ((call_ctxt, p_h, prev_bounds, bound))
    end = time.time ()
    save_bound (False, split_bin_addr, call_ctxt, p_h, prev_bounds, bound,
        time = end - start)
    return bound

def problem_hash (p):
    return syntax.hash_tuplify ([p.name, p.entries,
      sorted (p.outputs.iteritems ()), sorted (p.nodes.iteritems ())])

def search_bin_bound (p, restrs, hyps, split):
    trace ('Searching for bound for 0x%x in %s.', (split, p.name))
    bound = search_bound (p, restrs, hyps, split)
    if bound:
      return bound

    # try to use a bound inferred from C
    if avoid_C_information[0]:
      # OK told not to
      return None
    if get_prior_loop_heads (p, split):
      # too difficult for now
      return None
    asm_tag = p.node_tags[split][0]
    (_, fname, _) = p.get_entry_details (asm_tag)
    funs = [f for pair in target_objects.pairings[fname]
      for f in pair.funs.values ()]
    c_tags = [tag for tag in p.tags ()
        if p.get_entry_details (tag)[1] in funs and tag != asm_tag]
    if len (c_tags) != 1:
      print 'Surprised to see multiple matching tags %s' % c_tags
      return None

    [c_tag] = c_tags

    return getBinaryBoundFromC (p, c_tag, split, restrs, hyps)

def rab_test ():
    [split_bin_addr] = get_loop_heads (functions['resolveAddressBits'])
    (p, hyps, addr_map) = get_call_ctxt_problem (split_bin_addr, [])
    split = p.loop_id (addr_map[split_bin_addr])
    [c_tag] = [tag for tag in p.tags () if tag != p.node_tags[split][0]]
    return getBinaryBoundFromC (p, c_tag, split, (), hyps)

last_search_bound = [0]

def search_bound (p, restrs, hyps, split):
    last_search_bound[0] = (p, restrs, hyps, split)

    # try a naive bin search first
    # limit this to a small bound for time purposes
    #   - for larger bounds the less naive approach can be faster
    bound = findLoopBoundBS(split, p, restrs=restrs, hyps=hyps,
      try_seq = [0, 1, 6])
    if bound != None:
      return (bound, 'NaiveBinSearch')

    l_hyps = get_linear_series_hyps (p, split, restrs, hyps)

    rep = rep_graph.mk_graph_slice (p, fast = True)

    def test (n):
        assert n > 10
        hyp = get_induct_eq_hyp (p, split, restrs, n - 2)
        visit = ((split, vc_offs (2)), ) + restrs
        continue_to_split_guess = rep.get_pc ((split, visit))
        return rep.test_hyp_whyps (syntax.mk_not (continue_to_split_guess),
          [hyp] + l_hyps + hyps)

    # findLoopBoundBS always checks to at least 16
    min_bound = 16
    max_bound = max_acceptable_bound[0]
    bound = upDownBinSearch (min_bound, max_bound, test)
    if bound != None and test (bound):
      return (bound, 'InductiveBinSearch')

    # let the naive bin search go a bit further
    bound = findLoopBoundBS(split, p, restrs=restrs, hyps=hyps)
    if bound != None:
      return (bound, 'NaiveBinSearch')

    return None

def getBinaryBoundFromC (p, c_tag, asm_split, restrs, hyps):
    c_heads = [h for h in search.init_loops_to_split (p, restrs)
      if p.node_tags[h][0] == c_tag]
    c_bounds = [(p.loop_id (split), search_bound (p, (), hyps, split))
      for split in c_heads]
    if not [b for (n, b) in c_bounds if b]:
      trace ('no C bounds found (%s).' % c_bounds)
      return None

    asm_tag = p.node_tags[asm_split][0]

    rep = rep_graph.mk_graph_slice (p)
    i_seq_opts = [(0, 1), (1, 1), (2, 1)]
    j_seq_opts = [(0, 1), (0, 2), (1, 1)]
    tags = [p.node_tags[asm_split][0], c_tag]
    try:
      split = search.find_split (rep, asm_split, restrs, hyps, i_seq_opts,
        j_seq_opts, 5, tags = [asm_tag, c_tag])
    except solver.SolverFailure, e:
      return None
    if not split or split[0] != 'Split':
      trace ('no split found (%s).' % repr (split))
      return None
    (_, split) = split
    rep = rep_graph.mk_graph_slice (p)
    checks = check.split_checks (p, (), hyps, split, tags = [asm_tag, c_tag])
    groups = check.proof_check_groups (checks)
    try:
      for group in groups:
        (res, el) = check.test_hyp_group (rep, group)
        if not res:
          trace ('split check failed!')
          trace ('failed at %s' % el)
          return None
    except solver.SolverFailure, e:
      return None
    (as_details, c_details, _, n, _) = split
    (c_split, (seq_start, step), _) = c_details
    c_bound = dict (c_bounds).get (p.loop_id (c_split))
    if not c_bound:
      trace ('key split was not bounded (%r, %r).' % (c_split, c_bounds))
      return None
    (c_bound, _) = c_bound
    max_it = (c_bound - seq_start) / step
    assert max_it > n, (max_it, n)
    (_, (seq_start, step), _) = as_details
    as_bound = seq_start + (max_it * step)
    # increment by 1 as this may be a bound for a different splitting point
    # which occurs later in the loop
    as_bound += 1
    return (as_bound, 'FromC')

def get_prior_loop_heads (p, split, use_rep = None):
    if use_rep:
      rep = use_rep
    else:
      rep = rep_graph.mk_graph_slice (p)
    prior = []
    split = p.loop_id (split)
    for h in p.loop_heads ():
      s = set (prior)
      if h not in s and rep.get_reachable (h, split) and h != split:
        # need to recurse to ensure prior are in order
        prior2 = get_prior_loop_heads (p, h, use_rep = rep)
        prior.extend ([h2 for h2 in prior2 if h2 not in s])
        prior.append (h)
    return prior

def add_loop_bound_restrs_hyps (p, restrs, hyps, split, bound, ctxt):
    # time this for diagnostic reasons
    start = time.time ()

    #vc_options([concrete numbers], [offsets])
    hyps = hyps + get_linear_series_hyps (p, split, restrs, hyps)
    hyps = list (set (hyps))
    if bound == None or bound >= 10:
        restrs = restrs + ((split, rep_graph.vc_options([0],[1])),)
    else:
        restrs = restrs + ((split, rep_graph.vc_upto (bound+1)),)

    end = time.time ()
    save_extra_timing ('LoopBoundRestrHyps', ctxt, end - start)

    return (restrs, hyps)

max_acceptable_bound = [1000000]

functions_hash = [None]

def get_functions_hash ():
    if functions_hash[0] != None:
      return functions_hash[0]
    h = hash (tuple (sorted ([(f, hash (functions[f])) for f in functions])))
    functions_hash[0] = h
    return h

addr_to_loop_id_cache = {}
complex_loop_id_cache = {}

def addr_to_loop_id (split):
    if split not in addr_to_loop_id_cache:
      add_fun_to_loop_data_cache (trace_refute.get_body_addrs_fun (split))
    return addr_to_loop_id_cache[split]

def is_complex_loop (split):
    split = addr_to_loop_id (split)
    if split not in complex_loop_id_cache:
      add_fun_to_loop_data_cache (trace_refute.get_body_addrs_fun (split))
    return complex_loop_id_cache[split]

def get_loop_addrs (split):
    split = addr_to_loop_id (split)
    f = functions[trace_refute.get_body_addrs_fun (split)]
    return [addr for addr in f.nodes if trace_refute.is_addr (addr)
        if addr_to_loop_id_cache.get (addr) == split]

def add_fun_to_loop_data_cache (fname):
    p = functions[fname].as_problem (problem.Problem)
    p.do_loop_analysis ()
    for h in p.loop_heads ():
      addrs = [n for n in p.loop_body (h)
        if trace_refute.is_addr (n)]
      min_addr = min (addrs)
      for addr in addrs:
        addr_to_loop_id_cache[addr] = min_addr
      complex_loop_id_cache[min_addr] = problem.has_inner_loop (p, h)
    return min_addr

def get_bound_super_ctxt (split, call_ctxt, no_splitting=False,
        known_bound_only=False):
    if not known_bounds:
      load_bounds ()
    for (ctxt2, fn_hash, bound) in known_bounds.get ((split, 'Global'), []):
      if ctxt2 == call_ctxt and fn_hash == get_functions_hash ():
        return bound
    min_loop_addr = addr_to_loop_id (split)
    if min_loop_addr != split:
      return get_bound_super_ctxt (min_loop_addr, call_ctxt,
            no_splitting = no_splitting, known_bound_only = known_bound_only)

    if known_bound_only:
        return None
    no_splitting_abort = [False]
    try:
      bound = get_bound_super_ctxt_inner (split, call_ctxt,
        no_splitting = (no_splitting, no_splitting_abort))
    except problem.Abort, e:
      bound = None
    if no_splitting_abort[0]:
      # don't record this bound, since it might change if splitting was allowed
      return bound
    known = known_bounds.setdefault ((split, 'Global'), [])
    known.append ((call_ctxt, get_functions_hash (), bound))
    save_bound (True, split, call_ctxt, get_functions_hash (), None, bound)
    return bound

from trace_refute import (function_limit, ctxt_within_function_limits)

def call_ctxt_computable (split, call_ctxt):
    fs = [trace_refute.identify_function ([], [call_site])
      for call_site in call_ctxt]
    return not ([f for f in fs if trace_refute.has_complex_loop (f)])

def get_bound_super_ctxt_inner (split, call_ctxt,
      no_splitting = (False, None)):
    first_f = trace_refute.identify_function ([], (call_ctxt + [split])[:1])
    call_sites = all_call_sites (first_f)

    if function_limit (first_f) == 0:
      return (0, 'FunctionLimit')
    safe_call_sites = [cs for cs in call_sites
      if ctxt_within_function_limits ([cs] + call_ctxt)]
    if call_sites and not safe_call_sites:
      return (0, 'FunctionLimit')

    if len (call_ctxt) < 3 and len (safe_call_sites) == 1:
      call_ctxt2 = list (safe_call_sites) + call_ctxt
      if call_ctxt_computable (split, call_ctxt2):
        return get_bound_super_ctxt (split, call_ctxt2)

    fname = trace_refute.identify_function (call_ctxt, [split])
    bound = function_limit_bound (fname, split)
    if bound:
      return bound

    bound = get_bound_ctxt (split, call_ctxt)
    if bound:
      return bound

    if no_splitting[0]:
      assert no_splitting[1], no_splitting
      no_splitting[1][0] = True
      return None

    # try to split over potential call sites
    if len (call_ctxt) >= 3:
      return None

    if len (call_sites) == 0:
      # either entry point or nonsense
      return None

    if [call_site for call_site in safe_call_sites
        if not call_ctxt_computable (split, [call_site] + call_ctxt)]:
      return None

    anc_bounds = [get_bound_super_ctxt (split, [call_site] + call_ctxt,
        no_splitting = True)
      for call_site in safe_call_sites]
    if None in anc_bounds:
      return None
    (bound, kind) = max (anc_bounds)
    return (bound, 'MergedBound')

def function_limit_bound (fname, split):
    p = functions[fname].as_problem (problem.Problem)
    p.do_analysis ()
    cuts = [n for n in p.loop_body (split)
        if p.nodes[n].kind == 'Call'
        if function_limit (p.nodes[n].fname) != None]
    if not cuts:
      return None
    graph = p.mk_node_graph (p.loop_body (split))
    # it is not possible to iterate the loop without visiting a bounded
    # function. naively, this sets the limit to the sum of all the possible
    # bounds, plus one because we can enter the loop a final time without
    # visiting any function call site yet.
    if logic.divides_loop (graph, set (cuts)):
      fnames = set ([p.nodes[n].fname for n in cuts])
      return (sum ([function_limit (f) for f in fnames]) + 1, 'FunctionLimit')

def loop_bound_difficulty_estimates (split, ctxt):
    # various guesses at how hard the loop bounding problem is.
    (p, hyps, addr_map) = get_call_ctxt_problem (split, ctxt, timing = False)

    loop_id = p.loop_id (addr_map[split])
    assert loop_id

    # number of instructions in the loop
    inst_node_ids = set (addr_map.itervalues ())
    l_insts = [n for n in p.loop_body (loop_id) if n in inst_node_ids]

    # number of instructions in the function
    tag = p.node_tags[loop_id][0]
    f_insts = [n for n in inst_node_ids if p.node_tags[n][0] == tag]

    # number of instructions in the whole calling context
    ctxt_insts = len (inst_node_ids)

    # well, what else?
    return (len (l_insts), len (f_insts), ctxt_insts)

def load_timing ():
    f = open ('%s/LoopBounds.txt' % target_objects.target_dir)
    timing = {}
    loop_time = 0.0
    ext_time = 0.0
    for line in f:
      bits = line.split ()
      if not (bits and 'Timing' in bits[0]):
        continue
      if bits[0] == 'LoopBoundTiming':
        (n, ext_ctxt) = parse_ctxt (bits, 1)
        assert n == len (bits) - 1
        time = float (bits[n])
        ctxt = ext_ctxt[:-1]
        split = ext_ctxt[-1]
        timing[(split, tuple(ctxt))] = time
        loop_time += time
      elif bits[0] == 'ExtraTiming':
        time = float (bits[-1])
        ext_time += time
    f.close ()
    f = open ('%s/time' % target_objects.target_dir)
    [l] = [l for l in f if '(wall clock)' in l]
    f.close ()
    tot_time_str = l.split ()[-1]
    tot_time = sum ([float(s) * (60 ** i)
      for (i, s) in enumerate (reversed (tot_time_str.split(':')))])

    return (loop_time, ext_time, tot_time, timing)

def mk_timing_metrics ():
    if not known_bounds:
      load_bounds ()
    probs = [(split_bin_addr, tuple (call_ctxt), bound)
      for (split_bin_addr, known) in known_bounds.iteritems ()
      if type (split_bin_addr) == int
      for (call_ctxt, h, prev_bounds, bound) in known]
    probs = set (probs)
    data = [(split, ctxt, bound,
        loop_bound_difficulty_estimates (split, list (ctxt)))
      for (split, ctxt, bound) in probs]
    return data

# sigh, this is so much work.
bound_kind_nums = {
  'FunctionLimit': 2,
  'NaiveBinSearch': 3,
  'InductiveBinSearch': 4,
  'FromC': 5,
  'MergedBound': 6,
}

gnuplot_colours = [
  "dark-red", "dark-blue", "dark-green", "dark-grey",
  "dark-orange", "dark-magenta", "dark-cyan"]

def save_timing_metrics (num):
    (loop_time, ext_time, tot_time, timing) = load_timing ()

    col = gnuplot_colours[num]
    from target import short_name

    time_ests = mk_timing_metrics ()
    import os
    f = open ('%s/LoopTimingMetrics.txt' % target_objects.target_dir, 'w')
    f.write ('"%s"\n' % short_name)

    for (split, ctxt, bound, ests) in time_ests:
      time = timing[(split, tuple (ctxt))]
      if bound == None:
        bdata = "1000000 7"
      else:
        bdata = '%d %d' % (bound[0], bound_kind_nums[bound[1]])
      (l_i, f_i, ct_i) = ests
      f.write ('%s %s %s %s %s %r %s\n' % (short_name, l_i, f_i, ct_i,
        bdata, col, time))
    f.close ()

def get_loop_heads (fun):
    if not fun.entry:
      return []
    p = fun.as_problem (problem.Problem)
    p.do_loop_analysis ()
    loops = set ()
    for h in p.loop_heads ():
      # any address in the loop will do. pick the smallest one
      addr = min ([n for n in p.loop_body (h) if trace_refute.is_addr (n)])
      loops.add ((addr, fun.name, problem.has_inner_loop (p, h)))
    return list (loops)

def get_all_loop_heads ():
    loops = set ()
    abort_funs = set ()
    for f in all_asm_functions ():
      try:
        loops.update (get_loop_heads (functions[f]))
      except problem.Abort, e:
        abort_funs.add (f)
    if abort_funs:
      trace ('Cannot analyse loops in: %s' % ', '.join (abort_funs))
    return loops

def get_complex_loops ():
    return [(loop, name) for (loop, name, compl) in get_all_loop_heads ()
        if compl]

def search_all_loops ():
    all_loops = get_all_loop_heads ()
    for (loop, _, _) in all_loops:
      get_bound_super_ctxt (loop, [])

main = search_all_loops

if __name__ == '__main__':
    import sys
    args = target_objects.load_target_args ()
    if args == ['search']:
      search_all_loops ()
    elif args[:1] == ['metrics']:
      num = args[1:].index (str (target_objects.target_dir))
      save_timing_metrics (num)


