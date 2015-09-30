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

#tryFun must take exactly 1 argument
def downBinSearch(minimum, maximum, tryFun):
    upperBound = maximum 
    lowerBound = minimum
    print 'searching between %d to %d' % (lowerBound,upperBound)
    ret = None
    while upperBound > lowerBound:
      cur = (lowerBound + upperBound) / 2
      if True:
        print 'trying %d' % cur
      if tryFun(cur):
          upperBound = cur
      else:
          lowerBound = cur + 1
    assert upperBound == lowerBound
    ret = lowerBound
    return ret

def addr_of_node (preds, n):
  while not trace_refute.is_addr (n):
    [n] = preds[n]
  return n

def all_asm_functions ():
    asm_fs = set ([pair.funs['ASM'] for f in target_objects.pairings
      for pair in target_objects.pairings[f]])
    for f in list (asm_fs):
      asm_fs.update (functions[f].function_calls ())
    return asm_fs

call_site_set = {}

def build_call_site_set ():
    for f in all_asm_functions ():
      preds = logic.compute_preds (functions[f].nodes)
      for (n, node) in functions[f].nodes.iteritems ():
        if node.kind == 'Call':
          s = call_site_set.setdefault (node.fname, set ())
          s.add (addr_of_node (preds, n))
    call_site_set[('IsLoaded', 'just in case')] = True

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
          bound_try_seq = [0,1,20,64]
        else:
          bound_try_seq = [0,1,20,64,130]
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

def linear_eq_induct_step_checks (p, restrs, hyps, tag, split, eqs):
    details = (split, (0, 1), eqs)
    cont = split_visit_one_visit (tag, details, restrs, vc_offs (1))
    # the 'trivial' hyp here ensures the representation includes a loop
    # of the rhs when proving const equations on the lhs
    hyps = ([pc_true_hyp (cont)] + hyps
            + [h for (h, _) in linear_eq_hyps_at_visit (tag, split,
            eqs, restrs, vc_offs (0))])

    return [(hyps, hyp, 'Induct check (%s) at inductive step for %d'
            % (desc, split))
        for (hyp, desc) in linear_eq_hyps_at_visit (tag, split, eqs,
            restrs, vc_offs (1))]

def get_linear_series_hyps (p, split,restrs,hyps):

    k = ('linear_series_hyps', split, restrs, tuple (hyps))
    if k in p.cached_analysis:
        return p.cached_analysis[k]

    cands = search.mk_seq_eqs (p, split, 1, with_rodata = False)
    cands += candidate_additional_eqs (p, split)
    (tag, _) = p.node_tags[split]

    rep = rep_graph.mk_graph_slice (p, fast = True)

    def do_checks (eqs):
        checks = (linear_eq_induct_step_checks (p, restrs, hyps, tag, split, eqs)
            + linear_eq_induct_base_checks (p, restrs, hyps, tag, split, eqs))

        groups = check.proof_check_groups (checks)
        for group in groups:
            if not check.test_hyp_group (rep, group):
                return False
        return True

    eqs = []
    failed = []
    while cands:
        cand = cands.pop ()
        if do_checks (eqs + [cand]):
            eqs.append (cand)
            cands = failed + cands
            failed = []
        else:
            failed.append (cand)

    hyps = [h for (h, _) in linear_eq_hyps_at_visit (tag, split, eqs,
             restrs, vc_offs (0))]
    p.cached_analysis[k] = hyps
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

def get_call_ctxt_problem (split, call_ctxt):
  from trace_refute import identify_function, build_compound_problem_with_links
  f = identify_function (call_ctxt, [split])
  for (ctxt2, p, hyps, addr_map) in call_ctxt_problems:
    if ctxt2 == (call_ctxt, f):
      return (p, hyps, addr_map)

  (p, hyps, addr_map) = build_compound_problem_with_links (call_ctxt, f)
  call_ctxt_problems.append(((call_ctxt, f), p, hyps, addr_map))
  del call_ctxt_problems[: -20]
  return (p, hyps, addr_map)

known_bound_restr_hyps = {}

known_bounds = {}

def serialise_bound (addr, (bound, kind)):
    assert bound == None or logic.is_int (bound)
    assert str (kind) == kind
    return [hex (addr), str (bound), kind]

def save_bound (split_bin_addr, call_ctxt, prob_hash, prev_bounds, bound):
    ss = ['LoopBound'] + serialise_bound (split_bin_addr, bound)
    ss += [str (len (call_ctxt))] + map (hex, call_ctxt)
    ss += [str (prob_hash), str (len (prev_bounds))]
    for (split, bound) in prev_bounds:
      ss += serialise_bound (split, bound)
    s = ' '.join (ss)
    f = open ('%s/LoopBounds.txt' % target_objects.target_dir, 'a')
    f.write (s + '\n')
    f.close ()
    trace ('Found bound %s for 0x%x in context %s.\n' % (bound, split_bin_addr, 
      call_ctxt))

def parse_bound (ss, n):
    addr = syntax.parse_int (ss[n])
    bound = ss[n + 1]
    if bound == 'None':
      bound = None
    else:
      bound = syntax.parse_int (bound)
    kind = ss[n + 2]
    return (n + 3, (addr, (bound, kind)))

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
      if bits[:1] != ['LoopBound']:
        continue
      (n, (addr, bound)) = parse_bound (bits, 1)
      def parse_ctxt_id (bits, n):
        return (n + 1, syntax.parse_int (bits[n]))
      (n, ctxt) = parse_list (parse_ctxt_id, bits, n)
      prob_hash = parse_int (bits[n])
      (n, prev_bounds) = parse_list (parse_bound, bits, n + 1)
      assert n == len (bits), bits
      known = known_bounds.setdefault (addr, [])
      known.append ((ctxt, prob_hash, prev_bounds, bound))
    known_bounds['Loaded'] = True

def get_bound_ctxt (split, call_ctxt):
    trace ('Getting bound for 0x%x in context %s.' % (split, call_ctxt))
    (p, hyps, addr_map) = get_call_ctxt_problem (split, call_ctxt)

    split_bin_addr = split

    split = p.loop_id (addr_map[split_bin_addr])
    assert split, (split_bin_addr, call_ctxt)
    prior = get_prior_loop_heads (p, split)
    assert split_bin_addr == min ([addr for addr in addr_map
        if p.loop_id (addr_map[addr]) == split])

    restrs = ()
    hyps = []
    prev_bounds = []
    for split2 in prior:
      # recursion!
      split2 = p.loop_id (split2)
      assert split2
      addr = min ([addr for addr in addr_map
        if p.loop_id (addr_map[addr]) == split2])
      bound = get_bound_ctxt (addr, call_ctxt)
      prev_bounds.append ((addr, bound))
      k = (p.name, split2, bound, restrs, hyps)
      if k in known_bound_restr_hyps:
        (restrs, hyps) = known_bound_restr_hyps[k]
      else:
        (restrs, hyps) = add_loop_bound_restrs_hyps (p, restrs, hyps,
          split2, bound)
        known_bound_restr_hyps[k] = (restrs, hyps)

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
    save_bound (split_bin_addr, call_ctxt, p_h, prev_bounds, bound)
    return bound

def problem_hash (p):
    return syntax.hash_tuplify ([p.name, p.entries,
      sorted (p.outputs.iteritems ()), sorted (p.nodes.iteritems ())])

def search_bin_bound (p, restrs, hyps, split):
    trace ('Searching for bound for 0x%x in %s.', (split, p.name))
    bound = search_bound (p, restrs, hyps, split)
    if bound:
      return bound

    # try using a bound inferred from C
    if len (p.entries) == 2 and len (p.loop_heads ()) == 2:
      if len (set ([p.node_tags[n][0] for n in p.loop_heads ()])) == 2:
        [asm_split] = [h for h in p.loop_heads() if is_asm_node (p, h)]
        [c_split] = [sp for sp in p.loop_heads () if not is_asm_node (p, sp)]
        return getBinaryBoundFromC (p, c_split, asm_split, hyps)

    return None

def search_bound (p, restrs, hyps, split):
    #try a naive bin search first
    bound = findLoopBoundBS(split, p, restrs=restrs, hyps=hyps)

    if bound != None:
      return (bound, 'BinSearch')

    print '     naive b search failed, trying induction, split:%d' % split
    b_searchable = False
    ret = getOffset(split,p)
    if ret:
        results = []
        moving_regs, offset = ret
        print '         moving_regs are %s, offset: %d' % (moving_regs,offset)
        exit_conds = getExitCond(split,p)
        b_searchable = exit_conds != None and True in [canBSearch(ec,p)
            for ec in exit_conds]
        #if at least one of the exit conds is a less/larger than test, we can b search this
        ret = guessBound(split,p, restrs)
        if ret:
            vals = ret
            print '         vals= %s' % str(vals)
            guesses = vals 
            print '         guesses are %s' % str(guesses)

            ret = tryGuessesInduct(guesses, split,p,offset,restrs,hyps)
            if not ret:
              print 'Oops !'
            else:
              print 'found bound: %d / 0x%x' % (ret,ret)
              results.append((ret, 'InductGuess'))
            print 'blindly guessing constants'
            consts = allConstants(split,p)
            consts += extra_loop_consts
            const_guesses = [x/offset for x in consts]
            const_guesses = [x for x in const_guesses if x > 30 and x < 0xf0000000]
            print 'guesses are : %s' % str(const_guesses)
            ret = tryGuessesInduct(consts, split,p,offset,restrs,hyps)
            if not ret == None:
               print 'blind constant guess worked : %d/%x' % (ret,ret)
               results.append((ret, 'InductConstGuess'))
            else:
               print 'blind guesses failed'

    maxi = None
    if results:
      # the state might not look binary-searchable, but if we
      # find a result by decrementing our current guess, we should
      # search lower anyway
      if findLoopBoundInduct(split, p, min (results) - 1, offset, restrs, hyps):
        maxi = min (results) - 1
    if results and maxi == None:
      maxi = min (results)
    if maxi == None:
      print 'getting max bound for b search'
      #firstly get a max bound
      bound_try_seq = [0x1000,0x2000000]
      for (i,guess) in enumerate(bound_try_seq):
        print 'trying %x' % guess
        valid = findLoopBoundInduct(split, p, guess, offset, restrs, hyps)
        print 'valid: %s' % valid
        if valid:
          print 'Got maximum bound ! %d' % guess
          maxi = guess
          break

    if not maxi == None:
      print 'b searching with induction !'
      tryFun = lambda x: findLoopBoundInduct(split, p, x, offset, restrs, hyps)
      results.append( (downBinSearch(1, maxi, tryFun), 'DownwardInduct') )

    if results:
      return min(results)
    return None

def getBinaryBoundFromC (p, c_split, asm_split, hyps):
    c_bound = search_bound (p, (), hyps, c_split)
    if c_bound == None:
      return None

    rep = rep_graph.mk_graph_slice (p)
    i_seq_opts = [(0, 1), (1, 1), (2, 1)]
    j_seq_opts = [(0, 1), (0, 2), (1, 1)]
    tags = [p.node_tags[asm_split][0], p.node_tags[c_split][0]]
    split = search.find_split (rep, asm_split, (), hyps, i_seq_opts,
        j_seq_opts, 5, tags = tags)
    if not split or split[0] != 'Split':
        return None
    (_, split) = split
    rep = rep_graph.mk_graph_slice (p)
    checks = check.split_checks (p, (), hyps, split)
    groups = check.proof_check_groups (checks)
    for group in groups:
        if not check.test_hyp_group (rep, group):
            return None
    (as_details, c_details, _, n, _) = split
    (_, (seq_start, step), _) = c_details
    max_it = (c_bound - seq_start) / step
    assert max_it > n, (max_it, n)
    (_, (seq_start, step), _) = as_details
    as_bound = seq_start + (max_it * step)
    # increment by 1 as this may be a bound for a different splitting point
    # which occurs later in the loop
    as_bound += 1
    return (as_bound, 'FromC')

def get_prior_loop_heads (p, split):
    rep = rep_graph.mk_graph_slice (p)
    return [h for h in p.loop_heads ()
      if rep.get_reachable (h, split)
      if p.loop_id (h) != p.loop_id (split)]

#given a bunch of guesses at the bound, try all of them with findLoopBoundInductWindow
def tryGuessesInduct(guesses, split, p, offset, restrs,hyps,adjust_two_comp=True):
    if adjust_two_comp:
        guesses = adjustTwoComps(guesses)
    guesses = [x for x in guesses if x > 30 and x < 0x4000001]
    guesses = sorted(list(set(guesses)))
    print 'Trying guesses: %s' % str ( [hex(x) for x in guesses] )
    for guess in guesses:
        valid = findLoopBoundInductWindow(split, p, guess, offset, restrs, hyps)
        print 'guess %d / 0x%x: valid %s' %(guess,guess,str(valid))
        if valid:
          return guess
    return None


def findLoopBoundInductWindow(split, p, split_guess, step_guess, restrs, hyps):
    WINDOW = 10
    #assume we can visit base - WINDOW, can we get to top_guessed + window ?
    r = tryLoopBoundInduct(split, p, split_guess - step_guess - WINDOW, 2*WINDOW , restrs, hyps)
    if not r:
      return False
    #ok find the actual bound with a linear search
    for i in range(split_guess - WINDOW, split_guess + WINDOW +1):
        r = findLoopBoundInduct(split, p, i, step_guess, restrs, hyps)
        if r:
          return i
    assert False, 'Dafaq ??'
      

def findLoopBoundInduct(split, p, split_guess, step_guess, restrs, hyps):
    return tryLoopBoundInduct(split,p, split_guess - step_guess, step_guess, restrs,hyps)

def tryLoopBoundInduct(split, p, base, window, restrs, hyps):
    if base + window > 0xf0000000:
      print 'split_guess too large to be true'
      return False
    #p.do_analysis ()
    #split = 4026613876
    # prove linear series (r3 ~= i * 8) and get hyps
    # this is a series of visits to 'split' numbered by i
    l_hyps = get_linear_series_hyps (p, split,restrs,hyps)
    if l_hyps == False:
      print '!! linear_series_hyps: False'
      return False
    #print 'linear_series_hyps: True'
    
    l_hyps = l_hyps + hyps
    # assume i = split_guess - step_guess
    hyp = get_induct_eq_hyp (p, split, restrs, base)
    rep = rep_graph.mk_graph_slice (p)
    # consider pc of visit i + 2 (i.e. 512)
    try:
        continue_to_split_guess = rep.get_pc ((split, ((split, vc_offs (window)),) + restrs))
    except:
        print 'continue_to_split_guess threw an exception'
        return False
    # test whether this is impossible
    try:
        ret = rep.test_hyp_whyps (syntax.mk_not (continue_to_split_guess), [hyp] + l_hyps)
    except:
        print 'hyp test failed'
        return False
    return ret 

def add_loop_bound_restrs_hyps (p, restrs, hyps, split, bound):
    #vc_options([concrete numbers], [offsets])
    hyps = hyps + get_linear_series_hyps (p, split, restrs, hyps)
    hyps = list (set (hyps))
    if bound == None or bound >= 10:
        restrs = restrs + ((split, rep_graph.vc_options([0],[1])),)
    else:
        restrs = restrs + ((split, rep_graph.vc_upto (bound+1)),)
    return (restrs, hyps)

max_acceptable_bound = [1000000]

def phyBounds(p_bounds, heads, phy_already=False, p = None):
    if not phy_already:
        phyAddr = lambda x: phyAddrP(x,p)
    else:
        phyAddr = lambda x: x
    ret = {}
    phy_ns = set([ phyAddr(x) for x in p_bounds ])
    for n in phy_ns:
      all_p_heads = [x for x in heads if phyAddr(x) == n]
      if [x for x in all_p_heads if x not in p_bounds]:
        #the physical loop can't be bounded !
        print 'failing to bound phy %x' % n
        continue
      #print 'all_p_heads: %s' % all_p_heads
      #print 'p_bounds:%s' % p_bounds
      ret[n] = max ([p_bounds[x] for x in p_bounds if phyAddr(x) == n ])
    return ret

def get_bound_super_ctxt (split, call_ctxt):
    first_f = trace_refute.identify_function ([], (call_ctxt + [split])[:1])
    call_sites = all_call_sites (first_f)
    if len (call_sites) == 0:
      return (0, 'NotCallable')
    if len (call_ctxt) < 3 and len (call_sites) == 1:
      return get_bound_super_ctxt (split, list (call_sites) + call_ctxt)

    bound = get_bound_ctxt (split, call_ctxt)
    if bound:
      return bound

    if len (call_ctxt) >= 3:
      return None

    anc_bounds = [get_bound_ctxt (split, [call_site] + call_ctxt)
      for call_site in call_sites]
    if None in anc_bounds:
      return None
    (bound, kind) = max (anc_bounds)
    return (bound, 'MergedBound')

def isRegName(s):
    if s in ['r0','r1','r3','r4','r5','r6','r7','r8','r9','r10','r11','r12','r13','ip']:
      return True
    if re.search(r'^r[0-9][0-9]?',s):
      return True
    if re.search(r'^ip',s):
      return True
    return False

def guess(eqs):
    xs = [x for x in eqs if not isRegName(x.name)]
    #print '%d Guesses are : ' % len(xs)
    #for x in xs:
    #  print x
    xs2 = [x for x in xs if 'vals' in vars(x)]
    xs3 = [x for x in xs2 if not x.name =='ROData' ]
    print '%d Guesses are : ' % len(xs3)
    for x in xs3:
      print x
    
    if len(xs3) == 1:
      ret = xs3[0]
      print 'unique guess:'
      print ret
      return ret
    return None


def parseOffset(expr):
    if expr.kind == 'Num':
        return expr.val
    expr2 = search.eval_model_expr ({}, None, expr)
    if expr2.kind == 'Num':
        return expr2.val
    assert not 'parseOffset: constant expr', (expr, expr2)

nzcv_regex = r'(?P<r>^[nzcv]\.?[0-9]*)'

def registersContained(p_n, p, args=None):
    ret = []
    if not args:
        node = p.nodes[p_n]
        args = node.get_args()

    if not isinstance(args,syntax.Expr):
      assert not isinstance(args,tuple)
      node = p.nodes[p_n]
      l = node.get_args()
     # print 'l: %s' % str(l)
      # supposedly this is assigning to the 4 flags, just pick one
      if l == []:
        return []
      #tup = l[0]
      tups = [t for t in l if re.search(nzcv_regex, t[0][0])]
      if not tups:
        return []
      tup = tups[0]
      assert isinstance(tup,tuple)
      if not re.search(nzcv_regex, tup[0][0]):
        return []
      expr = tup[1]
    else:
      expr = args
    if expr.kind == 'Num':
      return [] 
    if isRegName(expr.name):
      return [expr.name]
    elif 'vals' not in vars(expr):
      return []
    vals = expr.vals
    for x in vals:
      ret += registersContained(None,p,args=x)
    return list(set(ret))
  
#is pn a node that assigns to oen of the specifc registers listed in ns ? 
def isNZCVAssignSpec(pn,p,ns=None):
    for x in ns:
      if not isNZCVAssign(pn,p,specific=x):
        return False
    return True

def isNZCVAssign(pn,p,specific=None):
    if 'upds' not in vars(p.nodes[pn]):
      return []
    upds = p.nodes[pn].upds
    if specific:
      regex = r'(?P<r>^'+specific+r')'
    else:
      regex = nzcv_regex
    ret = []
    for x in upds:
      r = re.search(regex,x[0][0])
      if r:
        ret.append(r.group('r'))
    return ret

def getNZCVAssignNodes(pn,p,specifics,visited=None):
    if visited ==None:
      visited = []
    node = p.nodes[pn]
    if isNZCVAssignSpec(pn,p,specifics):
      return [pn]
    preds = [x for x in p.preds[pn] if x not in visited]
    ret = []
    for x in preds:
        ret += getNZCVAssignNodes(x,p,specifics,visited=visited)
    return ret


def isNZCVCheck(expr):
    op = expr.name
    #if expr.name in ['n','z','c','v']:
    r = re.search(nzcv_regex, expr.name)
    if r:
      return [r.group('r')]
    if not 'vals' in vars(expr):
      return []
    vals = expr.vals
    if op == 'Not':
      return isNZCVCheck(vals[0])
    elif op in ['And','Or']:
      ret = []
      for x in vals:
        rs = isNZCVCheck(x)
        if rs:
          ret.append(rs)
      return ret

def getExitCond(p_n,p):
    ns = set (p.loop_body (p_n))
    xs = [x for x in p.loop_body (p_n)
        if p.nodes[x].kind == 'Cond'
        if [ y for y in p.nodes[x].get_conts() 
                    if y not in ns and not y == 'Err']
        if isNZCVCheck (p.nodes[x].cond) ]

    ret = xs
    if len(ret) >1:
      for x in ret:
        print x
    if not ret:
      print 'exit cond not found !'
      return None
    if len(ret) != 1:
      print ret
    #assert len(ret) == 1
    return ret


def getOffset(p_n,p):
    #TODO: allow for multiple possible offsets
    vas = search.get_loop_var_analysis_at(p,p_n)
    xs = [(var,data) for (var,data) in vas if data[0]=='LoopLinearSeries' ]
    #exclude constants
    #xs = [x for x in xs if x[1][2].kind != 'Num']
    if len(xs) == 0:
      return None
    if len(xs) != 1:
      print 'len(xs) %d' % len(xs)
      offsets = []
      for x in xs:
        print 'x: %s' % str(x)
        this_off = parseOffset(x[1][2])
        if this_off > 1000:
          this_off = 0x100000000 - this_off
          assert this_off < 1000
        offsets.append (this_off)
      offsets = list(set(offsets))
      regs = [x[0].name for x in xs]
      if len(offsets) == 1:
        return regs, offsets[0]
      print 'multiple offsets ! %r' % offsets
      #FIXME maybe
      return regs,min(offsets)
    assert len(xs) == 1
    
    x = xs[0]
    var = x[0]
    #ok wht register are we looking at ? this is most likely at var
    register = var.name
    data = x[1]
    offset_data = data[2]
    offset = parseOffset(offset_data)
    #return [register],offset
    return register,offset


def getStopRegs(exit_cond, p, moving_regs):
    rcs = registersContained(exit_cond, p)
    dets = isNZCVAssign(exit_cond,p)
    print 'exit_cond %d' % exit_cond

    #print 'dets: %s' % str(dets)
    if dets:
      return rcs
    ret = []
    for x in p.preds[exit_cond]:
      ret += getStopRegs(x,p,moving_regs) 
    return list(set(ret))
    #return ret
def loopEntries(p_n,p):
    ns = list(p.loop_data[p_n][1])
    xs = [x for x in ns if [y for y in p.preds[x] if y not in ns]]
    if len(xs) != 1:
      print 'len: %s' % len(xs)
      for x in xs:
        print 'x: %s' % str(x)
    return xs

def guessBoundEntry(p_n,p,restrs,stop_reg,entry, how = False):
    tag = p.node_tags[p_n][0]
    #exactly once at the entry
    #restrs2 = restrs + ((entry, VisitCount('Number',1)), )
    restrs2 = restrs + ((p.loop_id(entry), VisitCount('Number',1)), )

    restrs3 = restr_others (p, restrs2, 2)
    rep = rep_graph.mk_graph_slice (p)
    epc = rep.get_pc (('Err', restrs3), tag = tag)
    #pc = rep.get_pc((entry, restrs3))
    try:
        pc_env = rep.get_node_pc_env((entry, restrs2))
    except:
        return None
    pc, env = pc_env
    pc_smt = to_smt_expr(pc,env,rep.solv)
    #pc, env = pc_env
    #ask for infeasible, and we should get a model where the negative of that is true
    hyp = mk_implies (mk_not (epc), mk_not (pc_smt))
    hyps = []
    m = {}
    ret = rep.test_hyp_whyps(hyp,hyps,model=m)
    if how:
      return m
    assert ret == False
    expr_stop_reg = syntax.mk_var (stop_reg, syntax.word32T)
    smt_stop_reg = solver.to_smt_expr(expr_stop_reg, env, rep.solv)
    expr = eval_model_expr(m,rep.solv,smt_stop_reg)
   
    #the more interesting question is, wht's stop_reg - moving_reg and stop_reg + moving_reg ?
    assert expr.kind == 'Num'
    return expr.val
   
def adjustTwoComps(xs):
    ret = []
    for x in xs:
        if x < 0x80000000:
          ret.append(x)
        else:
          two_comp = 0x100000000 - x
          ret.append(two_comp)
          ret.append(x)
    return ret

#all constants the loop specified by head contains
#all constants this problem contanis if whole_p is set
def allConstants(head,p,whole_p=False):
    if not whole_p:
      ns = list(p.loop_data[head][1])
    else:
      ns = p.nodes.keys()
    ret = []
    for x in ns:
      ret += constantsContained(x,p)
    ret = adjustTwoComps(ret)
    return sorted(list(set(ret)))

#all constants contained at the node p_n
def constantsContained(p_n,p):
    node = p.nodes[p_n]
    #if 'upds' not in vars(p.nodes[p_n]):
    #  return []
    stack = []
    if node.kind == 'Basic':
        upds = p.nodes[p_n].upds
        for x in upds:
          lv,v = x
          stack.append(v)
    elif node.kind == 'Cond':
        stack.append(p.nodes[p_n].get_args())
    else:
        return []
    ret = []
    while stack:
      v = stack.pop()
      if v.kind == 'Num':
        ret.append(v.val)
      elif 'vals' in vars(v):
        stack += v.vals
    ret = adjustTwoComps(ret)
    ret = [x for x in ret if x > 15] 
    
    return sorted(list(set(ret))) 

def canBSearch(exit_cond,p):
    flags = isNZCVCheck(p.nodes[exit_cond].get_args())
    assert flags
    if len(flags) == 1 and flags[0].startswith('z'):
      return False
    return True 

def guessBound(p_n,p, restrs):
    ret = getOffset(p_n,p)
    if ret == None:
      return None
    moving_regs, offset = ret 
    print 'moving_regs: %s' % (moving_regs)
    print 'offset: %d'  % offset

    exit_conds = getExitCond(p_n,p)
    if not exit_conds:
      return None
    stop_regs = []
    for exit_cond in exit_conds:
        stop_regs += getStopRegs(exit_cond,p,moving_regs)
    print 'stop_regs: %s' % str(stop_regs)
    entries = loopEntries(p_n,p)
    if restrs == None:
        others = [x for x in p.loop_heads() if not x == p_n]
        print 'others: %s' % str(others)
        restrs = tuple( [(n2, rep_graph.vc_options([0],[1])) for n2 in others] )
    vs = []
    for e in entries:
        for stop_reg in stop_regs:
            val = guessBoundEntry(p_n,p,restrs,stop_reg,e)
            if val == None:
                continue
	    print 'for entry %s stop_reg %s, val:%d, bound: %d' % ((p_n,
              p.node_tags[p_n]), stop_reg, val,val/offset )
	    vs.append(val/offset)
    return vs

def get_all_loop_heads ():
    loops = set ()
    abort_funs = set ()
    for f in all_asm_functions ():
      if not functions[f].entry:
        continue
      p = functions[f].as_problem (problem.Problem)
      try:
        p.do_loop_analysis ()
      except problem.Abort, e:
        abort_funs.add (f)
        continue
      for h in p.loop_heads ():
        # any address in the loop will do. pick the smallest one
        addr = min ([n for n in p.loop_body (h) if trace_refute.is_addr (n)])
        loops.add (addr)
    if abort_funs:
      trace ('Cannot analyse loops in: %s' % ', '.join (abort_funs))
    return loops

def search_all_loops ():
    all_loops = get_all_loop_heads ()
    for loop in all_loops:
      try:
        get_bound_super_ctxt (loop, [])
      except problem.Abort, e:
        continue

if __name__ == '__main__':
    import sys
    args = target_objects.load_target ()
    search_all_loops ()


