#
# Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

import syntax
import solver
import problem
import rep_graph
import search
import logic
import check

from target_objects import functions, trace, pairings, pre_pairings, printout
import target_objects

from logic import azip

from syntax import mk_var, word32T, builtinTs, mk_eq, mk_less_eq

last_stuff = [0]

def default_n_vc (p, n):
    head = p.loop_id (n)
    general = [(n2, rep_graph.vc_options ([0], [1]))
               for n2 in p.loop_heads ()
               if n2 != head]
    specific = [(head, rep_graph.vc_offs (1)) for _ in [1] if head]
    return (n, tuple (general + specific))

def split_sum_s_expr (expr, solv, extra_defs, typ):
    """divides up a linear expression 'a - b - 1 + a'
    into ({'a':2, 'b': -1}, -1) i.e. 'a' times 2 etc and constant
    value of -1."""
    #print 'expr:'
    print expr
#	print 'solvdefs:'
    #for ss in solv.defs:
    #	print ss
    #print solv.defs
    def rec (expr):
        return split_sum_s_expr (expr, solv, extra_defs, typ)
    if expr[0] == 'bvadd':
        var = {}
        const = 0
        for x in expr[1:]:
            (var2, const2) = rec (x)
            for (v, count) in var2.iteritems ():
                var.setdefault (v, 0)
                var[v] += count
            const += const2
        return (var, const)
    elif expr[0] == 'bvsub':
        (_, lhs, rhs) = expr
        (lvar, lconst) = rec (lhs)
        (rvar, rconst) = rec (rhs)
        const = lconst - rconst
        var = dict ([(v, lvar.get (v, 0) - rvar.get (v, 0))
                     for v in set.union (set (lvar), set (rvar))])
        return (var, const)
    elif expr in solv.defs:
        print 'in_solvdefs:'
        return rec (solv.defs[expr])
    elif expr in extra_defs:
        print 'extra_defs:'
        print extra_defs
        return rec (extra_defs[expr])
    elif expr[:2] in ['#x', '#b']:
        val = solver.smt_to_val (expr)
        print 'val:'
        print val
        assert val.kind == 'Num'
        return ({}, val.val)
    else:
        return ({expr: 1}, 0)

def split_merge_ite_sum_sexpr (foo):
    (s0, s1) = [solver.smt_num_t (n, typ) for n in [0, 1]]
    if y != s0:
        expr = ('bvadd', ('ite', cond, ('bvsub', x, y), s0), y)
        return rec (expr)
    (xvar, xconst) = rec (x)
    var = dict ([(('ite', cond, v, s0), n)
                 for (v, n) in xvar.iteritems ()])
    var.setdefault (('ite', cond, s1, s0), 0)
    var[('ite', cond, s1, s0)] += xconst
    return (var, 0)

def simplify_expr_whyps (sexpr, rep, hyps, cache = None, extra_defs = {},
                         bool_hyps = None):
    if cache == None:
        cache = {}
    if bool_hyps == None:
        bool_hyps = []
    if sexpr in extra_defs:
        sexpr = extra_defs[sexpr]
    if sexpr in rep.solv.defs:
        sexpr = rep.solv.defs[sexpr]
    if sexpr[0] == 'ite':
        (_, cond, x, y) = sexpr
        cond_exp = solver.mk_smt_expr (solver.flat_s_expression (cond),
                                       syntax.boolT)
        (mk_nimp, mk_not) = (syntax.mk_n_implies, syntax.mk_not)
        if rep.test_hyp_whyps (mk_nimp (bool_hyps, cond_exp),
                               hyps, cache = cache):
            return x
        elif rep.test_hyp_whyps (mk_nimp (bool_hyps, mk_not (cond_exp)),
                                 hyps, cache = cache):
            return y
        x = simplify_expr_whyps (x, rep, hyps, cache = cache,
                                 extra_defs = extra_defs,
                                 bool_hyps = bool_hyps + [cond_exp])
        y = simplify_expr_whyps (y, rep, hyps, cache = cache,
                                 extra_defs = extra_defs,
                                 bool_hyps = bool_hyps + [syntax.mk_not (cond_exp)])
        if x == y:
            return x
        return ('ite', cond, x, y)
    return sexpr

last_10_non_const = []

def offs_expr_const (addr_expr, sp_expr, rep, hyps, extra_defs = {},
                     cache = None, typ = syntax.word32T):
    """if the offset between a stack addr and the initial stack pointer
    is a constant offset, try to compute it."""
    if syntax.is_64bit:
        typ = syntax.word64T
    print 'bla:'
    print typ
    addr_x = solver.parse_s_expression (addr_expr)
    sp_x = solver.parse_s_expression (sp_expr)
    print addr_x
    print sp_x
    vs = [(addr_x, 1), (sp_x, -1)]
    const = 0

    while True:
        start_vs = list (vs)
        print 'vs:'
        print vs
        print 'start_vs:'
        print start_vs
        new_vs = {}
        for (x, mult) in vs:
            (var, c) = split_sum_s_expr (x, rep.solv, extra_defs,
                                         typ = typ)
            for v in var:
                new_vs.setdefault (v, 0)
                new_vs[v] += var[v] * mult
            const += c * mult
        print 'new_vs:'
        print new_vs

        vs = [(x, n) for (x, n) in new_vs.iteritems ()
              if n % (2 ** typ.num) != 0]
        print 'vs:'
        print vs
        if not vs:
            return const
        vs = [(simplify_expr_whyps (x, rep, hyps,
                                    cache = cache, extra_defs = extra_defs), n)
              for (x, n) in vs]
        if sorted (vs) == sorted (start_vs):
            pass # vs = split_merge_ite_sum_sexpr (vs)
        if sorted (vs) == sorted (start_vs):
            trace ('offs_expr_const: not const')
            trace ('%s - %s' % (addr_expr, sp_expr))
            trace (str (vs))
            trace (str (hyps))
            last_10_non_const.append ((addr_expr, sp_expr, vs, hyps))
            del last_10_non_const[:-10]
            return None

def has_stack_var (expr, stack_var):
    while True:
        if expr.is_op ('MemUpdate'):
            [m, p, v] = expr.vals
            expr = m
        elif expr.kind == 'Var':
            return expr == stack_var
        else:
            assert not 'has_stack_var: expr kind', expr

def mk_not_callable_hyps (p):
    hyps = []
    for n in p.nodes:
        if p.nodes[n].kind != 'Call':
            continue
        if get_asm_callable (p.nodes[n].fname):
            continue
        tag = p.node_tags[n][0]
        hyp = rep_graph.pc_false_hyp ((default_n_vc (p, n), tag))
        hyps.append (hyp)
    return hyps

last_get_ptr_offsets = [0]
last_get_ptr_offsets_setup = [0]

def get_ptr_offsets (p, n_ptrs, bases, hyps = [], cache = None,
                     fail_early = False):
    """detect which ptrs are guaranteed to be at constant offsets
    from some set of basis ptrs"""
    rep = rep_graph.mk_graph_slice (p, fast = True)
    if cache == None:
        cache = {}
    last_get_ptr_offsets[0] = (p, n_ptrs, bases, hyps)

    smt_bases = []
    for (n, ptr, k) in bases:
        n_vc = default_n_vc (p, n)
        (_, env) = rep.get_node_pc_env (n_vc)
        print 'ptr\n'
        print ptr
        print '\n'
        print 'env\n'
        print env

        print '\n'
        #print rep.solv
        smt = solver.smt_expr (ptr, env, rep.solv)

        smt_bases.append ((smt, k))
        ptr_typ = ptr.typ

    smt_ptrs = []
    for (n, ptr) in n_ptrs:
        n_vc = default_n_vc (p, n)
        pc_env = rep.get_node_pc_env (n_vc)
        if not pc_env:
            continue
        smt = solver.smt_expr (ptr, pc_env[1], rep.solv)
        hyp = rep_graph.pc_true_hyp ((n_vc, p.node_tags[n][0]))
        smt_ptrs.append (((n, ptr), smt, hyp))

    hyps = hyps + mk_not_callable_hyps (p)
    for tag in set ([p.node_tags[n][0] for (n, _) in n_ptrs]):
        hyps = hyps + init_correctness_hyps (p, tag)
    tags = set ([p.node_tags[n][0] for (n, ptr) in n_ptrs])
    ex_defs = {}
    for t in tags:
        ex_defs.update (get_extra_sp_defs (rep, t))

    offs = []

    print 'smt_bases:'
    print smt_bases
    print 'smt_ptrs:'
    print smt_ptrs

    for (v, ptr, hyp) in smt_ptrs:
        off = None
        for (ptr2, k) in smt_bases:
            off = offs_expr_const (ptr, ptr2, rep, [hyp] + hyps,
                                   cache = cache, extra_defs = ex_defs,
                                   typ = ptr_typ)
            print ptr_typ
            if off != None:
                offs.append ((v, off, k))
                break
        if off == None:
            trace ('get_ptr_offs fallthrough at %d: %s' % v)
            trace (str ([hyp] + hyps))
            #print v
            #print ptr
            #rv64_hack
            # it is possible that rv64 function does not change stack at all
            #assert not fail_early, (v, ptr)
        print 'get_ptr_offs:'
        print off

    return offs

def init_correctness_hyps (p, tag):
    (_, fname, _) = p.get_entry_details (tag)
    if fname not in pairings:
        # conveniently handles bootstrap case
        return []
    # revise if multi-pairings for ASM an option
    [pair] = pairings[fname]
    true_tag = None
    if tag in pair.funs:
        true_tag = tag
    elif p.hook_tag_hints.get (tag, tag) in pair.funs:
        true_tag = p.hook_tag_hints.get (tag, tag)
    if true_tag == None:
        return []
    (inp_eqs, _) = pair.eqs
    in_tag = "%s_IN" % true_tag
    eqs = [eq for eq in inp_eqs if eq[0][1] == in_tag
           and eq[1][1] == in_tag]
    return check.inst_eqs (p, (), eqs, {true_tag: tag})

extra_symbols = set ()

def preserves_sp (fname):
    """all functions will keep the stack pointer equal, whether they have
    pairing partners or not."""
    assume_sp_equal = bool (target_objects.hooks ('assume_sp_equal'))
    print assume_sp_equal
    #assert False
    if not extra_symbols:
        for fname2 in target_objects.symbols:
            extra_symbols.add(fname2)
            extra_symbols.add('_'.join (fname2.split ('.')))
    return (get_asm_calling_convention (fname)
            or assume_sp_equal
            or fname in extra_symbols)

def get_extra_sp_defs (rep, tag):
    """add extra defs/equalities about stack pointer for the
    purposes of stack depth analysis."""
    # FIXME how to parametrise this?
    if syntax.arch == 'armv7':
        sp = mk_var ('r13', syntax.word32T)
        #assert False
    elif syntax.arch == 'rv64':
        sp = mk_var('r2', syntax.word64T)
        #print sp
        #assert False
    else:
        print 'unsupported arch %s' % syntax.arch
        assert False


    defs = {}

    fcalls = [n_vc for n_vc in rep.funcs
              if logic.is_int (n_vc[0])
              if rep.p.node_tags[n_vc[0]][0] == tag
              if preserves_sp (rep.p.nodes[n_vc[0]].fname)]
    for (n, vc) in fcalls:
        (inputs, outputs, _) = rep.funcs[(n, vc)]
        if (sp.name, sp.typ) not in outputs:
            continue
        inp_sp = solver.smt_expr (sp, inputs, rep.solv)
        inp_sp = solver.parse_s_expression (inp_sp)
        out_sp = solver.smt_expr (sp, outputs, rep.solv)
        out_sp = solver.parse_s_expression (out_sp)
        if inp_sp != out_sp:
            defs[out_sp] = inp_sp
    return defs

def get_stack_sp (p, tag):
    """get stack and stack-pointer variables"""
    entry = p.get_entry (tag)
    #print 'entry'
    #print entry
    renames = p.entry_exit_renames (tags = [tag])
    r = renames[tag + '_IN']
    #print renames
    #print r
    #assert False

    if syntax.arch == 'armv7':
        sp = syntax.rename_expr (mk_var ('r13', syntax.word32T), r)
        #assert False
    elif syntax.arch == 'rv64':
        sp = syntax.rename_expr(mk_var('r2', syntax.word64T), r)
        #print sp
    else:
        print "Unsupported arch %s" % syntax.arch
        assert False

    stack = syntax.rename_expr (mk_var ('stack',
                                        syntax.builtinTs['Mem']), r)
    #print stack
    return (stack, sp)

def pseudo_node_lvals_rvals (node):
    assert node.kind == 'Call'
    cc = get_asm_calling_convention_at_node (node)
    if not cc:
        return None

    arg_vars = set ([var for arg in cc['args']
                     for var in syntax.get_expr_var_set (arg)])

    callee_saved_set = set (cc['callee_saved'])
    rets = [(nm, typ) for (nm, typ) in node.rets
            if mk_var (nm, typ) not in callee_saved_set]

    return (rets, arg_vars)

def is_asm_node (p, n):
    tag = p.node_tags[n][0]
    return tag == 'ASM' or p.hook_tag_hints.get (tag, None) == 'ASM'

def all_pseudo_node_lvals_rvals (p):
    pseudo = {}
    for n in p.nodes:
        if not is_asm_node (p, n):
            continue
        elif p.nodes[n].kind != 'Call':
            continue
        ps = pseudo_node_lvals_rvals (p.nodes[n])
        if ps != None:
            pseudo[n] = ps
    return pseudo

def adjusted_var_dep_outputs_for_tag (p, tag):
    (ent, fname, _) = p.get_entry_details (tag)
    fun = functions[fname]
    cc = get_asm_calling_convention (fname)
    callee_saved_set = set (cc['callee_saved'])
    ret_set = set ([(nm, typ) for ret in cc['rets']
                    for (nm, typ) in syntax.get_expr_var_set (ret)])
    rets = [(nm2, typ) for ((nm, typ), (nm2, _))
            in azip (fun.outputs, p.outputs[tag])
            if (nm, typ) in ret_set
            or mk_var (nm, typ) in callee_saved_set]
    return rets

def adjusted_var_dep_outputs (p):
    outputs = {}
    for tag in p.outputs:
        ent = p.get_entry (tag)
        if is_asm_node (p, ent):
            outputs[tag] = adjusted_var_dep_outputs_for_tag (p, tag)
        else:
            outputs[tag] = p.outputs[tag]
    def output (n):
        tag = p.node_tags[n][0]
        return outputs[tag]
    return output

def is_stack (expr):
    return expr.kind == 'Var' and 'stack' in expr.name

class StackOffsMissing (Exception):
    pass

def stack_virtualise_expr (expr, sp_offs):
    #print expr.kind
    #print 'kk \n'

    if expr.is_op ('MemAcc') and is_stack (expr.vals[0]):
        #	print 'here \n'
        [m, p] = expr.vals
    #	print 'type'
    #	print expr.typ
    #	print '\n'
    #	print expr

        if syntax.is_64bit:
            mk_word = syntax.mk_word64
        else:
            mk_word = syntax.mk_word32

        if expr.typ == syntax.word8T:
            ps = [(syntax.mk_minus (p, mk_word(n)), n)
                  for n in [0, 1, 2, 3]]
        elif expr.typ == syntax.word32T:
            ps = [(p, 0)]
            assert False
        elif expr.typ == syntax.word64T:
            ps = [(p, 0)]
            #assert False
        else:
            assert expr.typ == syntax.word32T, expr
        ptrs = [(p, 'MemAcc') for (p, _) in ps]
        if sp_offs == None:
            return (ptrs, None)
        # FIXME: very 32-bit specific
        assert False

        ps = [(p, n) for (p, n) in ps if p in sp_offs
              if sp_offs[p][1] % 4 == 0]
        if not ps:
            return (ptrs, expr)
        [(p, n)] = ps
        if p not in sp_offs:
            raise StackOffsMissing ()
        (k, offs) = sp_offs[p]
        v = mk_var (('Fake', k, offs), syntax.word32T)
        if n != 0:
            v = syntax.mk_shiftr (v, n * 8)
        v = syntax.mk_cast (v, expr.typ)
        return (ptrs, v)
    elif expr.kind == 'Op':
        vs = [stack_virtualise_expr (v, sp_offs) for v in expr.vals]
        return ([p for (ptrs, _) in vs for p in ptrs],
                syntax.adjust_op_vals (expr, [v for (_, v) in vs]))
    else:
        return ([], expr)

def stack_virtualise_upd (((nm, typ), expr), sp_offs):
    #assert False
    if 'stack' in nm:
        upds = []
        ptrs = []
        while expr.is_op ('MemUpdate'):
            [m, p, v] = expr.vals
            ptrs.append ((p, 'MemUpdate'))
            (ptrs2, v2) = stack_virtualise_expr (v, sp_offs)
            ptrs.extend (ptrs2)
            if sp_offs != None:
                if p not in sp_offs:
                    raise StackOffsMissing ()
                (k, offs) = sp_offs[p]
                #rv64_hack
                upds.append (((('Fake', k, offs),
                               syntax.word64T), v2))
            expr = m
        assert is_stack (expr), expr
        return (ptrs, upds)
    else:
        (ptrs, expr2) = stack_virtualise_expr (expr, sp_offs)
        return (ptrs, [((nm, typ), expr2)])

def stack_virtualise_ret (expr, sp_offs):
    #assert False
    if expr.kind == 'Var':
        return ([], (expr.name, expr.typ))
    elif expr.is_op ('MemAcc'):
        [m, p] = expr.vals
    #	assert expr.typ == syntax.word32T, expr
        assert is_stack (m), expr
        if sp_offs != None:
            (k, offs) = sp_offs[p]
            #rv64_hack
            r = (('Fake', k, offs), syntax.word64T)
        else:
            r = None
        return ([(p, 'MemUpdate')], r)
    else:
        assert not 'ret expr understood', expr

def stack_virtualise_node (node, sp_offs):
    #assert False
    if node.kind == 'Cond':
        (ptrs, cond) = stack_virtualise_expr (node.cond, sp_offs)
        if sp_offs == None:
            return (ptrs, None)
        else:
            return (ptrs, syntax.Node ('Cond',
                    node.get_conts (), cond))
    elif node.kind == 'Call':
        print node.fname
        assert False
        if is_instruction (node.fname):
            return ([], node)
        cc = get_asm_calling_convention_at_node (node)
        print cc
        assert False
        assert cc != None, node.fname
        args = [arg for arg in cc['args'] if not is_stack (arg)]
        args = [stack_virtualise_expr (arg, sp_offs) for arg in args]
        rets = [ret for ret in cc['rets_inp'] if not is_stack (ret)]
        rets = [stack_virtualise_ret (ret, sp_offs) for ret in rets]
        ptrs = list (set ([p for (ps, _) in args for p in ps]
                          + [p for (ps, _) in rets for p in ps]))
        if sp_offs == None:
            return (ptrs, None)
        else:
            return (ptrs, syntax.Node ('Call', node.cont,
                    (None, [v for (_, v) in args]
                     + [p for (p, _) in ptrs],
                     [r for (_, r) in rets])))
    elif node.kind == 'Basic':
        upds = [stack_virtualise_upd (upd, sp_offs) for upd in node.upds]
        ptrs = list (set ([p for (ps, _) in upds for p in ps]))
        if sp_offs == None:
            return (ptrs, None)
        else:
            #rv64_hack
            ptr_upds = [(('unused#ptr#name%d' % i, syntax.word64T),
                         ptr) for (i, (ptr, _)) in enumerate (ptrs)]
            return (ptrs, syntax.Node ('Basic', node.cont,
                    [upd for (_, us) in upds for upd in us]
                + ptr_upds))
    else:
        assert not "node kind understood", node.kind

def mk_get_local_offs (p, tag, sp_reps):
    if syntax.is_64bit:
        mk_word = syntax.mk_word64
        wordT = syntax.word64T
    else:
        mk_word = syntax.mk_word32
        wordT = syntax.word32T

    (stack, _) = get_stack_sp (p, tag)
    def mk_local (n, kind, off, k):
        (v, off2) = sp_reps[n][k]
        ptr = syntax.mk_plus (v, mk_word(off + off2))
        if kind == 'Ptr':
            return ptr
        elif kind == 'MemAcc':
            return syntax.mk_memacc (stack, ptr, wordT)
    return mk_local

def adjust_ret_ptr (ptr):
    """this is a bit of a hack.

    the return slots are named based on r0_input, which will be unchanged,
    which is handy, but we really want to be talking about r0, which will
    produce meaningful offsets against the pointers actually used in the
    program."""
    #assert False
    if syntax.is_64bit:
        return logic.var_subst(ptr,
                               {('ret_addr_inpt', syntax.word64T):
                                syntax.mk_var('r10', syntax.word32T)},
                               must_subst = False)
    else:
        return logic.var_subst (ptr, {('ret_addr_input', syntax.word32T):
                                      syntax.mk_var ('r0', syntax.word32T)}, must_subst = False)

def get_loop_virtual_stack_analysis (p, tag):
    """computes variable liveness etc analyses with stack slots treated
    as virtual variables."""
    cache_key = ('loop_stack_analysis', tag)
    if cache_key in p.cached_analysis:
        return p.cached_analysis[cache_key]

    (ent, fname, _) = p.get_entry_details (tag)
    (_, sp) = get_stack_sp (p, tag)
    cc = get_asm_calling_convention (fname)
    rets = list (set ([ptr for arg in cc['rets']
                       for (ptr, _) in stack_virtualise_expr (arg, None)[0]]))
    print cc
    print rets
    assert None
    rets = [adjust_ret_ptr (ret) for ret in rets]
    renames = p.entry_exit_renames (tags = [tag])
    r = renames[tag + '_OUT']
    rets = [syntax.rename_expr (ret, r) for ret in rets]

    ns = [n for n in p.nodes if p.node_tags[n][0] == tag]
    loop_ns = logic.minimal_loop_node_set (p)

    ptrs = list (set ([(n, ptr) for n in ns
                       for ptr in (stack_virtualise_node (p.nodes[n], None))[0]]))
    ptrs += [(n, (sp, 'StackPointer')) for n in ns if n in loop_ns]
    offs = get_ptr_offsets (p, [(n, ptr) for (n, (ptr, _)) in ptrs],
                            [(ent, sp, 'stack')]
                            + [(ent, ptr, 'indirect_ret') for ptr in rets[:1]])

    ptr_offs = {}
    rep_offs = {}
    upd_offsets = {}
    for ((n, ptr), off, k) in offs:
        off = norm_int (off, 32)
        ptr_offs.setdefault (n, {})
        rep_offs.setdefault (n, {})
        ptr_offs[n][ptr] = (k, off)
        rep_offs[n][k] = (ptr, - off)

    for (n, (ptr, kind)) in ptrs:
        if kind == 'MemUpdate' and n in loop_ns:
            loop = p.loop_id (n)
            (k, off) = ptr_offs[n][ptr]
            upd_offsets.setdefault (loop, set ())
            upd_offsets[loop].add ((k, off))
    loc_offs = mk_get_local_offs (p, tag, rep_offs)

    adj_nodes = {}
    for n in ns:
        try:
            (_, node) = stack_virtualise_node (p.nodes[n],
                                               ptr_offs.get (n, {}))
        except StackOffsMissing, e:
            printout ("Stack analysis issue at (%d, %s)."
                      % (n, p.node_tags[n]))
            node = p.nodes[n]
        adj_nodes[n] = node

    # finally do analysis on this collection of nodes

    preds = dict (p.preds)
    preds['Ret'] = [n for n in preds['Ret'] if p.node_tags[n][0] == tag]
    preds['Err'] = [n for n in preds['Err'] if p.node_tags[n][0] == tag]
    vds = logic.compute_var_deps (adj_nodes,
                                  adjusted_var_dep_outputs (p), preds)

    result = (vds, adj_nodes, loc_offs, upd_offsets, (ptrs, offs))
    p.cached_analysis[cache_key] = result
    return result

def norm_int (n, radix):
    n = n & ((1 << radix) - 1)
    n2 = n - (1 << radix)
    if abs (n2) < abs (n):
        return n2
    else:
        return n

def loop_var_analysis (p, split):
    """computes the same loop dataflow analysis as in the 'logic' module
    but with stack slots treated as virtual variables."""

    if syntax.is_64bit:
        mk_word = syntax.mk_word64
    else:
        mk_word = syntax.mk_word32

    if not is_asm_node (p, split):
        return None
    head = p.loop_id (split)
    tag = p.node_tags[split][0]
    assert head

    #print 'aa\n'
    #print p

    key = ('loop_stack_virtual_var_cycle_analysis', split)
    if key in p.cached_analysis:
        return p.cached_analysis[key]

    (vds, adj_nodes, loc_offs,
     upd_offsets, _) = get_loop_virtual_stack_analysis (p, tag)
    loop = p.loop_body (head)

    va = logic.compute_loop_var_analysis (p, vds, split,
                                          override_nodes = adj_nodes)

    (stack, _) = get_stack_sp (p, tag)

    va2 = []
    uoffs = upd_offsets.get (head, [])
    for (v, data) in va:
        if v.kind == 'Var' and v.name[0] == 'Fake':
            (_, k, offs) = v.name
            if (k, offs) not in uoffs:
                continue
            v2 = loc_offs (split, 'MemAcc', offs, k)
            va2.append ((v2, data))
        elif v.kind == 'Var' and v.name.startswith ('stack'):
            assert v.typ == stack.typ
            continue
        else:
            va2.append ((v, data))
    stack_const = stack
    for (k, off) in uoffs:
        stack_const = syntax.mk_memupd (stack_const,
                                        loc_offs (split, 'Ptr', off, k),
                                        mk_word(0))
    sp = asm_stack_rep_hook (p, (stack.name, stack.typ), 'Loop', split)
    assert sp and sp[0] == 'SplitMem', (split, sp)
    (_, st_split) = sp
    stack_const = logic.mk_stack_wrapper (st_split, stack_const, [])
    stack_const = logic.mk_eq_selective_wrapper (stack_const,
                                                 ([], [0]))

    va2.append ((stack_const, 'LoopConst'))

    p.cached_analysis[key] = va2
    return va2

def inline_no_pre_pairing (p):
    # FIXME: handle code sharing with check.inline_completely_unmatched
    while True:
        ns = [n for n in p.nodes if p.nodes[n].kind == 'Call'
              if p.nodes[n].fname not in pre_pairings
              if not is_instruction (p.nodes[n].fname)]
        for n in ns:
            trace ('Inlining %s at %d.' % (p.nodes[n].fname, n))
            problem.inline_at_point (p, n)
        if not ns:
            return

last_asm_stack_depth_fun = [0]

def check_before_guess_asm_stack_depth (fun):
    from solver import smt_expr
    if not fun.entry:
        return None
    p = fun.as_problem (problem.Problem, name = 'Target')
    try:
        p.do_analysis ()
        p.check_no_inner_loops ()
        inline_no_pre_pairing (p)
    except problem.Abort, e:
        return None
    rep = rep_graph.mk_graph_slice (p, fast = True)
    try:
        rep.get_pc (default_n_vc (p, 'Ret'), 'Target')
        err_pc = rep.get_pc (default_n_vc (p, 'Err'), 'Target')
    except solver.EnvMiss, e:
        return None

    inlined_funs = set ([fn for (_, _, fn) in p.inline_scripts['Target']])
    if inlined_funs:
        printout ('  (stack analysis also involves %s)'
                  % ', '.join(inlined_funs))

    return p

def guess_asm_stack_depth (fun):
    p = check_before_guess_asm_stack_depth (fun)
    if not p:
        return (0, {})

    last_asm_stack_depth_fun[0] = fun.name

    entry = p.get_entry ('Target')
    print 'entry: '
    print entry
    (_, sp) = get_stack_sp (p, 'Target')
    print 'sp:'
    print sp
    nodes = get_asm_reachable_nodes (p, tag_set = ['Target'])
    print "nodes:"
    print map(hex, list(nodes))
    offs = get_ptr_offsets (p, [(n, sp) for n in nodes],
                            [(entry, sp, 'InitSP')], fail_early = True)

    #rv64_hack
    if not len(offs) == len(nodes):
        print len(offs)
        print offs
        print len(nodes)
        print nodes

    #rv64 hack
    #assert len (offs) == len (nodes), map (hex, set (nodes)
    #	- set ([n for ((n, _), _, _) in offs]))

    all_offs = [(n, signed_offset (off, 32, 10 ** 6))
                for ((n, ptr), off, _) in offs]
    min_offs = min ([offs for (n, offs) in all_offs])
    max_offs = max ([offs for (n, offs) in all_offs])

    assert min_offs >= 0 or max_offs <= 0, all_offs
    multiplier = 1
    if min_offs < 0:
        multiplier = -1
        max_offs = - min_offs

    fcall_offs = [(p.nodes[n].fname, offs * multiplier)
                  for (n, offs) in all_offs if p.nodes[n].kind == 'Call']
    fun_offs = {}
    for f in set ([f for (f, _) in fcall_offs]):
        fun_offs[f] = max ([offs for (f2, offs) in fcall_offs
                            if f2 == f])

    return (max_offs, fun_offs)

def signed_offset (n, bits, bound = 0):
    n = n & ((1 << bits) - 1)
    if n >= (1 << (bits - 1)):
        n = n - (1 << bits)
    if bound:
        assert n <= bound, (n, bound)
        assert n >= (- bound), (n, bound)
    return n

def ident_conds (fname, idents):
    rolling = syntax.true_term
    conds = []
    for ident in idents.get (fname, [syntax.true_term]):
        conds.append ((ident, syntax.mk_and (rolling, ident)))
        rolling = syntax.mk_and (rolling, syntax.mk_not (ident))
    return conds

def ident_callables (fname, callees, idents):
    from solver import to_smt_expr, smt_expr
    from syntax import mk_not, mk_and, true_term

    auto_callables = dict ([((ident, f, true_term), True)
                            for ident in idents.get (fname, [true_term])
                            for f in callees if f not in idents])

    if not [f for f in callees if f in idents]:
        return auto_callables

    fun = functions[fname]
    p = fun.as_problem (problem.Problem, name = 'Target')
    check_ns = [(n, ident, cond) for n in p.nodes
                if p.nodes[n].kind == 'Call'
                if p.nodes[n].fname in idents
                for (ident, cond) in ident_conds (p.nodes[n].fname, idents)]

    p.do_analysis ()
    assert check_ns

    rep = rep_graph.mk_graph_slice (p, fast = True)
    err_hyp = rep_graph.pc_false_hyp ((default_n_vc (p, 'Err'), 'Target'))

    callables = auto_callables
    nhyps = mk_not_callable_hyps (p)

    for (ident, cond) in ident_conds (fname, idents):
        renames = p.entry_exit_renames (tags = ['Target'])
        cond = syntax.rename_expr (cond, renames['Target_IN'])
        entry = p.get_entry ('Target')
        e_vis = ((entry, ()), 'Target')
        hyps = [err_hyp, rep_graph.eq_hyp ((cond, e_vis),
                                           (true_term, e_vis))]

        for (n, ident2, cond2) in check_ns:
            k = (ident, p.nodes[n].fname, ident2)
            (inp_env, _, _) = rep.get_func (default_n_vc (p, n))
            pc = rep.get_pc (default_n_vc (p, n))
            cond2 = to_smt_expr (cond2, inp_env, rep.solv)
            if rep.test_hyp_whyps (mk_not (mk_and (pc, cond2)),
                                   hyps + nhyps):
                callables[k] = False
            else:
                callables[k] = True
    return callables

def compute_immediate_stack_bounds (idents, names):
    from syntax import true_term
    immed = {}
    names = sorted (names)
    for (i, fname) in enumerate (names):
        printout ('Doing stack analysis for %r. (%d of %d)' % (fname,
                                                               i + 1, len (names)))
        fun = functions[fname]
        (offs, fn_offs) = guess_asm_stack_depth (fun)
        callables = ident_callables (fname, fn_offs.keys (), idents)
        for ident in idents.get (fname, [true_term]):
            calls = [((fname2, ident2), fn_offs[fname2])
                     for fname2 in fn_offs
                     for ident2 in idents.get (fname2, [true_term])
                     if callables[(ident, fname2, ident2)]]
            immed[(fname, ident)] = (offs, dict (calls))
    last_immediate_stack_bounds[0] = immed
    return immed

last_immediate_stack_bounds = [0]

def immediate_stack_bounds_loop (immed):
    graph = dict ([(k, immed[k][1].keys ()) for k in immed])
    graph['ENTRY'] = list (immed)
    comps = logic.tarjan (graph, ['ENTRY'])
    rec_comps = [[x] + y for (x, y) in comps if y]
    return rec_comps

def compute_recursive_stack_bounds (immed):
    assert not immediate_stack_bounds_loop (immed)
    bounds = {}
    todo = immed.keys ()
    report = 1000
    while todo:
        if len (todo) >= report:
            trace ('todo length %d' % len (todo))
            trace ('tail: %s' % todo[-20:])
            report += 1000
        (fname, ident) = todo.pop ()
        if (fname, ident) in bounds:
            continue
        (static, calls) = immed[(fname, ident)]
        if [1 for k in calls if k not in bounds]:
            todo.append ((fname, ident))
            todo.extend (calls.keys ())
            continue
        else:
            bounds[(fname, ident)] = max ([static]
                                          + [bounds[k] + calls[k] for k in calls])
    return bounds

def stack_bounds_to_closed_form (bounds, names, idents):
    closed = {}
    if syntax.is_64bit:
        mk_word = syntax.mk_word64
    else:
        mk_word = syntax.mk_word32
    #print mk_word
    #assert False

    for fname in names:
        #res = syntax.mk_word32 (bounds[(fname, syntax.true_term)])
        res = mk_word(bounds[(fname, syntax.true_term)])
        extras = []
        if fname in idents:
            assert idents[fname][-1] == syntax.true_term
            extras = reversed (idents[fname][:-1])
        for ident in extras:
            #alt = syntax.mk_word32 (bounds[(fname, ident)])
            alt = mk_word(bounds[(fname, ident)])
            res = syntax.mk_if (ident, alt, res)
        closed[fname] = res
    return closed

def compute_asm_stack_bounds (idents, names):
    immed = compute_immediate_stack_bounds (idents, names)
    bounds = compute_recursive_stack_bounds (immed)
    closed = stack_bounds_to_closed_form (bounds, names, idents)
    return closed

recursion_trace = []
recursion_last_assns = [[]]

def get_recursion_identifiers (funs, extra_unfolds = []):
    idents = {}
    del recursion_trace[:]
    graph = dict ([(f, list (functions[f].function_calls ()))
                   for f in functions])
    fs = funs
    fs2 = set ()
    while fs2 != fs:
        fs2 = fs
        fs = set.union (set ([f for f in graph if [f2 for f2 in graph[f]
                        if f2 in fs2]]),
                        set ([f2 for f in fs2 for f2 in graph[f]]), fs2)
    graph = dict ([(f, graph[f]) for f in fs])
    entries = list (fs - set ([f2 for f in graph for f2 in graph[f]]))
    comps = logic.tarjan (graph, entries)
    for (head, tail) in comps:
        if tail or head in graph[head]:
            group = [head] + list (tail)
            idents2 = compute_recursion_idents (group,
                                                extra_unfolds)
            idents.update (idents2)
    return idents

def compute_recursion_idents (group, extra_unfolds):
    idents = {}
    group = set (group)
    recursion_trace.append ('Computing for group %s' % group)
    printout ('Doing recursion analysis for function group:')
    printout ('  %s' % list(group))
    prevs = set ([f for f in functions
                  if [f2 for f2 in functions[f].function_calls () if f2 in group]])
    for f in prevs - group:
        recursion_trace.append ('  checking for %s' % f)
        trace ('Checking idents for %s' % f)
        while add_recursion_ident (f, group, idents, extra_unfolds):
            pass
    return idents

def function_link_assns (p, call_site, tag):
    call_vis = (default_n_vc (p, call_site), p.node_tags[call_site][0])
    return rep_graph.mk_function_link_hyps (p, call_vis, tag)

def add_recursion_ident (f, group, idents, extra_unfolds):
    from syntax import mk_eq, mk_implies, mk_var
    p = problem.Problem (None, name = 'Recursion Test')
    chain = []
    tag = 'fun0'
    p.add_entry_function (functions[f], tag)
    p.do_analysis ()
    assns = []
    recursion_last_assns[0] = assns

    while True:
        res = find_unknown_recursion (p, group, idents, tag, assns,
                                      extra_unfolds)
        if res == None:
            break
        if p.nodes[res].fname not in group:
            problem.inline_at_point (p, res)
            continue
        fname = p.nodes[res].fname
        chain.append (fname)
        tag = 'fun%d' % len (chain)
        (args, _, entry) = p.add_entry_function (functions[fname], tag)
        p.do_analysis ()
        assns += function_link_assns (p, res, tag)
    if chain == []:
        return None
    recursion_trace.append ('  created fun chain %s' % chain)
    word_args = [(i, mk_var (s, typ))
                 for (i, (s, typ)) in enumerate (args)
                 if typ.kind == 'Word']
    rep = rep_graph.mk_graph_slice (p, fast = True)
    (_, env) = rep.get_node_pc_env ((entry, ()))

    m = {}
    res = rep.test_hyp_whyps (syntax.false_term, assns, model = m)
    assert m

    if find_unknown_recursion (p, group, idents, tag, [], []) == None:
        idents.setdefault (fname, [])
        idents[fname].append (syntax.true_term)
        recursion_trace.append ('      found final ident for %s' % fname)
        return syntax.true_term
    assert word_args
    recursion_trace.append ('      scanning for ident for %s' % fname)
    for (i, arg) in word_args:
        (nm, typ) = functions[fname].inputs[i]
        arg_smt = solver.to_smt_expr (arg, env, rep.solv)
        val = search.eval_model_expr (m, rep.solv, arg_smt)
        if not rep.test_hyp_whyps (mk_eq (arg_smt, val), assns):
            recursion_trace.append ('      discarded %s = 0x%x, not stable' % (nm, val.val))
            continue
        entry_vis = ((entry, ()), tag)
        ass = rep_graph.eq_hyp ((arg, entry_vis), (val, entry_vis))
        res = find_unknown_recursion (p, group, idents, tag,
                                      assns + [ass], [])
        if res:
            fname2 = p.nodes[res].fname
            recursion_trace.append ('      discarded %s, allows recursion to %s' % (nm, fname2))
            continue
        eq = syntax.mk_eq (mk_var (nm, typ), val)
        idents.setdefault (fname, [])
        idents[fname].append (eq)
        recursion_trace.append ('    found ident for %s: %s' % (fname, eq))
        return eq
    assert not "identifying assertion found"

def find_unknown_recursion (p, group, idents, tag, assns, extra_unfolds):
    from syntax import mk_not, mk_and, foldr1
    rep = rep_graph.mk_graph_slice (p, fast = True)
    for n in p.nodes:
        if p.nodes[n].kind != 'Call':
            continue
        if p.node_tags[n][0] != tag:
            continue
        fname = p.nodes[n].fname
        if fname in extra_unfolds:
            return n
        if fname not in group:
            continue
        (inp_env, _, _) = rep.get_func (default_n_vc (p, n))
        pc = rep.get_pc (default_n_vc (p, n))
        new = foldr1 (mk_and, [pc] + [syntax.mk_not (
            solver.to_smt_expr (ident, inp_env, rep.solv))
            for ident in idents.get (fname, [])])
        if rep.test_hyp_whyps (mk_not (new), assns):
            continue
        return n
    return None

asm_cc_cache = {}

def is_instruction (fname):
    bits = fname.split ("'")
    return bits[1:] and bits[:1] in [["l_impl"], ["instruction"]]

def get_asm_calling_convention (fname):
    print fname
    print "callcon:"
    #assert False
    if fname in asm_cc_cache:
        print fname
        print asm_cc_cache[fname]
        #assert False
        print 'cachedcc:'
        return asm_cc_cache[fname]
    if fname not in pre_pairings:
        bits = fname.split ("'")
        if not is_instruction (fname):
            trace ("Warning: unusual unmatched function (%s, %s)."
                   % (fname, bits))
        return None
    pair = pre_pairings[fname]
    assert pair['ASM'] == fname
    c_fun = functions[pair['C']]
    from logic import split_scalar_pairs
    (var_c_args, c_imem, glob_c_args) = split_scalar_pairs (c_fun.inputs)
    (var_c_rets, c_omem, glob_c_rets) = split_scalar_pairs (c_fun.outputs)

    num_args = len (var_c_args)
    num_rets = len (var_c_rets)
    print num_args
    print num_rets

    #assert False
    const_mem = not (c_omem)
    #print 'const_mem\n'
    #print const_mem
    #print c_omem

    cc = get_asm_calling_convention_inner (num_args, num_rets, const_mem)
    asm_cc_cache[fname] = cc
    return cc

def get_asm_calling_convention_inner (num_c_args, num_c_rets, const_mem):
    key = ('Inner', num_c_args, num_c_rets, const_mem)
    if key in asm_cc_cache:
        #assert False
        return asm_cc_cache[key]

    from logic import mk_var_list, mk_stack_sequence
    from syntax import mk_var, word32T, word64T, builtinTs

    if syntax.arch == 'armv7':
        arg_regs = mk_var_list (['r0', 'r1', 'r2', 'r3'], word32T)
        r0 = arg_regs[0]
        sp = mk_var ('r13', word32T)
        st = mk_var ('stack', builtinTs['Mem'])
        r0_input = mk_var ('ret_addr_input', word32T)
        #assert False
    elif syntax.arch == 'rv64':
        arg_regs = mk_var_list(['r10', 'r11', 'r12', 'r13', 'r14',
                                'r15', 'r16', 'r17'], word64T)

        r0 = arg_regs[0]
        r1 = arg_regs[1]
        sp = mk_var('r2', word64T)
        st = mk_var('stack', builtinTs['Mem'])
        r0_input = mk_var('r10_input', word64T)
        #assert False
    else:
        print 'Unsupported arch %s' % syntax.arch
        assert False

    mem = mk_var ('mem', builtinTs['Mem'])
    dom = mk_var ('dom', builtinTs['Dom'])
    dom_stack = mk_var ('dom_stack', builtinTs['Dom'])
    if syntax.arch == 'armv7':
        global_args = [mem, dom, st, dom_stack, sp, mk_var ('ret', word32T)]
        sregs = mk_stack_sequence (sp, 4, st, word32T, num_c_args + 1)
    elif syntax.arch == 'rv64':
        global_args = [mem, dom, st, dom_stack, sp, mk_var('ret', word64T)]
        sregs = mk_stack_sequence(sp, 8, st, word64T, num_c_args + 1)
        print global_args
        print num_c_args
        print num_c_rets
    else:
        assert False

    arg_seq = [r for r in arg_regs] + [s for (s, _) in sregs]
    if num_c_rets > 1:
        # the 'return-too-much' issue.
        # instead r0 is a save-returns-here pointer
        arg_seq.pop (0)
        #rv64_hack
        rets = mk_stack_sequence (r0_input, 8, st, word64T, num_c_rets)
        rets = [r for (r, _) in rets]
        # need to handle multiple return value case
        assert False
    else:
        rets = [r0]

    if syntax.arch == 'armv7':
        callee_saved_vars = ([mk_var (v, word32T)
                              for v in 'r4 r5 r6 r7 r8 r9 r10 r11 r13'.split ()]
                             + [dom, dom_stack])
        #assert False
    elif syntax.arch == 'rv64':
        callee_saved_vars = ([mk_var(v, word64T)
                              for v in 'r18 r19 r20 r21 r22 r23 r24 r25 r26 r27'.split()]
                             + [dom, dom_stack])
        print callee_saved_vars
        #assert False
    else:
        assert False

    if const_mem:
        callee_saved_vars += [mem]
    else:
        rets += [mem]

    rets += [st]

    #rets += [mem]
    print 'rets:'
    print const_mem
    print rets
    print st
    #assert False
    cc = {'args': arg_seq[: num_c_args] + global_args,
          'rets': rets, 'callee_saved': callee_saved_vars}

    print 'printcc:'
    print cc
    #assert None
    asm_cc_cache[key] = cc
    return cc

def get_asm_calling_convention_at_node (node):
    print 'node:'
    print node
    cc = get_asm_calling_convention (node.fname)
    print 'cc:'
    print cc
    print 'done cc'
    if not cc:
        return None


    fun = functions[node.fname]
    arg_input_map = dict (azip (fun.inputs, node.args))
    ret_output_map = dict (azip (fun.outputs,
                                 [mk_var (nm, typ) for (nm, typ) in node.rets]))
    print 'arg\n'
    print arg_input_map
    print 'ret\n'
    print ret_output_map
    print node.fname
    args = [logic.var_subst (arg, arg_input_map) for arg in cc['args']]
    rets = [logic.var_subst (ret, ret_output_map) for ret in cc['rets']]
    # these are useful because they happen to map ret r0_input back to
    # the previous value r0, rather than the useless value r0_input_ignore.
    rets_inp = [logic.var_subst (ret, arg_input_map) for ret in cc['rets']]
    saved = [logic.var_subst (v, ret_output_map)
             for v in cc['callee_saved']]
    print 'args:'
    print args
    print "rets:"
    print rets
    print "rets_inp"
    print rets_inp
    print "saved"
    print saved
    #assert None
    return {'args': args, 'rets': rets,
            'rets_inp': rets_inp, 'callee_saved': saved}

call_cache = {}

def get_asm_callable (fname):
    if fname not in pre_pairings:
        return True
    c_fun = pre_pairings[fname]['C']

    if not call_cache:
        for f in functions:
            call_cache[f] = False
        for f in functions:
            fun = functions[f]
            for n in fun.reachable_nodes (simplify = True):
                if fun.nodes[n].kind == 'Call':
                    call_cache[fun.nodes[n].fname] = True
    return call_cache[c_fun]

def get_asm_reachable_nodes (p, tag_set = None):
    if tag_set == None:
        tag_set = [tag for tag in p.tags ()
                   if is_asm_node (p, p.get_entry (tag))]
    frontier = [p.get_entry (tag) for tag in tag_set]
    nodes = set ()
    while frontier:
        n = frontier.pop ()
        if n in nodes or n not in p.nodes:
            continue
        nodes.add (n)
        node = p.nodes[n]
        if node.kind == 'Call' and not get_asm_callable (node.fname):
            continue
        node = logic.simplify_node_elementary (node)
        frontier.extend (node.get_conts ())
    return nodes

def convert_recursion_idents (idents):
    asm_idents = {}
    for f in idents:
        if f not in pre_pairings:
            continue
        f2 = pre_pairings[f]['ASM']
        assert f2 != f
        asm_idents[f2] = []
        for ident in idents[f]:
            if ident.is_op ('True'):
                asm_idents[f2].append (ident)
            elif ident.is_op ('Equals'):
                [x, y] = ident.vals
                # this is a bit hacky
                [i] = [i for (i, (nm, typ))
                       in enumerate (functions[f].inputs)
                       if x.is_var ((nm, typ))]
                cc = get_asm_calling_convention (f2)
                x = cc['args'][i]
                asm_idents[f2].append (syntax.mk_eq (x, y))
            else:
                assert not 'ident kind convertible'
    return asm_idents

def mk_pairing (pre_pair, stack_bounds):
    asm_f = pre_pair['ASM']
    sz = stack_bounds[asm_f]
    #print sz
    c_fun = functions[pre_pair['C']]

    from logic import split_scalar_pairs
    (var_c_args, c_imem, glob_c_args) = split_scalar_pairs (c_fun.inputs)
    (var_c_rets, c_omem, glob_c_rets) = split_scalar_pairs (c_fun.outputs)

    if syntax.arch == 'armv7':
        eqs = logic.mk_eqs_arm_none_eabi_gnu (var_c_args, var_c_rets,
                                              c_imem, c_omem, sz)
    elif syntax.arch == 'rv64':
        eqs = logic.mk_eqs_riscv64_unknown_linux_gnu(var_c_args, var_c_rets,
                                                     c_imem, c_omem, sz)
    else:
        assert False

    print 'eqs\n'
    for e in eqs:
        print type(e)
        for ee in e:
            print  ee

    #assert False
    return logic.Pairing (['ASM', 'C'],
                          {'ASM': asm_f, 'C': c_fun.name}, eqs)

def mk_pairings (stack_bounds):
    new_pairings = {}
    for f in pre_pairings:
        if f in new_pairings:
            continue
        pair = mk_pairing (pre_pairings[f], stack_bounds)
        for fun in pair.funs.itervalues ():
            new_pairings[fun] = [pair]
    return new_pairings

def serialise_stack_bounds (stack_bounds):
    lines = []
    for fname in stack_bounds:
        ss = ['StackBound', fname]
        stack_bounds[fname].serialise (ss)
        lines.append (' '.join (ss) + '\n')
    return lines

def deserialise_stack_bounds (lines):
    bounds = {}
    for line in lines:
        bits = line.split ()
        if not bits:
            continue
        assert bits[0] == 'StackBound'
        fname = bits[1]
        (_, bound) = syntax.parse_expr (bits, 2)
        #print 'bound: '
        #print bound
        #print 'bits: '
        #print bits
        #print bits[2]
        #assert False
        bounds[fname] = bound
    return bounds

funs_with_tag = {}

def get_functions_with_tag (tag):
    if tag in funs_with_tag:
        return funs_with_tag[tag]
    visit = set ([pre_pairings[f][tag] for f in pre_pairings
                  if tag in pre_pairings[f]])
    visit.update ([pair.funs[tag] for f in pairings
                   for pair in pairings[f] if tag in pair.funs])
    funs = set (visit)
    while visit:
        f = visit.pop ()
        funs.add (f)
        visit.update (set (functions[f].function_calls ()) - funs)
    funs_with_tag[tag] = funs
    return funs

def compute_stack_bounds (quiet = False):
    prev_tracer = target_objects.tracer[0]
    if quiet:
        target_objects.tracer[0] = lambda s, n: ()

    try:
        c_fs = get_functions_with_tag ('C')
        idents = get_recursion_identifiers (c_fs)
        asm_idents = convert_recursion_idents (idents)
        asm_fs = get_functions_with_tag ('ASM')
        printout ('Computed recursion limits.')

        bounds = compute_asm_stack_bounds (asm_idents, asm_fs)
        printout ('Computed stack bounds.')
    except Exception, e:
        if quiet:
            target_objects.tracer[0] = prev_tracer
        raise

    if quiet:
        target_objects.tracer[0] = prev_tracer
    return bounds

def read_fn_hash (fname):
    try:
        assert fname != None
        #print fname
        f = open (fname)
        s = f.readline ()
        bits = s.split ()
        if bits[0] != 'FunctionHash' or len (bits) != 2:
            return None
        return int (bits[1])
    except ValueError, e:
        return None
    except IndexError, e:
        return None
    except IOError, e:
        return None

def add_pairings(pairing_tups):
    pre_pairings.clear()
    for (asm_f, c_f) in pairing_tups:
        pair = {'ASM': asm_f, 'C': c_f}
        pre_pairings[c_f] = pair
        pre_pairings[asm_f] = pair


def mk_stack_pairings (pairing_tups, stack_bounds_fname = None,
                       quiet = True):
    """build the stack-aware calling-convention-aware logical pairings
    once a collection of function pairs have been read."""

    # simplifies interactive testing of this function
    pre_pairings.clear ()

    for (asm_f, c_f) in pairing_tups:
        pair = {'ASM': asm_f, 'C': c_f}
        assert c_f not in pre_pairings
        assert asm_f not in pre_pairings
        pre_pairings[c_f] = pair
        pre_pairings[asm_f] = pair

    fn_hash = hash (tuple (sorted ([(f, hash (functions[f]))
                                    for f in functions])))
    prev_hash = read_fn_hash (stack_bounds_fname)
    #rv64_hack to use the old stack bounds
    #if prev_hash == fn_hash:
    if prev_hash:
        f = open (stack_bounds_fname)
        f.readline ()
        stack_bounds = deserialise_stack_bounds (f)
        f.close ()
    else:
        printout ('Computing stack bounds.')
        stack_bounds = compute_stack_bounds (quiet = quiet)
        f = open (stack_bounds_fname, 'w')
        f.write ('FunctionHash %s\n' % fn_hash)
        for line in serialise_stack_bounds (stack_bounds):
            f.write(line)
        f.close ()

    problematic_synthetic ()

    return mk_pairings (stack_bounds)

def asm_stack_rep_hook (p, (nm, typ), kind, n):
    if not is_asm_node (p, n):
        return None

    if not (nm.startswith ('stack') and typ == syntax.builtinTs['Mem']):
        return None

    assert kind in ['Call', 'Init', 'Loop'], kind
    if kind == 'Init':
        return None

    tag = p.node_tags[n][0]
    (_, sp) = get_stack_sp (p, tag)

    return ('SplitMem', sp)

reg_aliases_armv7 = {'r11': ['fp'], 'r14': ['lr'], 'r13': ['sp']}
reg_aliases_rv64 = {
    'r1': ['ra'],
    'r2': ['sp'],
    'r8': ['fp'],
}

def inst_const_rets (node):
    assert "instruction'" in node.fname
    if syntax.arch == 'armv7':
        reg_aliases = reg_aliases_armv7
    elif syntax.arch == 'rv64':
        reg_aliases = reg_aliases_rv64
    else:
        print 'Unsupported arch %s' % syntax.arch
        assert False

    bits = set ([s.lower () for s in node.fname.split ('_')])
    fun = functions[node.fname]
    def is_const (nm, typ):
        if typ in [builtinTs['Mem'], builtinTs['Dom']]:
            return True
        #print typ
        #assert False
        if typ != word32T or typ != word64T:
            return False
        return not (nm in bits or [al for al in reg_aliases.get (nm, [])
                                   if al in bits])
    is_consts = [is_const (nm, typ) for (nm, typ) in fun.outputs]
    input_set = set ([v for arg in node.args
                      for v in syntax.get_expr_var_set (arg)])
    return [mk_var (nm, typ)
            for ((nm, typ), const) in azip (node.rets, is_consts)
            if const and (nm, typ) in input_set]

def node_const_rets (node):
    if "instruction'" in node.fname:
        return inst_const_rets (node)
    if node.fname in pre_pairings:
        if pre_pairings[node.fname]['ASM'] != node.fname:
            return None
        cc = get_asm_calling_convention_at_node (node)
        input_set = set ([v for arg in node.args
                          for v in syntax.get_expr_var_set (arg)])
        callee_saved_set = set (cc['callee_saved'])
        return [mk_var (nm, typ) for (nm, typ) in node.rets
                if mk_var (nm, typ) in callee_saved_set
                if (nm, typ) in input_set]
    elif preserves_sp (node.fname):
        if node.fname not in get_functions_with_tag ('ASM'):
            return None
        f_outs = functions[node.fname].outputs

        #rv64_hack
        sp_reg = 'r13'
        if syntax.arch == 'rv64':
            sp_reg = 'r2'

        print f_outs
        assert False


        return [mk_var (nm, typ)
                for ((nm, typ), (nm2, _)) in azip (node.rets, f_outs)
                if nm2 == sp_reg]
    else:
        return None

def const_ret_hook (node, nm, typ):
    consts = node_const_rets (node)
    return consts and mk_var (nm, typ) in consts

def get_const_rets (p, node_set = None):
    if node_set == None:
        node_set = p.nodes
    const_rets = {}
    for n in node_set:
        if p.nodes[n].kind != 'Call':
            continue
        consts = node_const_rets (node)
        const_rets[n] = [(v.name, v.typ) for v in consts]
    return const_rets

def problematic_synthetic ():
    synth = [s for s in target_objects.symbols
             if '.clone.' in s or '.part.' in s or '.constprop.' in s]
    synth = ['_'.join (s.split ('.')) for s in synth]
    if not synth:
        return
    printout ('Synthetic symbols: %s' % synth)
    synth_calls = set ([f for f in synth
                        if f in functions
                        if functions[f].function_calls ()])
    printout ('Synthetic symbols which make function calls: %s'
              % synth_calls)
    if not synth_calls:
        return
    if syntax.arch == 'armv7':
        synth_stack = set ([f for f in synth_calls
                            if [node for node in functions[f].nodes.itervalues ()
                                if node.kind == 'Basic'
                                if ('r13', word32T) in node.get_lvals ()]])
    elif syntax.arch == 'rv64':
        synth_stack = set([f for f in synth_calls
                           if [node for node in functions[f].nodes.itervalues()
                               if node.kind == 'Basic'
                               if ('r2', word64T) in node.get_lvals()]])
    else:
        assert False

    printout ('Synthetic symbols which call and move sp: %s'
              % synth_stack)
    synth_problems = set ([f for f in synth_stack
                           if [f2 for f2 in functions
                               if f in functions[f2].function_calls ()
                               if len (set (functions[f2].function_calls ())) > 1]
                           ])
    printout ('Problematic synthetics: %s' % synth_problems)
    return synth_problems

def add_hooks ():
    k = 'stack_logic'
    add = target_objects.add_hook
    add ('problem_var_rep', k, asm_stack_rep_hook)
    add ('loop_var_analysis', k, loop_var_analysis)
    add ('rep_unsafe_const_ret', k, const_ret_hook)

add_hooks ()

