#
# Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

import syntax
from syntax import word64T, word32T, word8T, boolT, builtinTs, Expr, Node
from syntax import true_term, false_term, mk_num
from syntax import foldr1

(mk_var, mk_plus, mk_uminus, mk_minus, mk_times, mk_modulus, mk_bwand, mk_eq,
 mk_less_eq, mk_less, mk_implies, mk_and, mk_or, mk_not, mk_word64, mk_word32, mk_word8,
 mk_word32_maybe, mk_cast, mk_memacc, mk_memupd, mk_arr_index, mk_arroffs,
 mk_if, mk_meta_typ, mk_pvalid) = syntax.mks

from syntax import structs
from target_objects import trace, printout

def is_int (n):
    return hasattr (n, '__int__')

def mk_eq_with_cast (a, c):
    return mk_eq (a, mk_cast (c, a.typ))

def mk_rodata (m):
    assert m.typ == builtinTs['Mem']
    return Expr ('Op', boolT, name = 'ROData', vals = [m])

def cast_pair (pair, mk_cast=mk_cast):
    (a, a_addr), (c, c_addr) = pair
    if a.typ != c.typ and c.typ == boolT:
        assert False
        c = mk_if (c, mk_word32 (1), mk_word32 (0))
    return ((a, a_addr), (mk_cast(c, a.typ), c_addr))

# The RISC-V calling convention requires some special handling for
# 32-bit values stored in 64-bit registers. These are presumed to
# be stored in sign-extended form, even if the C type is unsigned.
def mk_cast_rv64(x, typ):
    signed = x.typ.num == 32 and typ.num == 64
    return mk_cast(x, typ, signed=signed)

def cast_pair_rv64(pair):
    return cast_pair(pair, mk_cast_rv64)

def split_scalar_globals (vs):
    for i in range (len (vs)):
        if vs[i].typ.kind != 'Word' and vs[i].typ != boolT:
            break
    else:
        i = len (vs)
    scalars = vs[:i]
    global_vars = vs[i:]

    for v in global_vars:
        if v.typ not in [builtinTs['Mem'], builtinTs['Dom'],
                         builtinTs['HTD'], builtinTs['PMS'],
                         syntax.arch.ghost_assertion_type]:
            assert not "scalar_global split expected", vs

    memT = builtinTs['Mem']
    mems = [v for v in global_vars if v.typ == memT]
    others = [v for v in global_vars if v.typ != memT]
    return (scalars, mems, others)

def mk_vars (tups):
    return [mk_var (nm, typ) for (nm, typ) in tups]

def split_scalar_pairs (var_pairs):
    return split_scalar_globals (mk_vars (var_pairs))

def azip (xs, ys):
    assert len (xs) == len (ys), (xs, ys)
    return zip (xs, ys)

def mk_mem_eqs (a_imem, c_imem, a_omem, c_omem, tags):
    [a_imem] = a_imem
    a_tag, c_tag = tags
    (c_in, c_out) = (c_tag + '_IN', c_tag + '_OUT')
    (a_in, a_out) = (a_tag + '_IN', a_tag + '_OUT')
    if c_imem:
        [c_imem] = c_imem
        ieqs = [((a_imem, a_in), (c_imem, c_in)),
                ((mk_rodata (c_imem), c_in), (true_term, c_in))]
    else:
        ieqs = [((mk_rodata (a_imem), a_in), (true_term, c_in))]
    if c_omem:
        [a_m] = a_omem
        [c_omem] = c_omem
        oeqs = [((a_m, a_out), (c_omem, c_out)),
                ((mk_rodata (c_omem), c_out), (true_term, c_out))]
    else:
        oeqs = [((a_m, a_out), (a_imem, a_in)) for a_m in a_omem]

    return (ieqs, oeqs)

def mk_fun_eqs (as_f, c_f, prunes = None):
    assert not 'used'

    (var_a_args, a_imem, glob_a_args) = split_scalar_pairs (as_f.inputs)
    (var_c_args, c_imem, glob_c_args) = split_scalar_pairs (c_f.inputs)
    (var_a_rets, a_omem, glob_a_rets) = split_scalar_pairs (as_f.outputs)
    (var_c_rets, c_omem, glob_c_rets) = split_scalar_pairs (c_f.outputs)

    (mem_ieqs, mem_oeqs) = mk_mem_eqs (a_imem, c_imem, a_omem, c_omem, ['ASM', 'C'])

    if not prunes:
        prunes = (var_a_args, var_a_args)
    assert len (prunes[0]) == len (var_c_args), (params, var_a_args,
                                                 var_c_args, prunes)
    a_map = dict (azip (prunes[1], var_a_args))
    ivar_pairs = [((a_map[p], 'ASM_IN'), (c, 'C_IN')) for (p, c)
                  in azip (prunes[0], var_c_args) if p in a_map]

    ovar_pairs = [((a_ret, 'ASM_OUT'), (c_ret, 'C_OUT')) for (a_ret, c_ret)
                  in azip (var_a_rets, var_c_rets)]
    return (map (cast_pair, mem_ieqs + ivar_pairs),
            map (cast_pair, mem_oeqs + ovar_pairs))

def mk_var_list (vs, typ):
    return [syntax.mk_var (v, typ) for v in vs]

def mk_offs_sequence (init, offs, n, do_reverse = False):
    r = range (n)
    if do_reverse:
        r.reverse ()
    def mk_offs (n):
        return Expr ('Num', init.typ, val = offs * n)
    return [mk_plus (init, mk_offs (m)) for m in r]

def mk_stack_sequence (sp, offs, stack, typ, n, do_reverse = False):
    return [(mk_memacc (stack, addr, typ), addr)
            for addr in mk_offs_sequence (sp, offs, n, do_reverse)]

def mk_aligned (w, n):
    assert w.typ.kind == 'Word'
    mask = Expr ('Num', w.typ, val = ((1 << n) - 1))
    return mk_eq (mk_bwand (w, mask), mk_num (0, w.typ))

def mk_eqs_arm_none_eabi_gnu (var_c_args, var_c_rets, c_imem, c_omem,
                              min_stack_size):
    arg_regs = mk_var_list (['r0', 'r1', 'r2', 'r3'], word32T)
    r0 = arg_regs[0]
    sp = mk_var ('r13', word32T)
    st = mk_var ('stack', builtinTs['Mem'])
    r0_input = mk_var ('ret_addr_input', word32T)
    sregs = mk_stack_sequence (sp, 4, st, word32T, len (var_c_args) + 1)

    ret = mk_var ('ret', word32T)
    preconds = [mk_aligned (sp, 2),
                mk_eq (ret, mk_var ('r14', word32T)),
                mk_aligned (ret, 2),
                mk_eq (r0_input, r0),
                mk_less_eq (min_stack_size, sp)]

    post_eqs = [(x, x) for x in mk_var_list (['r4', 'r5', 'r6', 'r7', 'r8',
                                              'r9', 'r10', 'r11', 'r13'], word32T)]

    arg_seq = [(r, None) for r in arg_regs] + sregs
    if len (var_c_rets) > 1:
        # the 'return-too-much' issue.
        # instead r0 is a save-returns-here pointer
        arg_seq.pop (0)
        preconds += [mk_aligned (r0, 2), mk_less_eq (sp, r0)]
        save_seq = mk_stack_sequence (r0_input, 4, st, word32T,
                                      len (var_c_rets))
        save_addrs = [addr for (_, addr) in save_seq]
        post_eqs += [(r0_input, r0_input)]
        out_eqs = zip (var_c_rets, [x for (x, _) in save_seq])
        out_eqs = [(c, mk_cast (a, c.typ)) for (c, a) in out_eqs]
        init_save_seq = mk_stack_sequence (r0, 4, st, word32T,
                                           len (var_c_rets))
        (_, last_arg_addr) = arg_seq[len (var_c_args) - 1]
        preconds += [mk_less_eq (sp, addr)
                     for (_, addr) in init_save_seq[-1:]]
        if last_arg_addr:
            preconds += [mk_less (last_arg_addr, addr)
                         for (_, addr) in init_save_seq[:1]]
    else:
        out_eqs = zip (var_c_rets, [r0])
        save_addrs = []
    arg_seq_addrs = [addr for ((_, addr), _) in zip (arg_seq, var_c_args)
                     if addr != None]
    swrap = mk_stack_wrapper (sp, st, arg_seq_addrs)
    swrap2 = mk_stack_wrapper (sp, st, save_addrs)
    post_eqs += [(swrap, swrap2)]

    mem = mk_var ('mem', builtinTs['Mem'])
    (mem_ieqs, mem_oeqs) = mk_mem_eqs ([mem], c_imem, [mem], c_omem,
                                       ['ASM', 'C'])

    addr = None
    arg_eqs = [cast_pair (((a_x, 'ASM_IN'), (c_x, 'C_IN')))
               for (c_x, (a_x, addr)) in zip (var_c_args, arg_seq)]
    if addr:
        preconds += [mk_less_eq (sp, addr)]
    ret_eqs = [cast_pair (((a_x, 'ASM_OUT'), (c_x, 'C_OUT')))
               for (c_x, a_x) in out_eqs]
    preconds = [((a_x, 'ASM_IN'), (true_term, 'ASM_IN')) for a_x in preconds]
    asm_invs = [((vin, 'ASM_IN'), (vout, 'ASM_OUT')) for (vin, vout) in post_eqs]

    return (arg_eqs + mem_ieqs + preconds,
            ret_eqs + mem_oeqs + asm_invs)


def mk_eqs_riscv64_unknown_linux_gnu(var_c_args, var_c_rets, c_imem, c_omem, min_stack_size):
    syntax.context_trace()

    arg_regs = mk_var_list(['r10', 'r11', 'r12', 'r13', 'r14', 'r15', 'r16', 'r17'], word64T)

    r10 = arg_regs[0]
    r11 = arg_regs[1]

    sp = mk_var('r2', word64T)
    st = mk_var('stack', builtinTs['Mem'])
    r10_input = mk_var('ret_addr_input', word64T)
    sregs = mk_stack_sequence(sp, 8, st, word64T, len(var_c_args) + 1)
    ret = mk_var('ret', word64T)

    preconds = [
        #for RV64, assume the stack is 16-byte aligned
        mk_aligned(sp, 4),
        mk_eq(ret, mk_var('r1', word64T)),

        # precondition; ret address is 2-byte aligned for
        # compress insturction or 4-byte aligned for
        # normal instruction
        # note that the assembly decompiler addes a check to
        # assert that the return address in r1 is 2-byte aligend.
        mk_aligned(ret, 1),
        mk_eq(r10_input, r10),
        mk_less_eq(min_stack_size, sp)
    ]

    post_eqs = [
        (x, x) for x in mk_var_list(
            ['r2', 'r3', 'r4', 'r8', 'r9', 'r18', 'r19', 'r20', 'r21',
             'r22', 'r23', 'r24', 'r25', 'r26', 'r27'],
            word64T)
    ]

    arg_seq = [(r, None) for r in arg_regs] + sregs

    if len (var_c_rets) > 2:
        # the 'return-too-much' issue.
        # instead r0 is a save-returns-here pointer
        arg_seq.pop (0)
        preconds += [mk_aligned (r10, 3), mk_less_eq (sp, r10)]
        save_seq = mk_stack_sequence (r10_input, 8, st, word64T,
                                      len (var_c_rets))
        save_addrs = [addr for (_, addr) in save_seq]
        post_eqs += [(r10_input, r10_input)]
        out_eqs = zip (var_c_rets, [x for (x, _) in save_seq])
        out_eqs = [(c, mk_cast_rv64(a, c.typ)) for (c, a) in out_eqs]
        init_save_seq = mk_stack_sequence (r10, 8, st, word64T,
                                           len(var_c_rets))
        (_, last_arg_addr) = arg_seq[len (var_c_args) - 1]
        preconds += [mk_less_eq (sp, addr)
                     for (_, addr) in init_save_seq[-1:]]
        if last_arg_addr:
            preconds += [mk_less (last_arg_addr, addr)
                         for (_, addr) in init_save_seq[:1]]

    elif len(var_c_rets) == 2:
        out_eqs = zip(var_c_rets, [r10, r11])
        save_addrs = []
    else:
        out_eqs = zip (var_c_rets, [r10])
        save_addrs = []

    arg_seq_addrs = [addr for ((_, addr), _) in zip (arg_seq, var_c_args)
                     if addr != None]
    swrap = mk_stack_wrapper (sp, st, arg_seq_addrs)
    swrap2 = mk_stack_wrapper (sp, st, save_addrs)

    post_eqs += [(swrap, swrap2)]

    mem = mk_var ('mem', builtinTs['Mem'])
    (mem_ieqs, mem_oeqs) = mk_mem_eqs ([mem], c_imem, [mem], c_omem,
                                       ['ASM', 'C'])

    addr = None
    arg_eqs = [cast_pair_rv64(((a_x, 'ASM_IN'), (c_x, 'C_IN')))
               for (c_x, (a_x, addr)) in zip (var_c_args, arg_seq)]

    if addr:
        preconds += [mk_less_eq (sp, addr)]

    ret_eqs = [cast_pair_rv64(((a_x, 'ASM_OUT'), (c_x, 'C_OUT')))
               for (c_x, a_x) in out_eqs]

    preconds = [((a_x, 'ASM_IN'), (true_term, 'ASM_IN')) for a_x in preconds]
    asm_invs = [((vin, 'ASM_IN'), (vout, 'ASM_OUT')) for (vin, vout) in post_eqs]

    return (arg_eqs + mem_ieqs + preconds, ret_eqs + mem_oeqs + asm_invs)

known_CPUs = {
    'arm-none-eabi-gnu': mk_eqs_arm_none_eabi_gnu,
    'riscv64-unknown-linux-gnu': mk_eqs_riscv64_unknown_linux_gnu,
}

def mk_fun_eqs_CPU (cpu_f, c_f, cpu_name, funcall_depth = 1):
    assert not 'used'
    cpu = known_CPUs[cpu_name]
    (var_c_args, c_imem, glob_c_args) = split_scalar_pairs (c_f.inputs)
    (var_c_rets, c_omem, glob_c_rets) = split_scalar_pairs (c_f.outputs)

    return cpu (var_c_args, var_c_rets, c_imem, c_omem,
                (funcall_depth * 256) + 256)

class Pairing:
    def __init__ (self, tags, funs, eqs, notes = None):
        [l_tag, r_tag] = tags
        self.tags = tags
        assert set (funs) == set (tags)
        self.funs = funs
        self.eqs = eqs

        self.l_f = funs[l_tag]
        self.r_f = funs[r_tag]
        self.name = 'Pairing (%s (%s) <= %s (%s))' % (self.l_f,
                                                      l_tag, self.r_f, r_tag)

        self.notes = {}
        if notes != None:
            self.notes.update (notes)

    def __str__ (self):
        return self.name

    def __hash__ (self):
        return hash (self.name)

    def __eq__ (self, other):
        return self.name == other.name and self.eqs == other.eqs

    def __ne__ (self, other):
        return not other or not self == other

def mk_pairing (functions, c_f, as_f, prunes = None, cpu = None):
    fs = (functions[as_f], functions[c_f])
    if cpu:
        eqs = mk_fun_eqs_CPU (fs[0], fs[1], cpu,
                              funcall_depth = funcall_depth (functions, c_f))
    else:
        eqs = mk_fun_eqs (fs[0], fs[1], prunes = prunes)
    return Pairing (['ASM', 'C'], {'C': c_f, 'ASM': as_f}, eqs)

def inst_eqs_pattern (pattern, params):
    (pat_params, inp_eqs, out_eqs) = pattern
    substs = [((x.name, x.typ), y)
              for (pat_vs, vs) in azip (pat_params, params)
              for (x, y) in azip (pat_vs, vs)]
    substs = dict (substs)
    subst = lambda x: var_subst (x, substs)
    return ([(subst (x), subst (y)) for (x, y) in inp_eqs],
            [(subst (x), subst (y)) for (x, y) in out_eqs])

def inst_eqs_pattern_tuples (pattern, params):
    return inst_eqs_pattern (pattern, map (mk_vars, params))

def inst_eqs_pattern_exprs (pattern, params):
    (inp_eqs, out_eqs) = inst_eqs_pattern (pattern, params)
    return (foldr1 (mk_and, [mk_eq (a, c) for (a, c) in inp_eqs]),
            foldr1 (mk_and, [mk_eq (a, c) for (a, c) in out_eqs]))

def var_match (var_exp, conc_exp, assigns):
    if var_exp.typ != conc_exp.typ:
        return False
    if var_exp.kind == 'Var':
        key = (var_exp.name, var_exp.typ)
        if key in assigns:
            return conc_exp == assigns[key]
        else:
            assigns[key] = conc_exp
            return True
    elif var_exp.kind == 'Op':
        if conc_exp.kind != 'Op' or var_exp.name != conc_exp.name:
            return False
        return all ([var_match (a, b, assigns)
                     for (a, b) in azip (var_exp.vals, conc_exp.vals)])
    else:
        return False

def var_subst (var_exp, assigns, must_subst = True):

    # hack for void func(void)
    must_subst = False
    def substor (var_exp):
        if var_exp.kind == 'Var':
            k = (var_exp.name, var_exp.typ)
            if must_subst or k in assigns:
                return assigns[k]
            else:
                return None
        else:
            return None
    return syntax.do_subst (var_exp, substor)

def recursive_term_subst (eqs, expr):
    if expr in eqs:
        return eqs[expr]
    if expr.kind == 'Op':
        vals = [recursive_term_subst (eqs, x) for x in expr.vals]
        return syntax.adjust_op_vals (expr, vals)
    return expr

def mk_accum_rewrites (typ):
    x = mk_var ('x', typ)
    y = mk_var ('y', typ)
    z = mk_var ('z', typ)
    i = mk_var ('i', typ)
    return [(x, i, mk_plus (x, y), mk_plus (x, mk_times (i, y)),
             y),
            (x, i, mk_plus (y, x), mk_plus (x, mk_times (i, y)),
             y),
            (x, i, mk_minus (x, y), mk_minus (x, mk_times (i, y)),
             mk_uminus (y)),
            (x, i, mk_plus (mk_plus (x, y), z),
             mk_plus (x, mk_times (i, mk_plus (y, z))),
             mk_plus (y, z)),
            (x, i, mk_plus (mk_plus (y, x), z),
             mk_plus (x, mk_times (i, mk_plus (y, z))),
             mk_plus (y, z)),
            (x, i, mk_plus (y, mk_plus (x, z)),
             mk_plus (x, mk_times (i, mk_plus (y, z))),
             mk_plus (y, z)),
            (x, i, mk_plus (y, mk_plus (z, x)),
             mk_plus (x, mk_times (i, mk_plus (y, z))),
             mk_plus (y, z)),
            (x, i, mk_minus (mk_minus (x, y), z),
             mk_minus (x, mk_times (i, mk_plus (y, z))),
             mk_plus (y, z)),
            ]

def mk_all_accum_rewrites ():
    return [rew for typ in [word8T, word32T, syntax.word16T,
                            syntax.word64T]
            for rew in mk_accum_rewrites (typ)]

accum_rewrites = mk_all_accum_rewrites ()

def default_val (typ):
    if typ.kind == 'Word':
        return Expr ('Num', typ, val = 0)
    elif typ == boolT:
        return false_term
    else:
        assert not 'default value for type %s created', typ

trace_accumulators = []

def accumulator_closed_form (expr, (nm, typ), add_mask = None):
    expr = toplevel_split_out_cast (expr)
    n = get_bwand_mask (expr)
    if n and not add_mask:
        return accumulator_closed_form (expr.vals[0], (nm, typ),
                                        add_mask = n)

    for (x, i, pattern, rewrite, offset) in accum_rewrites:
        var = mk_var (nm, typ)
        ass = {(x.name, x.typ): var}
        m = var_match (pattern, expr, ass)
        if m:
            x2_def = default_val (typ)
            i2_def = default_val (word32T)
            def do_rewrite (x2 = x2_def, i2 = i2_def):
                ass[(x.name, x.typ)] = x2
                ass[(i.name, i.typ)] = i2
                vs = var_subst (rewrite, ass)
                if add_mask:
                    vs = mk_bwand_mask (vs, add_mask)
                return vs
            offs = var_subst (offset, ass)
            return (do_rewrite, offs)
    if trace_accumulators:
        trace ('no accumulator %s' % ((expr, nm, typ), ))
    return (None, None)

def split_out_cast (expr, target_typ, bits):
    """given a word-type expression expr (of any word length),
    compute a simplified expression expr' of the target type, which will
    have the property that expr' && mask bits = cast expr,
    where && is bitwise-and (BWAnd), mask n is the bitpattern set at the
    bottom n bits, e.g. (1 << n) - 1, and cast is WordCast."""
    if expr.is_op (['WordCast', 'WordCastSigned']):
        [x] = expr.vals
        if x.typ.num >= bits and expr.typ.num >= bits:
            return split_out_cast (x, target_typ, bits)
        else:
            return mk_cast (expr, target_typ)
    elif expr.is_op ('BWAnd'):
        [x, y] = expr.vals
        if y.kind == 'Num':
            val = y.val
        else:
            val = 0
        full_mask = (1 << bits) - 1
        if val & full_mask == full_mask:
            return split_out_cast (x, target_typ, bits)
        else:
            return mk_cast (expr, target_typ)
    elif expr.is_op (['Plus', 'Minus']):
        # rounding issues will appear if this arithmetic is done
        # at a smaller number of bits than we'll eventually report
        if expr.typ.num >= bits:
            vals = [split_out_cast (x, target_typ, bits)
                    for x in expr.vals]
            if expr.is_op ('Plus'):
                return mk_plus (vals[0], vals[1])
            else:
                return mk_minus (vals[0], vals[1])
        else:
            return mk_cast (expr, target_typ)
    else:
        return mk_cast (expr, target_typ)

def toplevel_split_out_cast (expr):
    bits = None
    if expr.is_op (['WordCast', 'WordCastSigned']):
        bits = min ([expr.typ.num, expr.vals[0].typ.num])
    elif expr.is_op ('BWAnd'):
        bits = get_bwand_mask (expr)

    if bits:
        expr = split_out_cast (expr, expr.typ, bits)
        return mk_bwand_mask (expr, bits)
    else:
        return expr

two_powers = {}

def get_bwand_mask (expr):
    """recognise (x && mask) opers, where mask = ((1 << n) - 1)
    for some n"""
    if not expr.is_op ('BWAnd'):
        return
    [x, y] = expr.vals
    if not y.kind == 'Num':
        return
    val = y.val & ((1 << (y.typ.num)) - 1)
    if not two_powers:
        for i in range (129):
            two_powers[1 << i] = i
    return two_powers.get (val + 1)

def mk_bwand_mask (expr, n):
    return mk_bwand (expr, mk_num (((1 << n) - 1), expr.typ))

def end_addr (p, typ):
    if typ[0] == 'Array':
        (_, typ, n) = typ
        sz = mk_times (syntax.arch.mk_word(typ.size ()), n)
    else:
        assert typ[0] == 'Type', typ
        (_, typ) = typ
        sz = syntax.arch.mk_word(typ.size ())
    return mk_plus (p, mk_minus (sz, syntax.arch.mk_word(1)))

def pvalid_assertion1 ((typ, k, p, pv), (typ2, k2, p2, pv2)):
    """first pointer validity assertion: incompatibility.
    pvalid1 & pvalid2 --> non-overlapping OR somehow-contained.
    typ/typ2 is ('Type', syntax.Type) or ('Array', Type, Expr) for
    dynamically sized arrays.
    """
    offs1 = mk_minus (p, p2)
    cond1 = get_styp_condition (offs1, typ, typ2)
    offs2 = mk_minus (p2, p)
    cond2 = get_styp_condition (offs2, typ2, typ)

    out1 = mk_less (end_addr (p, typ), p2)
    out2 = mk_less (end_addr (p2, typ2), p)
    return mk_implies (mk_and (pv, pv2), foldr1 (mk_or,
                                                 [cond1, cond2, out1, out2]))

def pvalid_assertion2 ((typ, k, p, pv), (typ2, k2, p2, pv2)):
    """second pointer validity assertion: implication.
    pvalid1 & strictly-contained --> pvalid2
    """
    if typ[0] == 'Array' and typ2[0] == 'Array':
        # this is such a vague notion it's not worth it
        return true_term
    offs1 = mk_minus (p, p2)
    cond1 = get_styp_condition (offs1, typ, typ2)
    imp1 = mk_implies (mk_and (cond1, pv2), pv)
    offs2 = mk_minus (p2, p)
    cond2 = get_styp_condition (offs2, typ2, typ)
    imp2 = mk_implies (mk_and (cond2, pv), pv2)
    return mk_and (imp1, imp2)

def sym_distinct_assertion ((typ, p, pv), (start, end)):
    out1 = mk_less (mk_plus (p, syntax.arch.mk_word(typ.size () - 1)), syntax.arch.mk_word(start))
    out2 = mk_less (syntax.arch.mk_word(end), p)
    return mk_implies (pv, mk_or (out1, out2))

def norm_array_type (t):
    if t[0] == 'Type' and t[1].kind == 'Array':
        (_, atyp) = t
        return ('Array', atyp.el_typ_symb, syntax.arch.mk_word(atyp.num), 'Strong')
    elif t[0] == 'Array' and len (t) == 3:
        (_, typ, l) = t
        # these derive from PArrayValid assertions. we know the array is
        # at least this long, but it might be longer.
        return ('Array', typ, l, 'Weak')
    else:
        return t

stored_styp_conditions = {}

def get_styp_condition (offs, inner_typ, outer_typ):
    r = get_styp_condition_inner1 (inner_typ, outer_typ)
    if not r:
        return false_term
    else:
        return r (offs)

def get_styp_condition_inner1 (inner_typ, outer_typ):
    inner_typ = norm_array_type (inner_typ)
    outer_typ = norm_array_type (outer_typ)
    k = (inner_typ, outer_typ)
    if k in stored_styp_conditions:
        return stored_styp_conditions[k]
    r = get_styp_condition_inner2 (inner_typ, outer_typ)
    stored_styp_conditions[k] = r
    return r

def array_typ_size ((kind, el_typ, num, _)):
    el_size = syntax.arch.mk_word(el_typ.size ())
    return mk_times (num, el_size)

def get_styp_condition_inner2 (inner_typ, outer_typ):
    if inner_typ[0] == 'Array' and outer_typ[0] == 'Array':
        (_, ityp, inum, _) = inner_typ
        (_, otyp, onum, outer_bound) = outer_typ
        # array fits in another array if the starting element is
        # a sub-element, and if the size of the left array plus
        # the offset fits in the right array
        cond = get_styp_condition_inner1 (('Type', ityp), outer_typ)
        isize = array_typ_size (inner_typ)
        osize = array_typ_size (outer_typ)
        if outer_bound == 'Strong' and cond:
            return lambda offs: mk_and (cond (offs),
                                        mk_less_eq (mk_plus (isize, offs), osize))
        else:
            return cond
    elif inner_typ == outer_typ:
        return lambda offs: mk_eq (offs, syntax.arch.mk_word(0))
    elif outer_typ[0] == 'Type' and outer_typ[1].kind == 'Struct':
        conds = [(get_styp_condition_inner1 (inner_typ,
                                             ('Type', sf_typ)), syntax.arch.mk_word(offs2))
                 for (_, offs2, sf_typ)
                 in structs[outer_typ[1].name].fields.itervalues()]
        conds = [cond for cond in conds if cond[0]]
        if conds:
            return lambda offs: foldr1 (mk_or,
                                        [c (mk_minus (offs, offs2))
                                         for (c, offs2) in conds])
        else:
            return None
    elif outer_typ[0] == 'Array':
        (_, el_typ, n, bound) = outer_typ
        cond = get_styp_condition_inner1 (inner_typ, ('Type', el_typ))
        el_size = syntax.arch.mk_word(el_typ.size ())
        size = mk_times (n, el_size)
        if bound == 'Strong' and cond:
            return lambda offs: mk_and (mk_less (offs, size),
                                        cond (mk_modulus (offs, el_size)))
        elif cond:
            return lambda offs: cond (mk_modulus (offs, el_size))
        else:
            return None
    else:
        return None

def all_vars_have_prop (expr, prop):
    class Failed (Exception):
        pass
    def visit (expr):
        if expr.kind != 'Var':
            return
        v2 = (expr.name, expr.typ)
        if not prop (v2):
            raise Failed ()
    try:
        expr.visit (visit)
        return True
    except Failed:
        return False

def all_vars_in_set (expr, var_set):
    return all_vars_have_prop (expr, lambda v: v in var_set)

def var_not_in_expr (var, expr):
    v2 = (var.name, var.typ)
    return all_vars_have_prop (expr, lambda v: v != v2)

def mk_array_size_ineq (typ, num, p):
    align = typ.align ()
    size = mk_times (syntax.arch.mk_word(typ.size ()), num)
    size_lim = ((2 ** syntax.arch.word_size) - syntax.arch.ptr_size) / typ.size()
    return mk_less_eq (num, syntax.arch.mk_word(size_lim))

def mk_align_valid_ineq (typ, p):
    if typ[0] == 'Type':
        (_, typ) = typ
        align = typ.align ()
        size = syntax.arch.mk_word(typ.size ())
        size_req = []
    else:
        assert typ[0] == 'Array', typ
        (kind, typ, num) = typ
        align = typ.align ()
        size = mk_times (syntax.arch.mk_word(typ.size ()), num)
        size_req = [mk_array_size_ineq (typ, num, p)]
    assert align in [1, 4, 8]
    w0 = syntax.arch.mk_word(0)
    if align > 1:
        align_req = [mk_eq (mk_bwand (p, syntax.arch.mk_word(align - 1)), w0)]
    else:
        align_req = []
    return foldr1 (mk_and, align_req + size_req + [mk_not (mk_eq (p, w0)),
                                                   mk_implies (mk_less (w0, size),
                                                               mk_less_eq (p, mk_uminus (size)))])

# generic operations on function/problem graphs
def dict_list (xys, keys = None):
    """dict_list ([(1, 2), (1, 3), (2, 4)]) = {1: [2, 3], 2: [4]}"""
    d = {}
    for (x, y) in xys:
        d.setdefault (x, [])
        d[x].append (y)
    if keys:
        for x in keys:
            d.setdefault (x, [])
    return d

def compute_preds (nodes):
    preds = dict_list ([(c, n) for n in nodes
                        for c in nodes[n].get_conts ()],
                       keys = nodes)
    for n in ['Ret', 'Err']:
        preds.setdefault (n, [])
    preds = dict ([(n, sorted (set (ps)))
                   for (n, ps) in preds.iteritems ()])
    return preds

def simplify_node_elementary(node):
    if node.kind == 'Cond' and node.cond == true_term:
        return Node ('Basic', node.left, [])
    elif node.kind == 'Cond' and node.cond == false_term:
        return Node ('Basic', node.right, [])
    elif node.kind == 'Cond' and node.left == node.right:
        return Node ('Basic', node.left, [])
    else:
        return node

def compute_var_flows (nodes, outputs, preds, override_lvals_rvals = {}):
    # compute a graph of reverse var flows to pass to tarjan's algorithm
    graph = {}
    entries = ['Ret']
    for (n, node) in nodes.iteritems ():
        if node.kind == 'Basic':
            for (lv, rv) in node.upds:
                graph[(n, 'Post', lv)] = [(n, 'Pre', v)
                                          for v in syntax.get_expr_var_set (rv)]
        elif node.is_noop ():
            pass
        else:
            if n in override_lvals_rvals:
                (lvals, rvals) = override_lvals_rvals[n]
            else:
                rvals = syntax.get_node_rvals (node)
                rvals = set (rvals.iteritems ())
                lvals = set (node.get_lvals ())
            if node.kind != 'Basic':
                lvals = list (lvals) + ['PC']
                entries.append ((n, 'Post', 'PC'))
            for lv in lvals:
                graph[(n, 'Post', lv)] = [(n, 'Pre', rv)
                                          for rv in rvals]
    graph['Ret'] = [(n, 'Post', v)
                    for n in preds['Ret'] for v in outputs (n)]
    vs = set ([v for k in graph for (_, _, v) in graph[k]])
    for v in vs:
        for n in nodes:
            graph.setdefault ((n, 'Post', v), [(n, 'Pre', v)])
            graph[(n, 'Pre', v)] = [(n2, 'Post', v)
                                    for n2 in preds[n]]

    comps = tarjan (graph, entries)
    return (graph, comps)

def mk_not_red (v):
    if v.is_op ('Not'):
        [v] = v.vals
        return v
    else:
        return syntax.mk_not (v)

def cont_with_conds (nodes, n, conds):
    while True:
        if n not in nodes or nodes[n].kind != 'Cond':
            return n
        cond = nodes[n].cond
        if cond in conds:
            n = nodes[n].left
        elif mk_not_red (cond) in conds:
            n = nodes[n].right
        else:
            return n

def contextual_conds (nodes, preds):
    """computes a collection of conditions that can be assumed true
    at any point in the node graph."""
    pre_conds = {}
    arc_conds = {}
    visit = [n for n in nodes if not (preds[n])]
    while visit:
        n = visit.pop ()
        if n not in nodes:
            continue
        in_arc_conds = [arc_conds.get ((pre, n), set ())
                        for pre in preds[n]]
        if not in_arc_conds:
            conds = set ()
        else:
            conds = set.intersection (* in_arc_conds)
        if pre_conds.get (n) == conds:
            continue
        pre_conds[n] = conds
        if n not in nodes:
            continue
        if nodes[n].kind == 'Cond' and nodes[n].left == nodes[n].right:
            c_conds = [conds, conds]
        elif nodes[n].kind == 'Cond':
            c_conds = [nodes[n].cond, mk_not_red (nodes[n].cond)]
            c_conds = [set.union (set ([c]), conds)
                       for c in c_conds]
        else:
            upds = set (nodes[n].get_lvals ())
            c_conds = [set ([c for c in conds if
                             not set.intersection (upds,
                                                   syntax.get_expr_var_set (c))])]
        for (cont, conds) in zip (nodes[n].get_conts (), c_conds):
            arc_conds[(n, cont)] = conds
            visit.append (cont)
    return (arc_conds, pre_conds)

def contextual_cond_simps (nodes, preds):
    """a common pattern in architectures with conditional operations is
    a sequence of instructions with the same condition.
    we can usually then reduce to a single contional block.
      b   e    =>    b-e
     / \ / \   =>   /   \
    a-c-d-f-g  =>  a-c-f-g
    this is sometimes important if b calculates a register that e uses
    since variable dependency analysis will see this register escape via
    the impossible path a-c-d-e
    """
    (arc_conds, pre_conds) = contextual_conds (nodes, preds)
    nodes = dict (nodes)
    for n in nodes:
        if nodes[n].kind == 'Cond':
            continue
        cont = nodes[n].cont
        conds = arc_conds[(n, cont)]
        cont2 = cont_with_conds (nodes, cont, conds)
        if cont2 != cont:
            nodes[n] = syntax.copy_rename (nodes[n],
                                           ({}, {cont: cont2}))
    return nodes

def minimal_loop_node_set (p):
    """discover a minimal set of loop addresses, excluding some operations
    using conditional instructions which are syntactically within the
    loop but semantically must always be followed by an immediate loop
    exit.

    amounts to rerunning loop detection after contextual_cond_simps."""

    loop_ns = set (p.loop_data)
    really_in_loop = {}
    nodes = contextual_cond_simps (p.nodes, p.preds)
    def is_really_in_loop (n):
        if n in really_in_loop:
            return really_in_loop[n]
        ns = []
        r = None
        while r == None:
            ns.append (n)
            if n not in loop_ns:
                r = False
            elif n in p.splittable_points (n):
                r = True
            else:
                conts = [n2 for n2 in nodes[n].get_conts ()
                         if n2 != 'Err']
                if len (conts) > 1:
                    r = True
                else:
                    [n] = conts
        for n in ns:
            really_in_loop[n] = r
        return r
    return set ([n for n in loop_ns if is_really_in_loop (n)])

def possible_graph_divs (p, min_cost = 20, max_cost = 20, ratio = 0.85,
                         trace = None):
    es = [e[0] for e in p.entries]
    divs = []
    direct_costs = {}
    future_costs = {'Ret': set (), 'Err': set ()}
    prev_costs = {}
    int_costs = {}
    fracs = {}
    for n in p.nodes:
        node = p.nodes[n]
        if node.kind == 'Call':
            cost = set ([(n, 20)])
        elif p.loop_id (n):
            cost = set ([(p.loop_id (n), 50)])
        else:
            cost = set ([(n, len (node.get_mem_accesses ()))])
            cost.discard ((n, 0))
        direct_costs[n] = cost
    for n in p.tarjan_order:
        prev_costs[n] = set.union (* ([direct_costs[n]]
                                      + [prev_costs.get (c, set ()) for c in p.preds[n]]))
    for n in reversed (p.tarjan_order):
        cont_costs = [future_costs.get (c, set ())
                      for c in p.nodes[n].get_conts ()]
        cost = set.union (* ([direct_costs[n]] + cont_costs))
        p_ct = sum ([c for (_, c) in prev_costs[n]])
        future_costs[n] = cost
        if p.nodes[n].kind != 'Cond' or p_ct > max_cost:
            continue
        ct = sum ([c for (_, c) in set.union (cost, prev_costs[n])])
        if ct < min_cost:
            continue
        [c1, c2] = [sum ([c for (_, c)
                          in set.union (cs, prev_costs[n])])
                    for cs in cont_costs]
        fracs[n] = ((c1 * c1) + (c2 * c2)) / (ct * ct * 1.0)
        if fracs[n] < ratio:
            divs.append (n)
    divs.reverse ()
    if trace != None:
        trace[0] = (direct_costs, future_costs, prev_costs,
                    int_costs, fracs)
    return divs

def compute_var_deps (nodes, outputs, preds, override_lvals_rvals = {},
                      trace = None):
    # outs = list of (outname, retvars)
    var_deps = {}
    visit = set ()
    visit.update (preds['Ret'])
    visit.update (preds['Err'])

    nodes = contextual_cond_simps (nodes, preds)

    while visit:
        n = visit.pop ()

        node = simplify_node_elementary (nodes[n])
        if n in override_lvals_rvals:
            (lvals, rvals) = override_lvals_rvals[n]
            lvals = set (lvals)
            rvals = set (rvals)
        elif node.is_noop ():
            lvals = set ([])
            rvals = set ([])
        else:
            rvals = syntax.get_node_rvals (node)
            rvals = set (rvals.iteritems ())
            lvals = set (node.get_lvals ())
        cont_vs = set ()

        for c in node.get_conts ():
            if c == 'Ret':
                cont_vs.update (outputs (n))
            elif c == 'Err':
                pass
            else:
                cont_vs.update (var_deps.get (c, []))
        vs = set.union (rvals, cont_vs - lvals)

        if n in var_deps and vs <= var_deps[n]:
            continue
        if trace and n in trace:
            diff = vs - var_deps.get (n, set())
            printout ('add %s at %d' % (diff, n))
            printout ('  %s, %s, %s, %s' % (len (vs), len (cont_vs), len (lvals), len (rvals)))
        var_deps[n] = vs
        visit.update (preds[n])

    return var_deps

def compute_loop_var_analysis (p, var_deps, n, override_nodes = None):
    if override_nodes == None:
        nodes = p.nodes
    else:
        nodes = override_nodes

    upd_vs = set ([v for n2 in p.loop_body (n)
                   if not nodes[n2].is_noop ()
                   for v in nodes[n2].get_lvals ()])
    const_vs = set ([v for n2 in p.loop_body (n)
                     for v in var_deps[n2] if v not in upd_vs])

    vca = compute_var_cycle_analysis (p, nodes, n,
                                      const_vs, set (var_deps[n]))
    vca = [(syntax.mk_var (nm, typ), data)
           for ((nm, typ), data) in vca.items ()]
    return vca

cvca_trace = []
cvca_diag = [False]
no_accum_expressions = set ()

def compute_var_cycle_analysis (p, nodes, n, const_vars, vs, diag = None):

    if diag == None:
        diag = cvca_diag[0]

    cache = {}
    del cvca_trace[:]
    impossible_nodes = {}
    loop = p.loop_body (n)

    def warm_cache_before (n2, v):
        cvca_trace.append ((n2, v))
        cvca_trace.append ('(')
        arc = []
        for i in range (100000):
            opts = [n3 for n3 in p.preds[n2] if n3 in loop
                    if v not in nodes[n3].get_lvals ()
                    if n3 != n
                    if (n3, v) not in cache]
            if not opts:
                break
            n2 = opts[0]
            arc.append (n2)
        if not (len (arc) < 100000):
            trace ('warmup overrun in compute_var_cycle_analysis')
            trace ('chasing %s in %s' % (v, set (arc)))
            assert False, (v, arc[-500:])
        for n2 in reversed (arc):
            var_eval_before (n2, v)
        cvca_trace.append (')')

    def var_eval_before (n2, v, do_cmp = True):
        if (n2, v) in cache and do_cmp:
            return cache[(n2, v)]
        if n2 == n and do_cmp:
            var_exp = mk_var (v[0], v[1])
            vs = set ([v for v in [v] if v not in const_vars])
            return (vs, var_exp)
        warm_cache_before (n2, v)
        ps = [n3 for n3 in p.preds[n2] if n3 in loop
              if not node_impossible (n3)]
        if not ps:
            return None
        vs = [var_eval_after (n3, v) for n3 in ps]
        if not all ([v3 == vs[0] for v3 in vs]):
            if diag:
                trace ('vs disagree for %s @ %d: %s' % (v, n2, vs))
            r = None
        else:
            r = vs[0]
        if do_cmp:
            cache[(n2, v)] = r
        return r
    def var_eval_after (n2, v):
        node = nodes[n2]
        if node.kind == 'Call' and v in node.rets:
            if diag:
                trace ('fetched %s from call at %d' % (v, n2))
            return None
        elif node.kind == 'Basic':
            for (lv, val) in node.upds:
                if lv == v:
                    return expr_eval_before (n2, val)
            return var_eval_before (n2, v)
        else:
            return var_eval_before (n2, v)
    def expr_eval_before (n2, expr):
        if expr.kind == 'Op':
            if expr.vals == []:
                return (set(), expr)
            vals = [expr_eval_before (n2, v)
                    for v in expr.vals]
            if None in vals:
                return None
            s = set.union (* [s for (s, v) in vals])
            if len(s) > 1:
                if diag:
                    trace ('too many vars for %s @ %d: %s' % (expr, n2, s))
                return None
            return (s, Expr ('Op', expr.typ,
                    name = expr.name,
                    vals = [v for (s, v) in vals]))
        elif expr.kind == 'Num':
            return (set(), expr)
        elif expr.kind == 'Var':
            return var_eval_before (n2,
                                    (expr.name, expr.typ))
        else:
            if diag:
                trace ('Unwalkable expr %s' % expr)
            return None
    def node_impossible (n2):
        if n2 in impossible_nodes:
            return impossible_nodes[n2]
        if n2 == n or n2 in p.get_loop_splittables (n):
            imposs = False
        else:
            pres = [n3 for n3 in p.preds[n2]
                    if n3 in loop if not node_impossible (n3)]
            if n2 in impossible_nodes:
                imposs = impossible_nodes[n2]
            else:
                imposs = not bool (pres)
        impossible_nodes[n2] = imposs
        node = nodes[n2]
        if imposs or node.kind != 'Cond':
            return imposs
        if 1 >= len ([n3 for n3 in node.get_conts ()
                      if n3 in loop]):
            return imposs
        c = expr_eval_before (n2, node.cond)
        if c != None:
            c = try_eval_expr (c[1])
        if c != None:
            trace ('determined loop inner cond at %d equals %s'
                   % (n2, c == syntax.true_term))
        if c == syntax.true_term:
            impossible_nodes[node.right] = True
        elif c == syntax.false_term:
            impossible_nodes[node.left] = True
        return imposs

    vca = {}
    for v in vs:
        rv = var_eval_before (n, v, do_cmp = False)
        if rv == None:
            vca[v] = 'LoopVariable'
            continue
        (s, expr) = rv
        if expr == mk_var (v[0], v[1]):
            vca[v] = 'LoopConst'
            continue
        if all_vars_in_set (expr, const_vars):
            # a repeatedly evaluated const expression, is const
            vca[v] = 'LoopConst'
            continue
        if var_not_in_expr (mk_var (v[0], v[1]), expr):
            # leaf calculations do not have data flow to
            # themselves. the search algorithm doesn't
            # have to worry about these.
            vca[v] = 'LoopLeaf'
            continue
        (form, offs) = accumulator_closed_form (expr, v)
        if form != None and all_vars_in_set (form (), const_vars):
            vca[v] = ('LoopLinearSeries', form, offs)
        else:
            if diag:
                trace ('No accumulator %s => %s'
                       % (v, expr))
            no_accum_expressions.add ((v, expr))
            vca[v] = 'LoopVariable'
    return vca

eval_expr_solver = [None]

def try_eval_expr (expr):
    """attempt to reduce an expression to a single result, vaguely like
    what constant propagation would do. it might work!"""
    import search
    if not eval_expr_solver[0]:
        import solver
        eval_expr_solver[0] = solver.Solver ()
    try:
        return search.eval_model_expr ({}, eval_expr_solver[0], expr)
    except KeyboardInterrupt, e:
        raise e
    except Exception, e:
        return None

expr_linear_sum = set (['Plus', 'Minus'])
expr_linear_cast = set (['WordCast', 'WordCastSigned'])

expr_linear_all = set.union (expr_linear_sum, expr_linear_cast,
                             ['Times', 'ShiftLeft'])

def possibly_linear (expr):
    if expr.kind in set (['Var', 'Num', 'Symbol', 'Type', 'Token']):
        return True
    elif expr.is_op (expr_linear_all):
        return all ([possibly_linear (x) for x in expr.vals])
    else:
        return False

def lv_expr (expr, env):
    if expr in env:
        return env[expr]
    elif expr.kind in set (['Num', 'Symbol', 'Type', 'Token']):
        return (expr, 'LoopConst', None, set ())
    elif expr.kind == 'Var':
        return (None, None, None, None)
    elif expr.kind != 'Op':
        assert expr in env, expr

    lvs = [lv_expr (v, env) for v in expr.vals]
    rs = [lv[1] for lv in lvs]
    mk_offs = lambda vals: syntax.adjust_op_vals (expr, vals)
    if None in rs:
        return (None, None, None, None)
    if set (rs) == set (['LoopConst']):
        return (expr, 'LoopConst', None, set ())
    offs_set = set.union (* ([lv[3] for lv in lvs] + [set ()]))
    arg_offs = []
    for (expr2, k, offs, _) in lvs:
        if k == 'LoopConst' and expr2.typ.kind == 'Word':
            arg_offs.append (syntax.mk_num (0, expr2.typ))
        else:
            arg_offs.append (offs)
    if expr.is_op (expr_linear_sum):
        if set (rs) == set (['LoopConst', 'LoopLinearSeries']):
            return (expr, 'LoopLinearSeries', mk_offs (arg_offs),
                    offs_set)
    elif expr.is_op ('Times'):
        if set (rs) == set (['LoopLinearSeries', 'LoopConst']):
            # the new offset is the product of the linear offset
            # and the constant value
            [linear_offs] = [offs for (_, k, offs, _) in lvs
                             if k == 'LoopLinearSeries']
            [const_value] = [v for (v, k, _, _) in lvs
                             if k == 'LoopConst']
            return (expr, 'LoopLinearSeries',
                    mk_offs ([linear_offs, const_value]), offs_set)
    if expr.is_op ('ShiftLeft'):
        if rs == ['LoopLinearSeries', 'LoopConst']:
            return (expr, 'LoopLinearSeries',
                    mk_offs ([arg_offs[0], lvs[1][0]]), offs_set)
    if expr.is_op (expr_linear_cast):
        if rs == ['LoopLinearSeries']:
            return (expr, 'LoopLinearSeries', mk_offs (arg_offs),
                    offs_set)
    return (None, None, None, None)

# FIXME: this should probably be unified with compute_var_cycle_analysis,
# but doing so is complicated
def linear_series_exprs (p, loop, va):
    def lv_init (v, data):
        if data[0] == 'LoopLinearSeries':
            return (v, 'LoopLinearSeries', data[2], set ([data[2]]))
        elif data == 'LoopConst':
            return (v, 'LoopConst', None, set ())
        else:
            return (None, None, None, None)
    cache = {loop: dict ([(v, lv_init (v, data)) for (v, data) in va])}
    post_cache = {}
    loop_body = p.loop_body (loop)
    frontier = [n2 for n2 in p.nodes[loop].get_conts ()
                if n2 in loop_body]
    def lv_merge ((v1, lv1, offs1, oset1), (v2, lv2, offs2, oset2)):
        if v1 != v2:
            return (None, None, None, None)
        assert lv1 == lv2 and offs1 == offs2
        return (v1, lv1, offs1, oset1)
    def compute_post (n):
        if n in post_cache:
            return post_cache[n]
        pre_env = cache[n]
        env = dict (cache[n])
        if p.nodes[n].kind == 'Basic':
            for ((v, typ), rexpr) in p.nodes[n].upds:
                env[mk_var (v, typ)] = lv_expr (rexpr, pre_env)
        elif p.nodes[n].kind == 'Call':
            for (v, typ) in p.nodes[n].get_lvals ():
                env[mk_var (v, typ)] = (None, None, None, None)
        post_cache[n] = env
        return env
    while frontier:
        n = frontier.pop ()
        if [n2 for n2 in p.preds[n] if n2 in loop_body
                if n2 not in cache]:
            continue
        if n in cache:
            continue
        envs = [compute_post (n2) for n2 in p.preds[n]
                if n2 in loop_body]
        all_vs = set.union (* [set (env) for env in envs])
        cache[n] = dict ([(v, foldr1 (lv_merge,
                                      [env.get (v, (None, None, None, None))
                                       for env in envs]))
                          for v in all_vs])
        frontier.extend ([n2 for n2 in p.nodes[n].get_conts ()
                          if n2 in loop_body])
    return cache

def get_loop_linear_offs (p, loop_head):
    import search
    va = search.get_loop_var_analysis_at (p, loop_head)
    exprs = linear_series_exprs (p, loop_head, va)
    def offs_fn (n, expr):
        assert p.loop_id (n) == loop_head
        env = exprs[n]
        rv = lv_expr (expr, env)
        if rv[1] == None:
            return None
        elif rv[1] == 'LoopConst':
            return mk_num (0, expr.typ)
        elif rv[1] == 'LoopLinearSeries':
            return rv[2]
        else:
            assert not 'lv_expr kind understood', rv
    return offs_fn

def interesting_node_exprs (p, n, tags = None, use_pairings = True):
    if tags == None:
        tags = p.pairing.tags
    node = p.nodes[n]
    memaccs = node.get_mem_accesses ()
    vs = [(kind, ptr) for (kind, ptr, v, m) in memaccs]
    vs += [('MemUpdateArg', v) for (kind, ptr, v, m) in memaccs
           if kind == 'MemUpdate']
    if node.kind == 'Call' and use_pairings:
        tag = p.node_tags[n][0]
        from target_objects import functions, pairings
        import solver
        fun = functions[node.fname]
        arg_input_map = dict (azip (fun.inputs, node.args))
        pairs = [pair for pair in pairings.get (node.fname, [])
                 if pair.tags == tags]
        if not pairs:
            return vs
        [pair] = pairs
        in_eq_vs = [(('Call', pair.name, i),
                     var_subst (v, arg_input_map))
                    for (i, ((lhs, l_s), (rhs, r_s)))
                    in enumerate (pair.eqs[0])
                    if l_s.endswith ('_IN') and r_s.endswith ('_IN')
                    if l_s != r_s
                    if solver.typ_representable (lhs.typ)
                    for (v, site) in [(lhs, l_s), (rhs, r_s)]
                    if site == '%s_IN' % tag]
        vs.extend (in_eq_vs)
    return vs

def interesting_linear_series_exprs (p, loop, va, tags = None,
                                     use_pairings = True):
    if tags == None:
        tags = p.pairing.tags
    expr_env = linear_series_exprs (p, loop, va)
    res_env = {}
    for (n, env) in expr_env.iteritems ():
        vs = interesting_node_exprs (p, n)

        vs = [(kind, v, lv_expr (v, env)) for (kind, v) in vs]
        vs = [(kind, v, offs, offs_set)
              for (kind, v, (_, lv, offs, offs_set)) in vs
              if lv == 'LoopLinearSeries']
        if vs:
            res_env[n] = vs
    return res_env

def mk_var_renames (xs, ys):
    renames = {}
    for (x, y) in azip (xs, ys):
        assert x.kind == 'Var' and y.kind == 'Var'
        assert x.name not in renames
        renames[x.name] = y.name
    return renames

def first_aligned_address (nodes, radix):
    ks = [k for k in nodes
          if k % radix == 0]
    if ks:
        return min (ks)
    else:
        return None

def entry_aligned_address (fun, radix):
    n = fun.entry
    while n % radix != 0:
        ns = fun.nodes[n].get_conts ()
        assert len (ns) == 1, (fun.name, n)
        [n] = ns
    return n

def aligned_address_sanity (functions, symbols, radix):
    for (f, func) in functions.iteritems ():
        if f not in symbols:
            # happens for static or invented functions sometimes
            continue
        if func.entry:
            addr = first_aligned_address (func.nodes, radix)
            if addr == None:
                printout ('Warning: %s: no aligned instructions' % f)
                continue
            addr2 = symbols[f][0]
            if addr != addr2:
                printout ('target mismatch on func %s' % f)
                printout ('  (starts at 0x%x not 0x%x)' % (addr, addr2))
                return False
            addr3 = entry_aligned_address (func, radix)
            if addr3 != addr2:
                printout ('entry mismatch on func %s' % f)
                printout ('  (enters at 0x%x not 0x%x)' % (addr3, addr2))
                return False
    return True

# variant of tarjan's strongly connected component algorithm
def tarjan (graph, entries):
    """tarjan (graph, entries)
    variant of tarjan's strongly connected component algorithm
    e.g. tarjan ({1: [2, 3], 3: [4, 5]}, [1])
    entries should not be reachable"""
    data = {}
    comps = []
    for v in entries:
        assert v not in data
        tarjan1 (graph, v, data, [], set ([]), comps)
    return comps

def tarjan1 (graph, v, data, stack, stack_set, comps):
    vs = []
    while True:
        # skip through nodes with single successors
        data[v] = [len(data), len(data)]
        stack.append(v)
        stack_set.add(v)
        cs = graph[v]
        if len (cs) != 1 or cs[0] in data:
            break
        vs.append ((v, cs[0]))
        [v] = cs

    for c in graph[v]:
        if c not in data:
            tarjan1 (graph, c, data, stack, stack_set, comps)
            data[v][1] = min (data[v][1], data[c][1])
        elif c in stack_set:
            data[v][1] = min (data[v][1], data[c][0])

    vs.reverse ()
    for (v2, c) in vs:
        data[v2][1] = min (data[v2][1], data[c][1])

    for (v2, _) in [(v, 0)] + vs:
        if data[v2][1] == data[v2][0]:
            comp = []
            while True:
                x = stack.pop ()
                stack_set.remove (x)
                if x == v2:
                    break
                comp.append (x)
            comps.append ((v2, comp))

def divides_loop (graph, split_set):
    graph2 = dict (graph)
    for n in split_set:
        graph2[n] = []
    assert 'ENTRY_POINT' not in graph2
    graph2['ENTRY_POINT'] = list (graph)
    comps = tarjan (graph2, ['ENTRY_POINT'])
    return not ([(h, t) for (h, t) in comps if t])

def strongly_connected_split_points1 (graph):
    """find the nodes of a strongly connected
    component which, when removed, disconnect the component.
    complex loops lack such a split point."""

    # find one simple cycle in the graph
    walk = []
    walk_set = set ()
    n = min (graph)
    while n not in walk_set:
        walk.append (n)
        walk_set.add (n)
        n = graph[n][0]
    i = walk.index (n)
    cycle = walk[i:]

    def subgraph_test (subgraph):
        graph2 = dict ([(n, [n2 for n2 in graph[n] if n2 in subgraph])
                        for n in subgraph])
        graph2['HEAD'] = list (subgraph)
        comps = tarjan (graph2, ['HEAD'])
        return bool ([h for (h, t) in comps if t])

    cycle_set = set (cycle)
    cycle = [('Node', set ([n]), False,
              [n2 for n2 in graph[n] if n2 != graph[n][0]])
             for n in cycle]
    i = 0
    while i < len (cycle):
        (kind, ns, test, unvisited) = cycle[i]
        if not unvisited:
            i += 1
            continue
        n = unvisited.pop ()
        arc_set = set ()
        while n not in cycle_set:
            if n in arc_set:
                # found two totally disjoint loops, so there
                # are no splitting points
                return set ()
            arc_set.add (n)
            n = graph[n][0]
        if n in ns:
            if kind == 'Node':
                # only this node can be a splittable now.
                if subgraph_test (set (graph) - set ([n])):
                    return set ()
                else:
                    return set ([n])
            else:
                cycle[i] = (kind, ns, True, unvisited)
                ns.update (arc_set)
                continue
        j = (i + 1) % len (cycle)
        new_ns = set ()
        new_unvisited = set ()
        new_test = False
        while n not in cycle[j][1]:
            new_ns.update (cycle[j][1])
            new_unvisited.update (cycle[j][3])
            new_test = cycle[j][2] or new_test
            j = (j + 1) % len (cycle)
        new_ns.update (arc_set)
        new_unvisited.update ([n3 for n2 in arc_set for n3 in graph[n2]])
        new_v = ('Group', new_ns, new_test, list (new_unvisited - new_ns))
        if j > i:
            cycle[i + 1:j] = [new_v]
        else:
            cycle = [cycle[i], new_v] + cycle[j:i]
            i = 0
        cycle_set.update (new_ns)
    for (kind, ns, test, unvisited) in cycle:
        if test and subgraph_test (ns):
            return set ()
    return set ([n for (kind, ns, _, _) in cycle
                 if kind == 'Node' for n in ns])

def strongly_connected_split_points (graph):
    res = strongly_connected_split_points1 (graph)
    res2 = set ()
    for n in graph:
        graph2 = dict (graph)
        graph2[n] = []
        graph2['ENTRY'] = list (graph)
        comps = tarjan (graph2, ['ENTRY'])
        if not [comp for comp in comps if comp[1]]:
            res2.add (n)
    assert res == res2, (graph, res, res2)
    return res

def get_one_loop_splittable (p, loop_set):
    """discover a component of a strongly connected
    component which, when removed, disconnects the component.
    complex loops lack such a split point."""
    candidates = set (loop_set)
    graph = dict ([(x, [y for y in p.nodes[x].get_conts ()
                        if y in loop_set]) for x in loop_set])
    while candidates:
        loop2 = find_loop_avoiding (graph, loop_set, candidates)
        candidates = set.intersection (loop2, candidates)
        if not candidates:
            return None
        n = candidates.pop ()
        graph2 = dict ([(x, [y for y in graph[x] if y != n])
                        for x in graph])
        comps = tarjan (graph2, [n])
        comps = [(h, t) for (h, t) in comps if t]
        if not comps:
            return n
        for (h, t) in comps:
            s = set ([h] + t)
            candidates = set.intersection (s, candidates)
    return None

def find_loop_avoiding (graph, loop, avoid):
    n = (list (loop - avoid) + list (loop))[0]
    arc = [n]
    visited = set ([n])
    while True:
        cs = set (graph[n])
        acs = cs - avoid
        vcs = set.intersection (cs, visited)
        if vcs:
            n = vcs.pop ()
            break
        elif acs:
            n = acs.pop ()
        else:
            n = cs.pop ()
        visited.add (n)
        arc.append (n)
    [i] = [i for (i, n2) in enumerate (arc) if n2 == n]
    return set (arc[i:])

# non-equality relations in proof hypotheses are recorded as a pretend
# equality and reverted to their 'real' meaning here.
def mk_stack_wrapper (stack_ptr, stack, excepts):
    return syntax.mk_rel_wrapper ('StackWrapper',
                                  [stack_ptr, stack] + excepts)

def mk_mem_acc_wrapper (addr, v):
    return syntax.mk_rel_wrapper ('MemAccWrapper', [addr, v])

def mk_mem_wrapper (m):
    return syntax.mk_rel_wrapper ('MemWrapper', [m])

def tm_with_word32_list (xs):
    if xs:
        return foldr1 (mk_plus, map (mk_word32, xs))
    else:
        return mk_uminus (mk_word32 (0))

def word32_list_from_tm (t):
    xs = []
    while t.is_op ('Plus'):
        [x, t] = t.vals
        assert x.kind == 'Num' and x.typ == word32T
        xs.append (x.val)
    if t.kind == 'Num':
        xs.append (t.val)
    return xs

def word64_list_from_tm (t):
    xs = []
    while t.is_op ('Plus'):
        [x, t] = t.vals
        assert x.kind == 'Num' and x.typ == word64T
        xs.append (x.val)
    if t.kind == 'Num':
        xs.append (t.val)
    return xs

def tm_with_word_list(xs):
    if xs:
        return foldr1(mk_plus, map(syntax.arch.mk_word, xs))
    else:
        return mk_uminus(syntax.arch.mk_word(0))

def mk_eq_selective_wrapper (v, (xs, ys)):
    # this is a huge hack, but we need to put these lists somewhere
    xs = tm_with_word_list (xs)
    ys = tm_with_word_list (ys)
    return syntax.mk_rel_wrapper ('EqSelectiveWrapper', [v, xs, ys])

def apply_rel_wrapper (lhs, rhs):
    syntax.context_trace()

    assert lhs.typ == syntax.builtinTs['RelWrapper']
    assert rhs.typ == syntax.builtinTs['RelWrapper']
    assert lhs.kind == 'Op'
    assert rhs.kind == 'Op'
    ops = set ([lhs.name, rhs.name])
    if ops == set (['StackWrapper']):
        [sp1, st1] = lhs.vals[:2]
        [sp2, st2] = rhs.vals[:2]
        excepts = list (set (lhs.vals[2:] + rhs.vals[2:]))
        for p in excepts:
            st1 = syntax.mk_memupd (st1, p, syntax.arch.mk_word(0))
            st2 = syntax.mk_memupd (st2, p, syntax.arch.mk_word(0))

        return syntax.Expr ('Op', boolT, name = 'StackEquals',
                            vals = [sp1, st1, sp2, st2])
    elif ops == set (['MemAccWrapper', 'MemWrapper']):
        [acc] = [v for v in [lhs, rhs] if v.is_op ('MemAccWrapper')]
        [addr, val] = acc.vals
        assert addr.typ == syntax.arch.wordT
        [m] = [v for v in [lhs, rhs] if v.is_op ('MemWrapper')]
        [m] = m.vals
        assert m.typ == builtinTs['Mem']
        expr = mk_eq (mk_memacc (m, addr, val.typ), val)
        return expr
    elif ops == set (['EqSelectiveWrapper']):
        [lhs_v, _, _] = lhs.vals
        [rhs_v, _, _] = rhs.vals
        if lhs_v.typ == syntax.builtinTs['RelWrapper']:
            return apply_rel_wrapper (lhs_v, rhs_v)
        else:
            return mk_eq (lhs, rhs)
    else:
        assert not 'rel wrapper opname understood'

def inst_eq_at_visit (exp, vis):
    if not exp.is_op ('EqSelectiveWrapper'):
        return True
    [_, xs, ys] = exp.vals
    xs = word64_list_from_tm(xs)
    ys = word64_list_from_tm(ys)
    if vis.kind == 'Number':
        return vis.n in xs
    elif vis.kind == 'Offset':
        return vis.n in ys
    else:
        assert not 'visit kind useable', vis

def strengthen_hyp (expr, sign = 1):
    if not expr.kind == 'Op':
        return expr
    if expr.name in ['And', 'Or']:
        vals = [strengthen_hyp (v, sign) for v in expr.vals]
        return syntax.adjust_op_vals (expr, vals)
    elif expr.name == 'Implies':
        [l, r] = expr.vals
        l = strengthen_hyp (l, - sign)
        r = strengthen_hyp (r, sign)
        return syntax.mk_implies (l, r)
    elif expr.name == 'Not':
        [x] = expr.vals
        x = strengthen_hyp (x, - sign)
        return syntax.mk_not (x)
    elif expr.name == 'StackEquals':
        if sign == 1:
            return syntax.Expr ('Op', boolT,
                                name = 'ImpliesStackEquals', vals = expr.vals)
        else:
            return syntax.Expr ('Op', boolT,
                                name = 'StackEqualsImplies', vals = expr.vals)
    elif expr.name == 'ROData':
        if sign == 1:
            return syntax.Expr ('Op', boolT,
                                name = 'ImpliesROData', vals = expr.vals)
        else:
            return expr
    elif expr.name == 'Equals' and expr.vals[0].typ == boolT:
        vals = expr.vals
        if vals[1] in [syntax.true_term, syntax.false_term]:
            vals = [vals[1], vals[0]]
        if vals[0] == syntax.true_term:
            return strengthen_hyp (vals[1], sign)
        elif vals[0] == syntax.false_term:
            return strengthen_hyp (syntax.mk_not (vals[1]), sign)
        else:
            return expr
    else:
        return expr

def weaken_assert (expr):
    return strengthen_hyp (expr, -1)

pred_logic_ops = set (['Not', 'And', 'Or', 'Implies'])

def norm_neg (expr):
    if not expr.is_op ('Not'):
        return expr
    [nexpr] = expr.vals
    if not nexpr.is_op (pred_logic_ops):
        return expr
    if nexpr.is_op ('Not'):
        [expr] = nexpr.vals
        return norm_neg (expr)
    [x, y] = nexpr.vals
    if nexpr.is_op ('And'):
        return mk_or (norm_mk_not (x), norm_mk_not (y))
    elif nexpr.is_op ('Or'):
        return mk_and (norm_mk_not (x), norm_mk_not (y))
    elif nexpr.is_op ('Implies'):
        return mk_and (x, mk_not (y))

def norm_mk_not (expr):
    return norm_neg (mk_not (expr))

def split_conjuncts (expr):
    expr = norm_neg (expr)
    if expr.is_op ('And'):
        [x, y] = expr.vals
        return split_conjuncts (x) + split_conjuncts (y)
    else:
        return [expr]

def split_disjuncts (expr):
    expr = norm_neg (expr)
    if expr.is_op ('Or'):
        [x, y] = expr.vals
        return split_disjuncts (x) + split_disjuncts (y)
    else:
        return [expr]

def binary_search_least (test, minimum, maximum):
    """find least n, minimum <= n <= maximum, for which test (n)."""
    assert maximum >= minimum
    if test (minimum):
        return minimum
    if maximum == minimum or not test (maximum):
        return None
    while maximum > minimum + 1:
        cur = (minimum + maximum) / 2
        if test (cur):
            maximum = cur
        else:
            minimum = cur + 1
    assert minimum + 1 == maximum
    return maximum

def binary_search_greatest (test, minimum, maximum):
    """find greatest n, minimum <= n <= maximum, for which test (n)."""
    assert maximum >= minimum
    if test (maximum):
        return maximum
    if maximum == minimum or not test (minimum):
        return None
    while maximum > minimum + 1:
        cur = (minimum + maximum) / 2
        if test (cur):
            minimum = cur
        else:
            maximum = cur - 1
    assert minimum + 1 == maximum
    return minimum

