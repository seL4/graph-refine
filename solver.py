#
# Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

import syntax

# code and classes for controlling SMT solvers, including 'fast' solvers,
# which support SMTLIB2 push/pop and are controlled by pipe, and heavyweight
# 'slow' solvers which are run once per problem on static input files.
import signal
solverlist_missing = """
This tool requires the use of an SMT solver.

This tool searches for the file '.solverlist' in the current directory and
in every parent directory up to the filesystem root.
"""
solverlist_format = """
The .solverlist format is one solver per line, e.g.

# SONOLAR is the strongest offline solver in our experiments.
SONOLAR: offline: /home/tsewell/bin/sonolar --input-format=smtlib2
# CVC4 is useful in online and offline mode.
CVC4: online: /home/tsewell/bin/cvc4 --incremental --lang smt --tlimit=5000
CVC4: offline: /home/tsewell/bin/cvc4 --lang smt
# Z3 is a useful online solver. Use of Z3 in offline mode is not recommended,
# because it produces incompatible models.
Z3 4.3: online: /home/tsewell/dev/z3-dist/build/z3 -t:2 -smt2 -in
# Z3 4.3: offline: /home/tsewell/dev/z3-dist/build/z3 -smt2 -in

N.B. only ONE online solver is needed, so Z3 is redundant in the above.

Each non-comment line is ':' separated, with this pattern:
name : online/offline/fast/slow : command

The name is used to identify the solver. The second token specifies
the solver mode. Solvers in "fast" or "online" mode must support all
interactive SMTLIB2 features including push/pop. With "slow" or "offline" mode
the solver will be executed once per query, and push/pop will not be used.

The remainder of each line is a shell command that executes the solver in
SMTLIB2 mode. For online solvers it is typically worth setting a resource
limit, after which the offline solver will be run.

The first online solver will be used. The offline solvers will be used in
parallel, by default. The set to be used in parallel can be controlled with
a strategy line e.g.:
strategy: SONOLAR all, SONOLAR hyp, CVC4 hyp

This specifies that SONOLAR and CVC4 should both be run on each hypothesis. In
addition SONOLAR will be applied to try to solve all related hypotheses at
once, which may be faster than solving them one at a time.
"""

solverlist_file = ['.solverlist']
class SolverImpl:
    def __init__ (self, name, fast, args, timeout):
        self.fast = fast
        self.args = args
        self.timeout = timeout
        self.origname = name
        self.mem_mode = None
        if self.fast:
            self.name = name + ' (online)'
        else:
            self.name = name + ' (offline)'

    def __repr__ (self):
        return 'SolverImpl (%r, %r, %r, %r)' % (self.name,
                                                self.fast, self.args, self.timeout)

def parse_solver (bits):
    import os
    import sys
    mode_set = ['fast', 'slow', 'online', 'offline']
    if len (bits) < 3 or bits[1].lower () not in mode_set:
        print 'solver.py: solver list could not be parsed'
        print '  in %s' % solverlist_file[0]
        print '  reading %r' % bits
        print solverlist_format
        sys.exit (1)
    name = bits[0]
    fast = (bits[1].lower () in ['fast', 'online'])
    args = bits[2].split ()
    assert os.path.exists (args[0]), (args[0], bits)
    if not fast:
        timeout = 6000
    else:
        timeout = 30
    return SolverImpl (name, fast, args, timeout)

def find_solverlist_file ():
    import os
    import sys
    path = os.path.abspath (os.getcwd ())
    while not os.path.exists (os.path.join (path, '.solverlist')):
        (parent, _) = os.path.split (path)
        if parent == path:
            print "solver.py: '.solverlist' missing"
            print solverlist_missing
            print solverlist_format
            sys.exit (1)
        path = parent
    fname = os.path.join (path, '.solverlist')
    solverlist_file[0] = fname
    return fname

def get_solver_set ():
    solvers = []
    strategy = None
    for line in open (find_solverlist_file ()):
        line = line.strip ()
        if not line or line.startswith ('#'):
            continue
        bits = [bit.strip () for bit in line.split (':', 2)]
        if bits[0] == 'strategy':
            [_, strat] = bits
            strategy = parse_strategy (strat)
        elif bits[0] == 'config':
            [_, config] = bits
            assert solvers
            parse_config_change (config, solvers[-1])
        else:
            solvers.append (parse_solver (bits))
    return (solvers, strategy)

def parse_strategy (strat):
    solvs = strat.split (',')
    strategy = []
    for solv in solvs:
        bits = solv.split ()
        if len (bits) != 2 or bits[1] not in ['all', 'hyp']:
            print "solver.py: strategy element %r" % bits
            print "found in .solverlist strategy line"
            print "should be [solvername, 'all' or 'hyp']"
            sys.exit (1)
        strategy.append (tuple (bits))
    return strategy

def parse_config_change (config, solver):
    for assign in config.split (','):
        bits = assign.split ('=')
        assert len (bits) == 2, bits
        [lhs, rhs] = bits
        lhs = lhs.strip ().lower ()
        rhs = rhs.strip ().lower ()
        if lhs == 'mem_mode':
            assert rhs in ['8', '32', '64']
            solver.mem_mode = rhs
        else:
            assert not 'config understood', assign

def load_solver_set ():
    import sys
    (solvers, strategy) = get_solver_set ()
    fast_solvers = [sv for sv in solvers if sv.fast]
    slow_solvers = [sv for sv in solvers if not sv.fast]
    slow_dict = dict ([(sv.origname, sv) for sv in slow_solvers])
    if strategy == None:
        strategy = [(nm, strat) for nm in slow_dict
                    for strat in ['all', 'hyp']]
    for (nm, strat) in strategy:
        if nm not in slow_dict:
            print "solver.py: strategy option %r" % nm
            print "found in .solverlist strategy line"
            print "not an offline solver (required for parallel use)"
            print "(known offline solvers %s)" % slow_dict.keys ()
            sys.exit (1)
    strategy = [(slow_dict[nm], strat) for (nm, strat) in strategy]
    assert fast_solvers, solvers
    assert slow_solvers, solvers
    return (fast_solvers[0], slow_solvers[0], strategy, slow_dict.values ())

(fast_solver, slow_solver, strategy, model_strategy) = load_solver_set ()

from syntax import (Expr, fresh_name, builtinTs, true_term, false_term,
                    foldr1, mk_or, boolT, word64T, word32T, word16T, word8T, mk_implies, Type, get_global_wrapper)
from target_objects import structs, rodata, sections, trace, printout
from logic import mk_align_valid_ineq, pvalid_assertion1, pvalid_assertion2

import syntax
import subprocess
import sys
import resource
import re
import random
import time
import tempfile
import os

last_solver = [None]
last_10_models = []
last_satisfiable_hyps = [None]
last_hyps = [None]
last_check_model_state = [None]
inconsistent_hyps = []

active_solvers = []
max_active_solvers = [5]

random_name = random.randrange (1, 10 ** 9)
count = [0]

save_solv_example_time = [-1]

def save_solv_example (solv, last_msgs, comments = []):
    count[0] += 1
    name = 'ex_%d_%d' % (random_name, count[0])
    f = open ('smt_examples/' + name, 'w')
    for msg in comments:
        f.write ('; ' + msg + '\n')
    solv.write_solv_script (f, last_msgs)
    f.close ()

def write_last_solv_script (solv, fname):
    f = open (fname, 'w')
    hyps = last_hyps[0]
    cmds = ['(assert %s)' % hyp for (hyp, _) in hyps] + ['(check-sat)']
    solv.write_solv_script (f, cmds)
    f.close ()

def run_time (elapsed, proc):
    user = None
    sys = None
    try:
        import psutil
        ps = psutil.Process (proc.pid)
        ps_time = ps.cpu_times ()
        user = ps_time.user
        sys = ps_time.system
        if elapsed == None:
            elapsed = time.time () - ps.create_time ()
    except ImportError, e:
        return '(cannot import psutil, cannot time solver)'
    except Exception, e:
        pass
    times = ['%.2fs %s' % (t, msg)
             for (t, msg) in zip ([elapsed, user, sys],
                                  ['elapsed', 'user', 'sys'])
             if t != None]
    if not times:
        return '(unknown time)'
    else:
        return '(%s)' % ', '.join (times)

def smt_typ(typ):
    if typ.kind == 'Word':
        return '(_ BitVec %d)' % typ.num
    elif typ.kind == 'WordArray':
        return '(Array (_ BitVec %d) (_ BitVec %d))' % tuple (typ.nums)
    elif typ.kind == 'TokenWords':
        return '(Array (_ BitVec %d) (_ BitVec %d))' % (
            syntax.arch.word_size.num, typ.num)
    smt_typ_builtins = get_smt_typ_builtins()
    return smt_typ_builtins[typ.name]
def get_smt_typ_builtins():
    return {
        'Bool':'Bool',
        'Mem':'{MemSort}', 'Dom':'{MemDomSort}',
        'Token': smt_typ(syntax.arch.word_type)
    }

smt_typs_omitted = set ([builtinTs['HTD'], builtinTs['PMS']])

smt_ops = dict (syntax.ops_to_smt)
# these additional smt ops aren't used as keywords in the syntax
more_smt_ops = {
    'TokenWordsAccess': 'select', 'TokenWordsUpdate': 'store'
}
smt_ops.update (more_smt_ops)

def smt_num (num, bits):
    if num < 0:
        return '(bvneg %s)' % smt_num (- num, bits)
    if bits % 4 == 0:
        digs = bits / 4
        rep = '%x' % num
        prefix = '#x'
    else:
        digs = bits
        rep = '{x:b}'.format (x = num)
        prefix = '#b'
    rep = rep[-digs:]
    rep = ('0' * (digs - len(rep))) + rep
    assert len (rep) == digs
    return prefix + rep

def smt_num_t (num, typ):
    assert typ.kind == 'Word', typ
    return smt_num (num, typ.num)

def mk_smt_expr (smt_expr, typ):
    return Expr ('SMTExpr', typ, val = smt_expr)

class EnvMiss (Exception):
    def __init__ (self, name, typ):
        self.name = name
        self.typ = typ

cheat_mem_doms = [True]

tokens = {}

def smt_expr (expr, env, solv):
    if expr.is_op (['WordCast', 'WordCastSigned']):
        [v] = expr.vals
        assert v.typ.kind == 'Word' and expr.typ.kind == 'Word'
        ex = smt_expr (v, env, solv)
        if expr.typ == v.typ:
            return ex
        elif expr.typ.num < v.typ.num:
            return '((_ extract %d 0) %s)' % (expr.typ.num - 1, ex)
        else:
            if expr.name == 'WordCast':
                return '((_ zero_extend %d) %s)' % (
                    expr.typ.num - v.typ.num, ex)
            else:
                #print expr.name
                #assert None
                return '((_ sign_extend %d) %s)' % (
                    expr.typ.num - v.typ.num, ex)
    elif expr.is_op (['ToFloatingPoint', 'ToFloatingPointSigned',
                      'ToFloatingPointUnsigned', 'FloatingPointCast']):
        ks = [v.typ.kind for v in expr.vals]
        expected_ks = {'ToFloatingPoint': ['Word'],
                       'ToFloatingPointSigned': ['Builtin', 'Word'],
                       'ToFloatingPointUnsigned': ['Builtin', 'Word'],
                       'FloatingPointCast': ['FloatingPoint']}
        expected_ks = expected_ks[expr.name]
        assert ks == expected_ks, (ks, expected_ks)
        oname = 'to_fp'
        if expr.name == 'ToFloatingPointUnsigned':
            expr.name == 'to_fp_unsigned'
        op = '(_ %s %d %d)' % tuple ([oname + expr.typ.nums])
        vs = [smt_expr (v, env, solv) for v in expr.vals]
        return '(%s %s)' % (op, ' '.join (vs))
    elif expr.is_op (['CountLeadingZeroes', 'WordReverse']):
        [v] = expr.vals
        assert expr.typ.kind == 'Word' and expr.typ == v.typ
        v = smt_expr (v, env, solv)
        oper = solv.get_smt_derived_oper (expr.name, expr.typ.num)
        return '(%s %s)' % (oper, v)
    elif expr.is_op ('CountTrailingZeroes'):
        [v] = expr.vals
        expr = syntax.mk_clz (syntax.mk_word_reverse (v))
        return smt_expr (expr, env, solv)
    elif expr.is_op (['PValid', 'PGlobalValid',
                      'PWeakValid', 'PArrayValid']):
        #print 'pvalid:\n'
        #print expr
        if expr.name == 'PArrayValid':
            [htd, typ_expr, p, num] = expr.vals
            num = to_smt_expr (num, env, solv)
        else:
            [htd, typ_expr, p] = expr.vals
        assert typ_expr.kind == 'Type'
        typ = typ_expr.val
        if expr.name == 'PGlobalValid':
            typ = get_global_wrapper (typ)
        if expr.name == 'PArrayValid':
            typ = ('Array', typ, num)
        else:
            typ = ('Type', typ)
        assert htd.kind == 'Var'
        htd_s = env[(htd.name, htd.typ)]
        p_s = smt_expr (p, env, solv)
        print 'hhhh:'
        print p_s
        print env
        var = solv.add_pvalids (htd_s, typ, p_s, expr.name)
        return var
    elif expr.is_op ('MemDom'):
        [p, dom] = [smt_expr (e, env, solv) for e in expr.vals]
        md = '(%s %s %s)' % (smt_ops[expr.name], p, dom)
        solv.note_mem_dom (p, dom, md)
        if cheat_mem_doms:
            return 'true'
        return md
    elif expr.is_op ('MemUpdate'):
        [m, p, v] = expr.vals
        assert v.typ.kind == 'Word'
        m_s = smt_expr (m, env, solv)
        p_s = smt_expr (p, env, solv)
        v_s = smt_expr (v, env, solv)
        return smt_expr_memupd (m_s, p_s, v_s, v.typ, solv)
    elif expr.is_op ('MemAcc'):
        [m, p] = expr.vals
        assert expr.typ.kind == 'Word'
        m_s = smt_expr (m, env, solv)
        p_s = smt_expr (p, env, solv)
        return smt_expr_memacc (m_s, p_s, expr.typ, solv)
    elif expr.is_op ('Equals') and expr.vals[0].typ == builtinTs['Mem']:
        (x, y) = [smt_expr (e, env, solv) for e in expr.vals]
        if x[0] == 'SplitMem' or y[0] == 'SplitMem':
            assert not 'mem equality involving split possible', (
                x, y, expr)
        sexp = '(mem-eq %s %s)' % (x, y)
        solv.note_model_expr (sexp, boolT)
        return sexp
    elif expr.is_op ('Equals') and expr.vals[0].typ == word32T:
        (x, y) = [smt_expr (e, env, solv) for e in expr.vals]
        sexp = '(word32-eq %s %s)' % (x, y)
        #assert False
        return sexp
    elif expr.is_op('Equals') and expr.vals[0].typ == word64T:
        (x, y) = [smt_expr(e, env, solv) for e in expr.vals]
        sexp = '(word64-eq %s %s)' % (x, y)
        #print sexp
        return sexp
    elif expr.is_op ('StackEqualsImplies'):
        [sp1, st1, sp2, st2] = [smt_expr (e, env, solv)
                                for e in expr.vals]
        if sp1 == sp2 and st1 == st2:
            return 'true'
        assert st2[0] == 'SplitMem', (expr.vals, st2)
        [_, split2, top2, bot2] = st2
        if split2 != sp2:
            res = solv.check_hyp_raw ('(= %s %s)' % (split2, sp2))
            assert res == 'unsat', (split2, sp2, expr.vals)
        eq = solv.get_stack_eq_implies (split2, top2, st1)
        return '(and (= %s %s) %s)' % (sp1, sp2, eq)
    elif expr.is_op ('ImpliesStackEquals'):
        [sp1, st1, sp2, st2] = expr.vals
        eq = solv.add_implies_stack_eq (sp1, st1, st2, env)
        sp1 = smt_expr (sp1, env, solv)
        sp2 = smt_expr (sp2, env, solv)
        print "ImpliesStackEquals:"
        print sp1
        print st1
        print sp2
        print st2
        print eq
        #rv64_hack
        # for functions that do not touch stack at all,
        # something like
        # (assert (not (and (= r2_init r2_init) stack-eq)))
        # is generated. This assert cannot be satifisfied, and
        # thus an 'unsat' result. A hack here to avoid the
        # always 'unsat' result.
        if sp1 == sp2 and sp1 == 'r2_init':
            #return '(not false)'
            #return '(and (not false) false)'
            pass

        return '(and (= %s %s) %s)' % (sp1, sp2, eq)
    elif expr.is_op ('IfThenElse'):
        (sw, x, y) = [smt_expr (e, env, solv) for e in expr.vals]
        return smt_ifthenelse (sw, x, y, solv)
    elif expr.is_op ('HTDUpdate'):
        var = solv.add_var ('updated_htd', expr.typ)
        return var
    elif expr.kind == 'Op':
        #print "expr:"
        #print expr
        #print 'done\n'
        vals = [smt_expr (e, env, solv) for e in expr.vals]
        if vals:
            sexp = '(%s %s)' % (smt_ops[expr.name], ' '.join(vals))
        else:
            sexp = smt_ops[expr.name]
        maybe_note_model_expr (sexp, expr.typ, expr.vals, solv)
        return sexp
    elif expr.kind == 'Num':
        return smt_num_t (expr.val, expr.typ)
    elif expr.kind == 'Var':
        if (expr.name, expr.typ) not in env:
            trace ('Env miss for %s in smt_expr' % expr.name)
            trace ('Environment is %s' % env)
            print expr
            print expr.name
            print expr.typ
            for e in env:
                print e
                print '\n'
            raise EnvMiss (expr.name, expr.typ)
        val = env[(expr.name, expr.typ)]
        assert val[0] == 'SplitMem' or type(val) == str
        return val
    elif expr.kind == 'Invent':
        var = solv.add_var ('invented', expr.typ)
        return var
    elif expr.kind == 'SMTExpr':
        return expr.val
    elif expr.kind == 'Token':
        return solv.get_token (expr.name)
    else:
        assert not 'handled expr', expr

def smt_expr_memacc (m, p, typ, solv):
    if m[0] == 'SplitMem':
        p = solv.cache_large_expr (p, 'memacc_pointer', syntax.arch.word_type)
        (_, split, top, bot) = m
        top_acc = smt_expr_memacc (top, p, typ, solv)
        bot_acc = smt_expr_memacc (bot, p, typ, solv)
        return '(ite (bvule %s %s) %s %s)' % (split, p, top_acc, bot_acc)
    if typ.num in [8, 32, 64]:
        sexp = '(load-word%d %s %s)' % (typ.num, m, p)
    else:
        assert not 'word load type supported', typ
    solv.note_model_expr (p, syntax.arch.word_type)
    solv.note_model_expr (sexp, typ)
    return sexp

def smt_expr_memupd (m, p, v, typ, solv):
    if m[0] == 'SplitMem':
        p = solv.cache_large_expr (p, 'memupd_pointer', syntax.arch.word_type)
        v = solv.cache_large_expr (v, 'memupd_val', typ)
        (_, split, top, bot) = m
        memT = syntax.builtinTs['Mem']
        top = solv.cache_large_expr (top, 'split_mem_top', memT)
        top_upd = smt_expr_memupd (top, p, v, typ, solv)
        bot = solv.cache_large_expr (bot, 'split_mem_bot', memT)
        bot_upd = smt_expr_memupd (bot, p, v, typ, solv)
        top = '(ite (bvule %s %s) %s %s)' % (split, p, top_upd, top)
        bot = '(ite (bvule %s %s) %s %s)' % (split, p, bot, bot_upd)
        return ('SplitMem', split, top, bot)
    elif typ.num == 8:
        p = solv.cache_large_expr (p, 'memupd_pointer', syntax.arch.word_type)
        p_align = '(bvand %s %s)' % (p, syntax.arch.smt_alignment_pattern)
        solv.note_model_expr (p_align, syntax.arch.word_type)
        solv.note_model_expr(
            '(load-word%d %s %s)' % (syntax.arch.word_size, m, p_align),
            syntax.arch.word_type
        )
        return '(store-word8 %s %s %s)' % (m, p, v)
    elif typ.num in [32, 64]:
        solv.note_model_expr(
            '(load-word%d %s %s)' % (typ.num, m, p),
            typ
        )
        solv.note_model_expr(p, syntax.arch.word_type)
        return '(store-word%d %s %s %s)' % (typ.num, m, p, v)
    else:
        assert not 'MemUpdate word width supported', typ

def smt_ifthenelse (sw, x, y, solv):
    if x[0] != 'SplitMem' and y[0] != 'SplitMem':
        return '(ite %s %s %s)' % (sw, x, y)
    if x[0] != 'SplitMem':
        (x_split, x_top, x_bot) = (syntax.arch.smt_native_zero, x, x)
    else:
        (_, x_split, x_top, x_bot) = x
    if y[0] != 'SplitMem':
        (y_split, y_top, y_bot) = (syntax.arch.smt_native_zero, y, y)
    else:
        (_, y_split, y_top, y_bot) = y
    if x_split != y_split:
        split = '(ite %s %s %s)' % (sw, x_split, y_split)
    else:
        split = x_split
    return ('SplitMem', split,
            '(ite %s %s %s)' % (sw, x_top, y_top),
            '(ite %s %s %s)' % (sw, x_bot, y_bot))

def to_smt_expr (expr, env, solv):
    if expr.typ == builtinTs['RelWrapper']:
        vals = [to_smt_expr (v, env, solv) for v in expr.vals]
        return syntax.adjust_op_vals (expr, vals)
    s = smt_expr (expr, env, solv)
    return mk_smt_expr (s, expr.typ)

def typ_representable (typ):
    return (typ.kind == 'Word' or typ == builtinTs['Bool']
            or typ == builtinTs['Token'])

def maybe_note_model_expr (sexpr, typ, subexprs, solv):
    """note this expression if values of its type can be represented
    but one of the subexpression values can't be.
    e.g. note (= x y) where the type of x/y is an SMT array."""
    if not typ_representable (typ):
        return
    if all ([typ_representable (v.typ) for v in subexprs]):
        return
    assert solv, (sexpr, typ)
    solv.note_model_expr (sexpr, typ)

def split_hyp_sexpr (hyp, accum):
    if hyp[0] == 'and':
        for h in hyp[1:]:
            split_hyp_sexpr (h, accum)
    elif hyp[0] == 'not' and hyp[1][0] == '=>':
        (_, p, q) = hyp[1]
        split_hyp_sexpr (p, accum)
        split_hyp_sexpr (('not', q), accum)
    elif hyp[0] == 'not' and hyp[1][0] == 'or':
        for h in hyp[1][1:]:
            split_hyp_sexpr (('not', h), accum)
    elif hyp[0] == 'not' and hyp[1][0] == 'not':
        split_hyp_sexpr (hyp[1][1], accum)
    elif hyp[:1] + hyp[2:] == ('=>', 'false'):
        split_hyp_sexpr (('not', hyp[1]), accum)
    elif hyp[:1] == ('=', ) and ('true' in hyp or 'false' in hyp):
        (_, p, q) = hyp
        if q in ['true', 'false']:
            (p, q) = (q, p)
        if p == 'true':
            split_hyp_sexpr (q, accum)
        else:
            split_hyp_sexpr (('not', q), accum)
    else:
        accum.append (hyp)
    return accum

def split_hyp (hyp):
    if (hyp.startswith ('(and ') or hyp.startswith ('(not (=> ')
        or hyp.startswith ('(not (or ')
            or hyp.startswith ('(not (not ')):
        return [flat_s_expression (h) for h in
                split_hyp_sexpr (parse_s_expression (hyp), [])]
    else:
        return [hyp]

def preexec (timeout):
    def ret ():
        # setting the session ID on a fork allows us to clean up
        # the resulting process group, useful if running multiple
        # solvers in parallel.
        os.setsid ()
        if timeout != None:
            resource.setrlimit(resource.RLIMIT_CPU,
                               (timeout, timeout))
    return ret

class ConversationProblem (Exception):
    def __init__ (self, prompt, response):
        self.prompt = prompt
        self.response = response

def get_s_expression (stream, prompt):
    try:
        return get_s_expression_inner (stream, prompt)
    except IOError, e:
        raise ConversationProblem (prompt, 'IOError')

def get_s_expression_inner (stdout, prompt):
    """retreives responses from a solver until parens match"""
    responses = [stdout.readline ().strip ()]
    if not responses[0].startswith ('('):
        bits = responses[0].split ()
        if len (bits) != 1:
            raise ConversationProblem (prompt, responses[0])
        return bits[0]
    lpars = responses[0].count ('(')
    rpars = responses[0].count (')')
    emps = 0
    while rpars < lpars:
        r = stdout.readline ().strip ()
        responses.append (r)
        lpars += r.count ('(')
        rpars += r.count (')')
        if r == '':
            emps += 1
            if emps >= 3:
                raise ConversationProblem (prompt, responses)
        else:
            emps = 0
    return parse_s_expressions (responses)

class SolverFailure (Exception):
    def __init__ (self, msg):
        self.msg = msg

    def __str__ (self):
        return 'SolverFailure (%r)' % self.msg

class Solver:
    def __init__ (self, produce_unsat_cores = False):
        self.replayable = []
        self.unsat_cores = produce_unsat_cores
        self.mem_mode = None
        self.online_solver = None
        self.parallel_solvers = {}
        self.parallel_model_states = {}

        self.names_used = {}
        self.names_used_order = []
        self.external_names = {}
        self.name_ext = ''
        self.pvalids = {}
        self.ptrs = {}
        self.cached_exprs = {}
        self.defs = {}
        self.doms = set ()
        self.model_vars = set ()
        self.model_exprs = {}
        self.arbitrary_vars = {}
        self.stack_eqs = {}
        self.mem_naming = {}
        self.tokens = {}
        self.smt_derived_ops = {}

        self.num_hyps = 0
        self.last_model_acc_hyps = (None, None)

        self.pvalid_doms = None
        self.assertions = []

        self.fast_solver = fast_solver
        self.slow_solver = slow_solver
        self.strategy = strategy
        self.model_strategy = model_strategy

        self.add_rodata_def ()

        last_solver[0] = self

    def preamble (self, solver_impl):
        preamble = []
        if solver_impl.fast:
            preamble += ['(set-option :print-success true)']
        preamble += [ '(set-option :produce-models true)',
                      '(set-logic QF_AUFBV)', ]
        if self.unsat_cores:
            preamble += ['(set-option :produce-unsat-cores true)']
        if solver_impl.mem_mode == '8':
            preamble.extend(syntax.arch.smt_word8_preamble)
        else:
            preamble.extend(syntax.arch.smt_native_preamble)
        print preamble
        return preamble

    def startup_solver (self, use_this_solver = None):
        if self not in active_solvers:
            active_solvers.append (self)
            while len (active_solvers) > max_active_solvers[0]:
                solv = active_solvers.pop (0)
                solv.close ('active solver limit')

        if use_this_solver:
            solver = use_this_solver
        else:
            solver = self.fast_solver
        devnull = open (os.devnull, 'w')
        self.mem_mode = solver.mem_mode
        self.online_solver = subprocess.Popen (solver.args,
                                               stdin = subprocess.PIPE, stdout = subprocess.PIPE,
                                               stderr = devnull, preexec_fn = preexec (solver.timeout))
        devnull.close ()

        for msg in self.preamble (solver):
            self.send (msg, replay=False)
        for (msg, _) in self.replayable:
            #print 'replay:'
            #print msg
            self.send (msg, replay=False)

    def close (self, reason = '?'):
        self.close_parallel_solvers (reason = 'self.close (%s)'
                                     % reason)
        self.close_online_solver ()

    def close_online_solver (self):
        if self.online_solver:
            self.online_solver.stdin.close()
            self.online_solver.stdout.close()
            self.online_solver = None

    def __del__ (self):
        self.close ('__del__')

    def smt_name (self, name, kind = ('Var', None),
                  ignore_external_names = False):
        name = name.replace("'", "_").replace("#", "_").replace('"', "_")
        if not ignore_external_names:
            name = fresh_name (name, self.external_names)
        name = fresh_name (name, self.names_used, kind)
        self.names_used_order.append (name)
        return name

    def write (self, msg):
        self.online_solver.stdin.write (msg + '\n')
        self.online_solver.stdin.flush()

    def send_inner (self, msg, replay = True, is_model = True):
        if self.online_solver == None:
            self.startup_solver ()

        if self.mem_mode == '8':
            msg = msg.format(** syntax.arch.smt_word8_conversions)
        else:
            msg = msg.format(** syntax.arch.smt_native_conversions)
        try:
            self.write (msg)
            response = self.online_solver.stdout.readline().strip()
        except IOError, e:
            raise ConversationProblem (msg, 'IOError')
        if response != 'success':
            raise ConversationProblem (msg, response)

    def solver_loop (self, attempt):
        err = None
        for i in range (5):
            if self.online_solver == None:
                self.startup_solver ()
            try:
                return attempt ()
            except ConversationProblem, e:
                trace ('SMT conversation problem (attempt %d)'
                       % (i + 1))
                trace ('I sent %s' % repr (e.prompt))
                trace ('I got %s' % repr (e.response))
                trace ('restarting solver')
                sys.exit(1) # FIXME:REMOVE
                self.online_solver = None
                err = (e.prompt, e.response)
        trace ('Repeated SMT failure, giving up.')
        raise ConversationProblem (err[0], err[1])

    def send (self, msg, replay = True, is_model = True):
        self.solver_loop (lambda: self.send_inner (msg,
                                                   replay = replay, is_model = is_model))
        if replay:
            self.replayable.append ((msg, is_model))

    def get_s_expression (self, prompt):
        return get_s_expression (self.online_solver.stdout, prompt)

    def prompt_s_expression_inner (self, prompt):
        try:
            #print 'here'
            #print prompt
            self.write (prompt)
            return self.get_s_expression (prompt)
        except IOError, e:
            raise ConversationProblem (prompt, 'IOError')

    def prompt_s_expression (self, prompt):
        return self.solver_loop (lambda:
                                 self.prompt_s_expression_inner (prompt))

    def hyps_sat_raw_inner (self, hyps, model, unsat_core,
                            recursion = False):
        self.send_inner ('(push 1)', replay = False)
        for hyp in hyps:
            self.send_inner ('(assert %s)' % hyp, replay = False,
                             is_model = False)
        response = self.prompt_s_expression_inner ('(check-sat)')
        if response not in set (['sat', 'unknown', 'unsat', '']):
            raise ConversationProblem ('(check-sat)', response)

        all_ok = True
        m = {}
        ucs = []
        if response == 'sat' and model:
            all_ok = self.fetch_model (m)
            print 'sat:'
            print all_ok
        if response == 'unsat' and unsat_core:
            #if response == 'unsat':
            ucs = self.get_unsat_core ()
            print 'ucs:'
            print ucs
            all_ok = ucs != None

        self.send_inner ('(pop 1)', replay = False)

        return (response, m, ucs, all_ok)

    def add_var (self, name, typ, kind = 'Var',
                 mem_name = None,
                 ignore_external_names = False):
        if typ in smt_typs_omitted:
            # skipped. not supported by all solvers
            name = self.smt_name (name, ('Ghost', typ),
                                  ignore_external_names = ignore_external_names)
            return name
        name = self.smt_name (name, kind = (kind, typ),
                              ignore_external_names = ignore_external_names)
        # writes to zero-wired registers (e.g. RISC-V x0) have no effect
        if any([ name.startswith(rz + '_')
                 for rz in syntax.arch.zero_wired_registers]):
            self.send(
                '(define-fun %s () %s %s)' % (
                    name, smt_typ(typ), syntax.arch.smt_native_zero
                )
            )
        else:
            self.send ('(declare-fun %s () %s)' % (name, smt_typ(typ)))
        if typ_representable (typ) and kind != 'Aux':
            self.model_vars.add (name)
        if typ == builtinTs['Mem'] and mem_name != None:
            if type (mem_name) == str:
                self.mem_naming[name] = mem_name
            else:
                (nm, prev) = mem_name
                if prev[0] == 'SplitMem':
                    prev = 'SplitMem'
                prev = parse_s_expression (prev)
                self.mem_naming[name] = (nm, prev)
        return name

    def add_var_restr (self, name, typ, mem_name = None):
        name = self.add_var (name, typ, mem_name = mem_name)
        return name

    def add_def (self, name, val, env, ignore_external_names = False):
        kind = 'Var'
        if val.typ in smt_typs_omitted:
            kind = 'Ghost'
        smt = smt_expr (val, env, self)
        if smt[0] == 'SplitMem':
            (_, split, top, bot) = smt
            def add (nm, typ, smt):
                val = mk_smt_expr (smt, typ)
                return self.add_def (name + '_' + nm, val, {},
                                     ignore_external_names = ignore_external_names)
            split = add('split', syntax.arch.word_type, split)
            top = add ('top', val.typ, top)
            bot = add ('bot', val.typ, bot)
            return ('SplitMem', split, top, bot)

        name = self.smt_name (name, kind = (kind, val.typ),
                              ignore_external_names = ignore_external_names)
        if kind == 'Ghost':
            # skipped. not supported by all solvers
            return name
        if val.kind == 'Var':
            trace ('WARNING: redef of var %r to name %s' % (val, name))

        typ = smt_typ (val.typ)
        print typ
        print name
        print smt
        self.send ('(define-fun %s () %s %s)' % (name, typ, smt))

        self.defs[name] = parse_s_expression (smt)
        print self.defs[name]
        if typ_representable (val.typ):
            self.model_vars.add (name)

        return name

    def add_rodata_def (self):
        ro_name = self.smt_name ('rodata', kind = 'Fun')
        imp_ro_name = self.smt_name ('implies-rodata', kind = 'Fun')
        assert ro_name == 'rodata', repr (ro_name)
        assert imp_ro_name == 'implies-rodata', repr (imp_ro_name)
        [rodata_data, rodata_ranges, rodata_ptrs] = rodata

        if not rodata_ptrs:
            assert not rodata_data
            ro_def = 'true'
            imp_ro_def = 'true'
        else:
            ro_witness = self.add_var ('rodata-witness', syntax.arch.word_type)
            ro_witness_val = self.add_var ('rodata-witness-val', syntax.arch.rodata_chunk_type)
            assert ro_witness == 'rodata-witness'
            assert ro_witness_val == 'rodata-witness-val'
            eq_vs = [(smt_num (p, syntax.arch.word_size), smt_num (v, syntax.arch.rodata_chunk_size))
                     for (p, v) in rodata_data.iteritems ()]
            eq_vs.append ((ro_witness, ro_witness_val))
            load_word_m = ('(= (load-word%d m' % syntax.arch.rodata_chunk_size) + ' %s) %s)'
            eqs = [load_word_m % v for v in eq_vs]
            ro_def = '(and %s)' % ' \n  '.join (eqs)
            ro_ineqs = ['(and (bvule %s %s) (bvule %s %s))'
                        % (smt_num (start, syntax.arch.word_size), ro_witness,
                           ro_witness, smt_num (end, syntax.arch.word_size))
                        for (start, end) in rodata_ranges]
            assns = ['(or %s)' % ' '.join (ro_ineqs),
                     '(= (bvand rodata-witness %s) %s)' % (syntax.arch.smt_rodata_mask, syntax.arch.smt_native_zero)]
            for assn in assns:
                self.assert_fact_smt (assn)
            imp_ro_def = eqs[-1]
        self.send ('(define-fun rodata ((m %s)) Bool %s)' % (
            smt_typ (builtinTs['Mem']), ro_def))
        self.send ('(define-fun implies-rodata ((m %s)) Bool %s)' % (
            smt_typ (builtinTs['Mem']), imp_ro_def))

    def get_eq_rodata_witness (self, v):
        ro_witness = mk_smt_expr ('rodata-witness', syntax.arch.word_size)
        return syntax.mk_eq (ro_witness, v)

    def check_hyp_raw (self, hyp, model = None, force_solv = False,
                       hyp_name = None):
        return self.hyps_sat_raw ([('(not %s)' % hyp, None)],
                                  model = model, unsat_core = None,
                                  force_solv = force_solv, hyps_name = hyp_name)

    def next_hyp (self, (hyp, tag), hyp_dict):
        self.num_hyps += 1
        name = 'hyp%d' % self.num_hyps
        hyp_dict[name] = tag
        return '(! %s :named %s)' % (hyp, name)

    def hyps_sat_raw (self, hyps, model = None, unsat_core = None,
                      force_solv = False, recursion = False,
                      slow_solver = None, hyps_name = None):
        assert self.unsat_cores or unsat_core == None

        hyp_dict = {}
        print hyps
        print 'kk'
        print type(hyps)
        raw_hyps = [(hyp2, tag) for (hyp, tag) in hyps
                    for hyp2 in split_hyp (hyp)]
        last_hyps[0] = list (raw_hyps)
        hyps = [self.next_hyp (h, hyp_dict) for h in raw_hyps]
        succ = False
        solvs_used = []
        if hyps_name == None:
            hyps_name = 'group of %d hyps' % len (hyps)
        trace ('testing %s:' % hyps_name)
        if recursion:
            trace ('  (recursion)')
        else:
            for (hyp, _) in raw_hyps:
                trace ('  ' + hyp)

        if force_solv != 'Slow':
            solvs_used.append (self.fast_solver.name)
            l = lambda: self.hyps_sat_raw_inner (hyps,
                                                 model != None, unsat_core != None,
                                                 recursion = recursion)
            try:
                (response, m, ucs, succ) = self.solver_loop (l)
            except ConversationProblem, e:
                response = 'ConversationProblem'

        if succ and m and not recursion:
            succ = self.check_model ([h for (h, _) in raw_hyps], m)

        if slow_solver == None:
            slow_solver = self.slow_solver
        if ((not succ or response not in ['sat', 'unsat'])
                and slow_solver and force_solv != 'Fast'):
            if solvs_used:
                trace ('failed to get result from %s'
                       % solvs_used[0])
            trace ('running %s' % slow_solver.name)
            self.close_online_solver ()
            solvs_used.append (slow_solver.name)
            response = self.use_slow_solver (raw_hyps,
                                             model = model, unsat_core = unsat_core,
                                             use_this_solver = slow_solver)
        elif not succ:
            pass
        elif m:
            model.clear ()
            model.update (m)
        elif ucs:
            unsat_core.extend (self.get_unsat_core_tags (ucs,
                                                         hyp_dict))

        if response == 'sat':
            if not recursion:
                last_satisfiable_hyps[0] = list (raw_hyps)
            if model and not recursion:
                assert self.check_model ([h for (h, _) in raw_hyps],
                                         model)
        elif response == 'unsat':
            fact = '(not (and %s))' % ' '.join ([h
                                                 for (h, _) in raw_hyps])
            # sending this fact (and not its core-deps) might
            # lead to inaccurate cores in the future
            if not self.unsat_cores:
                self.send ('(assert %s)' % fact)
        else:
            # couldn't get a useful response from either solver.
            trace ('Solvers %s failed to resolve sat/unsat'
                   % solvs_used)
            trace ('last solver result %r' % response)
            raise SolverFailure (response)
        return response

    def get_unsat_core_tags (self, fact_names, hyps):
        names = set (fact_names)
        trace ('uc names: %s' % names)
        core = [hyps[name] for name in names
                if name.startswith ('hyp')]
        for s in fact_names:
            if s.startswith ('assert'):
                n = int (s[6:])
                core.append (self.assertions[n][1])
        trace ('uc tags: %s' % core)
        return core

    def write_solv_script (self, f, input_msgs, solver = slow_solver,
                           only_if_is_model = False):
        if solver.mem_mode == '8':
            smt_convs = syntax.arch.smt_word8_conversions
        else:
            smt_convs = syntax.arch.smt_native_conversions
        for msg in self.preamble (solver):
            msg = msg.format (** smt_convs)
            f.write (msg + '\n')
        for (msg, is_model) in self.replayable:
            if only_if_is_model and not is_model:
                continue
            msg = msg.format (** smt_convs)
            f.write (msg + '\n')

        for msg in input_msgs:
            msg = msg.format (** smt_convs)
            f.write (msg + '\n')

        f.flush ()

    def exec_slow_solver (self, input_msgs, timeout = None,
                          use_this_solver = None):
        import shutil
        solver = self.slow_solver
        if use_this_solver:
            solver = use_this_solver
        if not solver:
            return 'no-slow-solver'

        (fd, name) = tempfile.mkstemp (suffix='.txt',
                                       prefix='graph-refine-problem-')
        tmpfile_write = open (name, 'w')
        self.write_solv_script (tmpfile_write, input_msgs,
                                solver = solver)
        tmpfile_write.close ()
        print name
        shutil.copyfile(name, './logs' + name + '.smt2')
        print 'solver inputs:\n'
        print input_msgs
        print 'done\n'
        proc = subprocess.Popen (solver.args,
                                 stdin = fd, stdout = subprocess.PIPE,
                                 preexec_fn = preexec (timeout))
        os.close (fd)
        os.unlink (name)

        return (proc, proc.stdout)

    def use_slow_solver (self, hyps, model = None, unsat_core = None,
                         use_this_solver = None):
        start = time.time ()

        cmds = ['(assert %s)' % hyp for (hyp, _) in hyps
                ] + ['(check-sat)']

        if model != None:
            cmds.append (self.fetch_model_request ())

        if use_this_solver:
            solver = use_this_solver
        else:
            solver = self.slow_solver

        (proc, output) = self.exec_slow_solver (cmds,
                                                timeout = solver.timeout, use_this_solver = solver)

        response = output.readline ().strip ()
        if model != None and response == 'sat':
            assert self.fetch_model_response (model,
                                              stream = output)
        if unsat_core != None and response == 'unsat':
            trace ('WARNING no unsat core from %s' % solver.name)
            unsat_core.extend ([tag for (_, tag) in hyps])

        output.close ()

        if response not in ['sat', 'unsat']:
            trace ('SMT conversation problem after (check-sat)')

        end = time.time ()
        trace ('Got %r from %s.' % (response, solver.name))
        trace ('  after %s' % run_time (end - start, proc))
        # adjust to save difficult problems
        cutoff_time = save_solv_example_time[0]
        if cutoff_time != -1 and end - start > cutoff_time:
            save_solv_example (self, cmds,
                               comments = ['reference time %s seconds' % (end - start)])

        if model:
            assert self.check_model ([h for (h, _) in hyps], model)

        return response

    def add_parallel_solver (self, k, hyps, model = None,
                             use_this_solver = None):
        #for h in hyps:
        #	print 'hyp: \n'
        #	print h
        #	print 'hyp done\n'

        cmds = ['(assert %s)' % hyp for hyp in hyps] + ['(check-sat)']

        if model != None:
            cmds.append (self.fetch_model_request ())

        #print 'cmds'
        #print cmds
        #print 'donecmds'

        trace ('  --> new parallel solver %s' % str (k))

        if k in self.parallel_solvers:
            raise IndexError ('duplicate parallel solver ID', k)
        solver = self.slow_solver
        if use_this_solver:
            solver = use_this_solver
        (proc, output) = self.exec_slow_solver (cmds,
                                                timeout = solver.timeout, use_this_solver = solver)
        self.parallel_solvers[k] = (hyps, proc, output, solver, model)

    def wait_parallel_solver_step (self):
        import select
        assert self.parallel_solvers
        fds = dict ([(output.fileno (), k) for (k, (_, _, output, _, _))
                     in self.parallel_solvers.iteritems ()])
        try:
            (rlist, _, _) = select.select (fds.keys (), [], [])
        except KeyboardInterrupt, e:
            self.close_parallel_solvers (reason = 'interrupted')
            raise e
        k = fds[rlist.pop ()]
        (hyps, proc, output, solver, model) = self.parallel_solvers[k]
        del self.parallel_solvers[k]
        response = output.readline ().strip ()
        trace ('  <-- parallel solver %s closed: %s' % (k, response))
        trace ('      after %s' % run_time (None, proc))
        if response not in ['sat', 'unsat']:
            trace ('SMT conversation problem in parallel solver')
        trace ('Got %r from %s in parallel.' % (response, solver.name))
        m = {}
        check = None
        if response == 'sat':
            last_satisfiable_hyps[0] = hyps
        if k[0] != 'ModelRepair':
            if model == None or response != 'sat':
                output.close ()
                return (k, hyps, response)
        # model issues
        m = {}
        if model != None:
            res = self.fetch_model_response (m, stream = output)
        output.close ()
        if model != None and not res:
            # just drop this solver at this point
            trace ('failed to extract model.')
            return None
        if k[0] == 'ModelRepair':
            (_, k, i) = k
            (state, hyps) = self.parallel_model_states[k]
        else:
            i = 0
            state = None
        res = self.check_model_iteration (hyps, state, (response, m))
        (kind, details) = res
        if kind == 'Abort':
            return None
        elif kind == 'Result':
            model.update (details)
            return (k, hyps, 'sat')
        elif kind == 'Continue':
            (solv, test_hyps, state) = details
            self.parallel_model_states[k] = (state, hyps)
            k = ('ModelRepair', k, i + 1)
            self.add_parallel_solver (k, test_hyps,
                                      use_this_solver = solv, model = model)
            return None

    def wait_parallel_solver (self):
        while True:
            assert self.parallel_solvers
            try:
                res = self.wait_parallel_solver_step ()
            except ConversationProblem, e:
                continue
            if res != None:
                return res

    def close_parallel_solvers (self, ks = None, reason = '?'):
        if ks == None:
            ks = self.parallel_solvers.keys ()
        else:
            ks = [k for k in ks if k in self.parallel_solvers]
        solvs = [(proc, output) for (_, proc, output, _, _)
                 in [self.parallel_solvers[k] for k in ks]]
        if ks:
            trace (' X<-- %d parallel solvers killed: %s'
                   % (len (ks), reason))
        for k in ks:
            del self.parallel_solvers[k]
        procs = [proc for (proc, _) in solvs]
        outputs = [output for (_, output) in solvs]
        for proc in procs:
            os.killpg (proc.pid, signal.SIGTERM)
        for output in outputs:
            output.close ()
        for proc in procs:
            os.killpg (proc.pid, signal.SIGKILL)
            proc.wait ()

    def parallel_check_hyps (self, hyps, env, model = None):
        """test a series of keyed hypotheses [(k1, h1), (k2, h2) ..etc]
        either returns (True, -) all hypotheses true
        or (False, ki) i-th hypothesis unprovable"""

        print 'chk:'
        print hyps

        hyps = [(k, hyp) for (k, hyp) in hyps
                if not self.test_hyp (hyp, env, force_solv = 'Fast',
                                      catch = True, hyp_name = "('hyp', %s)" % k)]
        assert not self.parallel_solvers
        if not hyps:
            return ('unsat', None)
        all_hyps = foldr1 (syntax.mk_and, [h for (k, h) in hyps])
        print 'all_hyps: %s' % all_hyps
        def spawn ((k, hyp), stratkey):
            goal = smt_expr (syntax.mk_not (hyp), env, self)
            [self.add_parallel_solver ((solver.name, strat, k),
                                       [goal], use_this_solver = solver,
                                       model = model)
             for (solver, strat) in self.strategy
             if strat == stratkey]
        if len (hyps) > 1:
            spawn ((None, all_hyps), 'all')
        spawn (hyps[0], 'hyp')
        solved = 0
        while True:
            ((nm, strat, k), _, res) = self.wait_parallel_solver ()
            if strat == 'all' and res == 'unsat':
                trace ('  -- hyps all confirmed by %s' % nm)
                break
            elif strat == 'hyp' and res == 'sat':
                trace ('  -- hyp refuted by %s' % nm)
                break
            elif strat == 'hyp' and res == 'unsat':
                ks = [(solver.name, strat, k)
                      for (solver, strat) in self.strategy]
                self.close_parallel_solvers (ks,
                                             reason = 'hyp shown unsat')
                solved += 1
                if solved < len (hyps):
                    spawn (hyps[solved], 'hyp')
                else:
                    trace ('  - hyps confirmed individually')
                    break
            if not self.parallel_solvers:
                res = 'timeout'
                trace ('  - all solvers timed out or failed.')
                break
        self.close_parallel_solvers (reason = ('checked %r' % res))
        return (res, k)

    def parallel_test_hyps (self, hyps, env, model = None):
        (res, k) = self.parallel_check_hyps (hyps, env, model)
        return (res == 'unsat', k, res)

    def slow_solver_multisat (self, hyps, model = None, timeout = 300):
        trace ('multisat check.')
        start = time.time ()

        cmds = []
        for hyp in hyps:
            cmds.extend (['(assert %s)' % hyp, '(check-sat)'])
            if model != None:
                cmds.append (self.fetch_model_request ())
        (proc, output) = self.exec_slow_solver (cmds, timeout = timeout)

        assert hyps
        for (i, hyp) in enumerate (hyps):
            trace ('multisat checking %s' % hyp)
            response = output.readline ().strip ()
            if response == 'sat':
                if model != None:
                    model.clear ()
                    most_sat = hyps[: i + 1]
                    assert self.fetch_model_response (model,
                                                      stream = output)
            else:
                self.solver = None
                if i == 0 and response == 'unsat':
                    self.send ('(assert (not %s))' % hyp)
                if i > 0:
                    if response != 'unsat':
                        trace ('conversation problem:')
                        trace ('multisat got %r' % response)
                    response = 'sat'
                break

        if model:
            assert self.check_model (most_sat, model)

        end = time.time ()
        trace ('multisat final result: %r after %s' % (response,
                                                       run_time (end - start, proc)))
        output.close ()

        return response

    def fetch_model_request (self):
        vs = self.model_vars
        exprs = self.model_exprs

        trace ('will fetch model%s for %d vars and %d compound exprs.'
               % (self.name_ext, len (vs), len (exprs)))

        vs2 = tuple (vs) + tuple ([nm for (nm, typ) in exprs.values ()])
        return '(get-value (%s))' % ' '.join (vs2)

    def fetch_model_response (self, model, stream = None, recursion = False):
        if stream == None:
            stream = self.online_solver.stdout
        values = get_s_expression (stream,
                                   'fetch_model_response')
        if values == None:
            trace ('Failed to fetch model!')
            return None

        expected_set = set (list (self.model_vars)
                            + [nm for (nm, typ) in self.model_exprs.values ()])
        malformed = [v for v in values if len (v) != 2
                     or v[0] not in expected_set]
        if malformed:
            trace ('bad model response components:')
            for v in malformed:
                trace (repr (v))
            return None

        filt_values = [(nm, v) for (nm, v) in values
                       if type (v) == str or '_' in v
                       if set (v) != set (['?'])]
        dropped = len (values) - len (filt_values)
        if dropped:
            trace ('Dropped %d of %d values' % (dropped, len (values)))
            if recursion:
                trace (' .. aborting recursive attempt.')
                return None

        abbrvs = [(sexp, name) for (sexp, (name, typ))
                  in self.model_exprs.iteritems ()]

        r = make_model (filt_values, model, abbrvs)
        if dropped:
            model[('IsIncomplete', None)] = True
        return r

    def get_arbitrary_vars (self, typ):
        self.arbitrary_vars.setdefault (typ, [])
        vs = self.arbitrary_vars[typ]
        def add ():
            v = self.add_var ('arbitary-var', typ, kind = 'Aux')
            vs.append (v)
            return v
        import itertools
        return itertools.chain (vs, itertools.starmap (add,
                                                       itertools.repeat ([])))

    def force_model_accuracy_hyps (self):
        if len (self.model_exprs) == self.last_model_acc_hyps[0]:
            return self.last_model_acc_hyps[1]
        words = set ()
        for (var_nm, typ) in self.model_exprs.itervalues ():
            if typ.kind == 'Word':
                s = '((_ extract %d %d) %s)' % (typ.num - 1,
                                                typ.num - 2, var_nm)
                words.add (s)
            elif typ == syntax.boolT:
                s = '(ite %s #b10 #b01)' % var_nm
                words.add (s)
            else:
                assert not 'model acc type known', typ
        hyps = []
        w2T = syntax.Type ('Word', 2)
        arb_vars = self.get_arbitrary_vars (w2T)
        while words:
            while len (words) < 4:
                words.add (arb_vars.next ())
            [a, b, c, d] = [words.pop () for x in range (4)]
            x = arb_vars.next ()
            y = arb_vars.next ()
            hyps.append (('(word2-xor-scramble %s)'
                          % ' '.join ([a, x, b, c, y, d]), None))
        self.last_model_acc_hyps = (len (self.model_exprs), hyps)
        return hyps

    def check_model_iteration (self, hyps, state, (res, model)):
        """process an iteration of checking a model. the solvers
        sometimes give partially bogus models, which we need to
        check for.
        the state at any time is (confirmed, test, cand_model, solvs)
        We build additional hypotheses (e.g. x = 0) from models.
        The 'confirmed' additional hyps have been shown sat together
        with the original hyps, and 'test' are under test this
        iteration. If the test is true, 'cand_model' will be
        confirmed to be a valid (possibly incomplete) model.
        We may prune a model down to an incomplete one to try to
        find a valid part. The 'solvs' are solvers which have yet
        to have a model tested (as candidate) from the current
        'confirmed' hyps."""
        if state == None:
            test = []
            confirmed = hyps
            assert res == 'sat'
            cand_model = None
            solvs = self.model_strategy
        else:
            (confirmed, test, cand_model, solvs) = state

        if cand_model and res == 'sat':
            if ('IsIncomplete', None) not in cand_model:
                return ('Result', cand_model)

        if res == 'sat':
            if set (test) - set (confirmed):
                # confirm experiment
                confirmed = sorted (set (confirmed + test))
                # progress was made, reenable all solvers
                solvs = solvs + [s for s in self.model_strategy
                                 if s not in solvs]
        elif res == 'unsat' and not test:
            printout ("WARNING: inconsistent sat/unsat.")
            inconsistent_hyps.append ((self, hyps, confirmed))
            return ('Abort', None)
        else:
            # since not sat, ignore model contents
            model = None

        # the candidate model wasn't confirmed, but might we
        # learn more by reducing it?
        if cand_model and res != 'sat':
            reduced = self.reduce_model (cand_model, hyps)
            r_hyps = get_model_hyps (reduced, self)
            solv = (solvs + self.model_strategy)[0]
            if set (r_hyps) - set (confirmed):
                return ('Continue', (solv, confirmed + r_hyps,
                        (confirmed, r_hyps, None, solvs)))

        # ignore the candidate model now, and try to continue with
        # the most recently returned model. that expires the solver
        # that produced this model from solvs
        solvs = solvs[1:]
        if not model and not solvs:
            # out of options
            return ('Abort', None)
        solv = (solvs + self.model_strategy)[0]

        if model:
            test_hyps = get_model_hyps (model, self)
        else:
            model = None
            test_hyps = []
        return ('Continue', (solv, confirmed + test_hyps,
                (confirmed, test_hyps, model, solvs)))

    def check_model (self, hyps, model):
        orig_model = model
        state = None
        arg = ('sat', dict (model))
        while True:
            res = self.check_model_iteration (hyps, state, arg)
            (kind, details) = res
            if kind == 'Abort':
                return False
            elif kind == 'Result':
                orig_model.clear ()
                orig_model.update (details)
                return True
            assert kind == 'Continue'
            (solv, test_hyps, state) = details
            m = {}
            res = self.hyps_sat_raw (test_hyps, model = m,
                                     force_solv = solv, recursion = True)
            arg = (res, m)

    def reduce_model (self, model, hyps):
        all_hyps = hyps + [h for (h, _) in self.assertions]
        all_hyps = map (parse_s_expression, all_hyps)
        m = reduce_model (model, self, all_hyps)
        trace ('reduce model size: %d --> %d' % (len (model), len (m)))
        return m

    def fetch_model (self, model, recursion = False):
        try:
            self.write (self.fetch_model_request ())
        except IOError, e:
            raise ConversationProblem ('fetch-model', 'IOError')
        return self.fetch_model_response (model, recursion = recursion)

    def get_unsat_core (self):
        res = self.prompt_s_expression_inner ('(get-unsat-core)')
        if res == None:
            return None
        if [s for s in res if type (s) != str]:
            raise ConversationProblem ('(get-unsat-core)', res)
        return res

    def check_hyp (self, hyp, env, model = None, force_solv = False,
                   hyp_name = None):
        hyp = smt_expr (hyp, env, self)
        print 'check_hyp:'
        print hyp
        force_solv = 'Slow'
        return self.check_hyp_raw (hyp, model = model,
                                   force_solv = force_solv, hyp_name = hyp_name)

    def test_hyp (self, hyp, env, model = None, force_solv = False,
                  catch = False, hyp_name = None):
        if catch:
            try:
                res = self.check_hyp (hyp, env, model = model,
                                      force_solv = force_solv,
                                      hyp_name = hyp_name)
            except SolverFailure, e:
                return False
        else:
            res = self.check_hyp (hyp, env, model = model,
                                  force_solv = force_solv, hyp_name = hyp_name)
        return res == 'unsat'

    def assert_fact_smt (self, fact, unsat_tag = None):
        self.assertions.append ((fact, unsat_tag))
        if unsat_tag and self.unsat_cores:
            name = 'assert%d' % len (self.assertions)
            self.send ('(assert (! %s :named %s))' % (fact, name),
                       is_model = False)
        else:
            self.send ('(assert %s)' % fact)

    def assert_fact (self, fact, env, unsat_tag = None):
        fact = smt_expr (fact, env, self)
        self.assert_fact_smt (fact, unsat_tag = unsat_tag)

    def get_smt_derived_oper (self, name, n):
        if (name, n) in self.smt_derived_ops:
            return self.smt_derived_ops[(name, n)]
        if n != 1:
            m = n / 2
            top = '((_ extract %d %d) x)' % (n - 1, m)
            bot = '((_ extract %d 0) x)' % (m - 1)
            top_app = '(%s %s)' % (self.get_smt_derived_oper (
                name, n - m), top)
            top_appx = '((_ zero_extend %d) %s)' % (m, top_app)
            bot_app = '(%s %s)' % (self.get_smt_derived_oper (
                name, m), bot)
            bot_appx = '((_ zero_extend %d) %s)' % (n - m, bot_app)
        if name == 'CountLeadingZeroes':
            fname = 'bvclz_%d' % n
        elif name == 'WordReverse':
            fname = 'bvrev_%d' % n
        else:
            assert not 'name understood', (name, n)
        fname = self.smt_name (fname, kind = 'Fun')

        if name == 'CountLeadingZeroes' and n == 1:
            self.send ('(define-fun %s ((x (_ BitVec 1)))' % fname
                       + ' (_ BitVec 1) (ite (= x #b0) #b1 #b0))')
        elif name == 'CountLeadingZeroes':
            self.send (('(define-fun %s ((x (_ BitVec %d)))'
                        + ' (_ BitVec %d) (ite (= %s %s)'
                        + ' (bvadd %s %s) %s))')
                       % (fname, n, n, top, smt_num (0, n - m),
                       bot_appx, smt_num (m, n), top_appx))
        elif name == 'WordReverse' and n == 1:
            self.send ('(define-fun %s ((x (_ BitVec 1)))' % fname
                       + ' (_ BitVec 1) x)')
        elif name == 'WordReverse':
            self.send (('(define-fun %s ((x (_ BitVec %d)))'
                        + ' (_ BitVec %d) (concat %s %s))')
                       % (fname, n, n, bot_app, top_app))
        else:
            assert not True
        self.smt_derived_ops[(name, n)] = fname
        return fname

        # this is how you would test it
        num = random.randrange (0, 2 ** n)
        clz = len (bin (num + (2 ** n))[3:].split('1')[0])
        assert self.check_hyp_raw ('(= (bvclz_%d %s) %s)' %
                                   (n, smt_num (num, n), smt_num (clz, n))) == 'unsat'
        num = num >> random.randrange (0, n)
        clz = len (bin (num + (2 ** n))[3:].split('1')[0])
        assert self.check_hyp_raw ('(= (bvclz_%d %s) %s)' %
                                   (n, smt_num (num, n), smt_num (clz, n))) == 'unsat'

    def cache_large_expr (self, s, name, typ):
        if s in self.cached_exprs:
            return self.cached_exprs[s]
        if len (s) < 80:
            return s
        name2 = self.add_def (name, mk_smt_expr (s, typ), {})
        self.cached_exprs[s] = name2
        self.cached_exprs[(name2, 'IsCachedExpr')] = True
        return name2

    def note_ptr (self, p_s):
        if p_s in self.ptrs:
            p = self.ptrs[p_s]
        else:
            p = self.add_def ('ptr', mk_smt_expr (p_s, syntax.arch.word_type), {})
            self.ptrs[p_s] = p
        return p

    def add_pvalids (self, htd_s, typ, p_s, kind, recursion = False):
        print 'pvalids:'
        print p_s
        htd_sexp = parse_s_expression (htd_s)
        if htd_sexp[0] == 'ite':
            [cond, l, r] = map (flat_s_expression, htd_sexp[1:])
            return '(ite %s %s %s)' % (cond,
                                       self.add_pvalids (l, typ, p_s, kind),
                                       self.add_pvalids (r, typ, p_s, kind))

        pvalids = self.pvalids
        if htd_s not in pvalids and not recursion:
            [_, _, rodata_ptrs] = rodata
            if not rodata_ptrs:
                rodata_ptrs = []
            for (r_addr, r_typ) in rodata_ptrs:
                # rv64_changed to word64T, should it
                # be rodata_chunk_type instead?
                r_addr.typ = syntax.arch.word_type
                r_addr_s = smt_expr (r_addr, {}, None)
                print 'raddr:'
                print type(r_addr)
                print r_addr
                print r_typ
                print r_addr_s
                var = self.add_pvalids (htd_s, ('Type', r_typ),
                                        r_addr_s, 'PGlobalValid',
                                        recursion = True)
                self.assert_fact_smt (var)

        print 'nodeptr:'
        print p_s
        if p_s == '#x7b38':
            assert False

        #print r_addr
        #print r_typ
        p = self.note_ptr (p_s)

        trace ('adding pvalid with type %s' % (typ, ))

        if htd_s in pvalids and (typ, p, kind) in pvalids[htd_s]:
            return pvalids[htd_s][(typ, p, kind)]
        else:
            var = self.add_var ('pvalid', boolT)
            pvalids.setdefault (htd_s, {})
            others = pvalids[htd_s].items()
            pvalids[htd_s][(typ, p, kind)] = var

            def smtify (((typ, p, kind), var)):
                return (typ, kind, mk_smt_expr (p, syntax.arch.word_type),
                        mk_smt_expr (var, boolT))
            pdata = smtify (((typ, p, kind), var))
            (_, _, p, pv) = pdata
            impl_al = mk_implies (pv, mk_align_valid_ineq (typ, p))
            self.assert_fact (impl_al, {})
            for val in others:
                kinds = [val[0][2], pdata[1]]
                if ('PWeakValid' in kinds and
                        'PGlobalValid' not in kinds):
                    continue
                ass = pvalid_assertion1 (pdata, smtify (val))
                ass_s = smt_expr (ass, None, None)
                self.assert_fact_smt (ass_s, unsat_tag =
                                      ('PValid', 1, var, val[1]))
                ass = pvalid_assertion2 (pdata, smtify (val))
                ass_s = smt_expr (ass, None, None)
                self.assert_fact_smt (ass_s,
                                      ('PValid', 2, var, val[1]))

            trace ('Now %d related pvalids' % len(pvalids[htd_s]))
            return var

    def get_imm_basis_mems (self, m, accum):
        #print m
        #print accum
        #print m[0]
        #print type(m)

        if m[0] == 'ite':
            (_, c, l, r) = m
            self.get_imm_basis_mems (l, accum)
            self.get_imm_basis_mems (r, accum)
        elif m[0] in ['store-word32', 'store-word8', 'store-word64']:
            (_, m, p, v) = m
            print m
            #assert False
            self.get_imm_basis_mems (m, accum)
        elif type (m) == tuple:
            assert not 'mem construction understood', m
        elif (m, 'IsCachedExpr') in self.cached_exprs:
            self.get_imm_basis_mems (self.defs[m], accum)
        else:
            assert type (m) == str
            accum.add (m)

    def get_basis_mems (self, m):
        # the obvious implementation requires exponential exploration
        # and may overrun the recursion limit.
        mems = set ()
        processed_defs = set ()

        self.get_imm_basis_mems (m, mems)
        while True:
            proc = [m for m in mems if m in self.defs
                    if m not in processed_defs]
            if not proc:
                return mems
            for m in proc:
                self.get_imm_basis_mems (self.defs[m], mems)
                processed_defs.add (m)

    def add_split_mem_var (self, addr, nm, typ, mem_name = None):
        assert typ == builtinTs['Mem']
        bot_mem = self.add_var (nm + '_bot', typ, mem_name = mem_name)
        top_mem = self.add_var (nm + '_top', typ, mem_name = mem_name)
        self.stack_eqs[('StackEqImpliesCheck', top_mem)] = None
        return ('SplitMem', addr, top_mem, bot_mem)

    def add_implies_stack_eq (self, sp, s1, s2, env):
        k = ('ImpliesStackEq', sp, s1, s2)
        if k in self.stack_eqs:
            return self.stack_eqs[k]
        addr = self.add_var ('stack-eq-witness', syntax.arch.word_type)
        self.assert_fact_smt(
            '(= (bvand %s %s) %s)' % (
                addr,
                syntax.arch.smt_stackeq_mask,
                syntax.arch.smt_native_zero
            )
        )
        sp_smt = smt_expr (sp, env, self)
        self.assert_fact_smt ('(bvule %s %s)' % (sp_smt, addr))
        ptr = mk_smt_expr (addr, syntax.arch.word_type)
        eq = syntax.mk_eq (syntax.mk_memacc (s1, ptr, syntax.arch.word_type),
                           syntax.mk_memacc (s2, ptr, syntax.arch.word_type))
        stack_eq = self.add_def ('stack-eq', eq, env)
        self.stack_eqs[k] = stack_eq
        return stack_eq

    def get_stack_eq_implies (self, split, st_top, other):
        if other[0] == 'SplitMem':
            [_, split2, top2, bot2] = other
            rhs = top2
            cond = '(bvule %s %s)' % (split2, split)
        else:
            rhs = other
            cond = 'true'
        self.note_model_expr ('(= %s %s)' % (st_top, rhs), boolT)
        mems = set ()
        self.get_imm_basis_mems (parse_s_expression (st_top), mems)
        assert len (mems) == 1, mems
        [st_top_base] = list (mems)
        k = ('StackEqImpliesCheck', st_top_base)
        assert k in self.stack_eqs, k
        assert self.stack_eqs[k] in [None, rhs], [k,
                                                  self.stack_eqs[k], rhs]
        self.stack_eqs[k] = rhs
        return '(=> %s (= %s %s))' % (cond, st_top, rhs)

    def get_token (self, string):
        if ('Token', string) not in self.tokens:
            n = len (self.tokens) + 1
            v = self.add_def ("token_%s" % string,
                              syntax.mk_num (n, token_smt_typ), {})
            self.tokens[('Token', string)] = v
            self.tokens[('Val', self.defs[v])] = string
        return self.tokens[('Token', string)]

    def note_mem_dom (self, p, d, md):
        self.doms.add ((p, d, md))

    def note_model_expr (self, sexpr, typ):
        psexpr = parse_s_expression (sexpr)
        if psexpr not in self.model_exprs:
            s = ''.join ([c for c in sexpr if c not in " ()"])
            s = s[:20]
            smt_expr = mk_smt_expr (sexpr, typ)
            v = self.add_def ('query_' + s, smt_expr, {})
            self.model_exprs[psexpr] = (v, typ)

    def add_pvalid_dom_assertions (self):
        if not self.doms:
            return
        if cheat_mem_doms:
            return
        bits = syntax.arch.word_size
        dom = iter (self.doms).next ()[1]

        pvs = [(var, (p, typ.size ()))
               for env in self.pvalids.itervalues ()
               for ((typ, p, kind), var) in env.iteritems ()]
        pvs += [('true', (smt_num (start, bits), (end - start) + 1))
                for (start, end) in sections.itervalues ()]

        pvalid_doms = (pvs, set (self.doms))
        print pvalid_doms
        assert False

        if self.pvalid_doms == pvalid_doms:
            return

        trace ('PValid/Dom complexity: %d, %d' % (len (pvalid_doms[0]),
                                                  len (pvalid_doms[1])))
        for (var, (p, sz)) in pvs:
            if sz > len (self.doms) * (bits / 8):
                for (q, _, md) in self.doms:
                    left = '(bvule %s %s)' % (p, q)
                    right = ('(bvule %s (bvadd %s %s))'
                             % (q, p, smt_num (sz - 1, bits)))
                    lhs = '(and %s %s)' % (left, right)
                    self.assert_fact_smt ('(=> %s %s)'
                                          % (lhs, md))
            else:
                vs = ['(mem-dom (bvadd %s %s) %s)'
                      % (p, smt_num (i, bits), dom)
                      for i in range (sz)]
                self.assert_fact_smt ('(=> %s (and %s))'
                                      % (var, ' '.join (vs)))

        self.pvalid_doms = pvalid_doms

    def narrow_unsat_core (self, solver, asserts):
        process = subprocess.Popen (solver[1],
                                    stdin = subprocess.PIPE, stdout = subprocess.PIPE,
                                    preexec_fn = preexec (solver[2]))
        self.write_solv_script (process.stdin, [], solver = solver,
                                only_if_is_model = True)
        asserts = list (asserts)
        for (i, (ass, tag)) in enumerate (asserts):
            process.stdin.write ('(assert (! %s :named uc%d))\n'
                                 % (ass, i))
        process.stdin.write ('(check-sat)\n(get-unsat-core)\n')
        process.stdin.close ()
        try:
            res = get_s_expression (process.stdout, '(check-sat)')
            core = get_s_expression (process.stdout,
                                     '(get-unsat-core)')
        except ConversationProblem, e:
            return asserts
        trace ('got response %r from %s' % (res, solver[0]))
        if res != 'unsat':
            return asserts
        for s in core:
            assert s.startswith ('uc')
        return set ([asserts[int (s[2:])] for s in core])

    def unsat_core_loop (self, asserts):
        asserts = set (asserts)

        orig_num_asserts = len (asserts) + 1
        while len (asserts) < orig_num_asserts:
            orig_num_asserts = len (asserts)
            trace ('Entering unsat_core_loop, %d asserts.'
                   % orig_num_asserts)
            for solver in unsat_solver_loop:
                asserts = self.narrow_unsat_core (solver,
                                                  asserts)
                trace (' .. now %d asserts.' % len (asserts))
        return set ([tag for (_, tag) in asserts])

    def unsat_core_with_loop (self, hyps, env):
        unsat_core = []
        hyps = [(smt_expr (hyp, env, self), tag) for (hyp, tag) in hyps]
        try:
            res = self.hyps_sat_raw (hyps, unsat_core = unsat_core)
        except ConversationProblem, e:
            res = 'unsat'
            unsat_core = []
        if res != 'unsat':
            return res
        if unsat_core == []:
            core = list (hyps) + list (self.assertions)
        else:
            unsat_core = set (unsat_core)
            core = [(ass, tag) for (ass, tag) in hyps
                    if tag in unsat_core] + [(ass, tag)
                                             for (ass, tag) in self.assertions
                                             if tag in unsat_core]
        return self.unsat_core_loop (core)

def merge_envs (envs, solv):
    var_envs = {}
    for (pc, env) in envs:
        pc_str = smt_expr (pc, env, solv)
        for (var, s) in env.iteritems ():
            var_envs.setdefault(var, {})
            var_envs[var].setdefault(s, [])
            var_envs[var][s].append (pc_str)

    env = {}
    for var in var_envs:
        its = var_envs[var].items()
        (v, _) = its[-1]
        for i in range(len(its) - 1):
            (v2, pc_strs) = its[i]
            if len (pc_strs) > 1:
                pc_str = '(or %s)' % (' '.join (pc_strs))
            else:
                pc_str = pc_strs[0]
            v = smt_ifthenelse (pc_str, v2, v, solv)
        env[var] = v
    return env

def fold_assoc_balanced (f, xs):
    if len (xs) >= 4:
        i = len (xs) / 2
        lhs = fold_assoc_balanced (f, xs[:i])
        rhs = fold_assoc_balanced (f, xs[i:])
        return f (lhs, rhs)
    else:
        return foldr1 (f, xs)

def merge_envs_pcs (pc_envs, solv):
    pc_envs = [(pc, env) for (pc, env) in pc_envs if pc != false_term]
    if pc_envs == []:
        path_cond = false_term
    else:
        pcs = list (set ([pc for (pc, _) in pc_envs]))
        path_cond = fold_assoc_balanced (mk_or, pcs)
    env = merge_envs (pc_envs, solv)

    return (path_cond, env, len (pc_envs) > 1)

def hash_test_hyp (solv, hyp, env, cache):
    assert hyp.typ == boolT
    s = smt_expr (hyp, env, solv)
    if s in cache:
        return cache[s]
    v = solv.test_hyp (mk_smt_expr (s, boolT), {})
    cache[s] = v
    return v

def hash_test_hyp_fast (solv, hyp, env, cache):
    assert hyp.typ == boolT
    s = smt_expr (hyp, env, solv)
    return cache.get (s)

paren_re = re.compile (r"(\(|\))")

def parse_s_expressions (ss):
    #print ss
    bits = [bit for s in ss for split1 in paren_re.split (s)
            for bit in split1.split ()]
    def group (n):
        if bits[n] != '(':
            return (n + 1, bits[n])
        xs = []
        n = n + 1
        while bits[n] != ')':
            (n, x) = group (n)
            xs.append (x)
        return (n + 1, tuple (xs))
    (n, v) = group (0)
    assert n == len (bits), ss
    return v

def parse_s_expression (s):
    return parse_s_expressions ([s])

def smt_to_val (s, toplevel = None):
    stores = []
    if len (s) == 3 and s[0] == '_' and s[1][:2] == 'bv':
        ln = int (s[2])
        n = int (s[1][2:])
        return syntax.mk_num (n, ln)
    elif type (s) == tuple:
        assert type (s) != tuple, s
    elif s.startswith ('#b'):
        return syntax.mk_num (int (s[2:], 2), len (s) - 2)
    elif s.startswith ('#x'):
        return syntax.mk_num (int (s[2:], 16), (len (s) - 2) * 4)
    elif s == 'true':
        return true_term
    elif s == 'false':
        return false_term
    assert not 'smt_to_val: smt expr understood', s

last_primitive_model = [0]

def eval_mem_name_sexp (m, defs, sexp):
    import search
    while True:
        if sexp[0] == 'ite':
            (_, c, l, r) = sexp
            b = search.eval_model (m, c)
            if b == syntax.true_term:
                sexp = l
            elif b == syntax.false_term:
                sexp = r
            else:
                assert not 'eval_model result understood'
        elif sexp[0] == 'store-word32':
            (_, sexp, p2, v2) = sexp
        else:
            assert type (sexp) == str
            if sexp in defs:
                sexp = defs[sexp]
            else:
                return sexp

def eval_mem_names (m, defs, mem_names):
    init_mem_names = {}
    for (m_var, naming) in mem_names.iteritems ():
        if type (naming) == tuple:
            (nm, sexp) = naming
            pred = eval_mem_name_sexp (m, defs, sexp)
            init_mem_names[m_var] = (nm, pred)
        elif type (naming) == str:
            m[m_var] = ((naming, ), {})
        else:
            assert not 'naming kind understood', naming
    stack = init_mem_names.keys ()
    while stack:
        m_var = stack.pop ()
        if m_var in m:
            continue
        (nm, pred) = init_mem_names[m_var]
        if pred in m:
            (pred_chain, _) = m[pred]
            m[m_var] = (pred_chain + (nm,), {})
        else:
            stack.extend ([m_var, pred])

def make_model (sexp, m, abbrvs = [], mem_defs = {}):
    last_primitive_model[0] = (sexp, abbrvs)
    m_pre = {}
    try:
        for (nm, v) in sexp:
            if type (nm) == tuple and type (v) == tuple:
                return False
            m_pre[nm] = smt_to_val (v)
        for (abbrv_sexp, nm) in abbrvs:
            if nm in m_pre:
                m_pre[abbrv_sexp] = m_pre[nm]
    except IndexError, e:
        print 'Error with make_model'
        print sexp
        raise e
    # only commit to adjusting m now we know we'll succeed
    m.update (m_pre)
    last_10_models.append (m_pre)
    last_10_models[:-10] = []
    return True

def get_model_hyps (model, solv):
    return ['(= %s %s)' % (flat_s_expression (x), smt_expr (v, {}, solv))
            for (x, v) in model.iteritems ()
            if x != ('IsIncomplete', None)]

def add_key_model_vs (sexpr, m, solv, vs):
    if sexpr[0] == '=>':
        (_, lhs, rhs) = sexpr
        add_key_model_vs (('or', ('not', lhs), rhs), m, solv, vs)
    elif sexpr[0] == 'or':
        vals = [(x, get_model_val (x, m)) for x in sexpr[1:]]
        true_vals = [x for (x, v) in vals if v == syntax.true_term]
        if not true_vals:
            for x in sexpr[1:]:
                add_key_model_vs (x, m, solv, vs)
        elif len (true_vals) == 1:
            add_key_model_vs (true_vals[0], m, solv, vs)
        else:
            vs.add (sexpr)
    elif sexpr[0] == 'and':
        vals = [(x, get_model_val (x, m)) for x in sexpr[1:]]
        false_vals = [x for (x, v) in vals if v == syntax.false_term]
        if not false_vals:
            for x in sexpr[1:]:
                add_key_model_vs (x, m, solv, vs)
        elif len (false_vals) == 1:
            add_key_model_vs (false_vals[0], m, solv, vs)
        else:
            vs.add (sexpr)
    elif sexpr[0] == 'ite':
        (_, p, x, y) = sexpr
        v = get_model_val (p, m)
        add_key_model_vs (p, m, solv, vs)
        if v == syntax.true_term:
            add_key_model_vs (x, m, solv, vs)
        if v == syntax.false_term:
            add_key_model_vs (y, m, solv, vs)
    elif type (sexpr) == str:
        if sexpr not in vs:
            vs.add (sexpr)
            if sexpr in solv.defs:
                add_key_model_vs (solv.defs[sexpr], m, solv, vs)
    else:
        for x in sexpr[1:]:
            add_key_model_vs (x, m, solv, vs)

def get_model_val (sexpr, m, toplevel = None):
    import search
    try:
        return search.eval_model (m, sexpr)
    except AssertionError, e:
        # this is awful, but happens sometimes because we're
        # evaluating in incomplete models
        return None

last_model_to_reduce = [0]

def reduce_model (m, solv, hyps):
    last_model_to_reduce[0] = (m, solv, hyps)
    vs = set ()
    for hyp in hyps:
        add_key_model_vs (hyp, m, solv, vs)
    return dict ([(k, m[k]) for k in m if k in vs])

def flat_s_expression (s):
    if type(s) == tuple:
        return '(' + ' '.join (map (flat_s_expression, s)) + ')'
    else:
        return s

pvalid_type_map = {}

def fun_cond_test (fun, unsats = None):
    if unsats == None:
        unsats = []
    ns = [n for n in fun.reachable_nodes (simplify = True)
          if fun.nodes[n].get_conts ()[1:] == ['Err']
          if fun.nodes[n].cond != syntax.false_term]
    if not ns:
        return
    solv = Solver ()
    for n in ns:
        vs = syntax.get_node_rvals (fun.nodes[n])
        env = dict ([((nm, typ), solv.add_var (nm, typ))
                     for (nm, typ) in vs.iteritems ()])
        r = solv.test_hyp (syntax.mk_not (fun.nodes[n].cond), env)
        if r == True:
            unsats.append ((fun.name, n))
    return unsats

def cond_tests ():
    unsats = []
    from target_objects import functions
    [fun_cond_test (fun, unsats) for (f, fun) in functions.iteritems ()]
    assert not unsats, unsats

#def compile_struct_pvalid ():
#def compile_pvalids ():
def quick_test (force_solv = False):
    """quick test that the solver supports the needed features."""
    fs = force_solv
    solv = Solver ()
    solv.assert_fact (true_term, {})
    assert solv.check_hyp (false_term, {}, force_solv = fs) == 'sat'
    assert solv.check_hyp (true_term, {}, force_solv = fs) == 'unsat'
    v = syntax.mk_var ('v', word32T)
    z = syntax.mk_word32 (0)
    env = {('v', word32T): solv.add_var ('v', word32T)}
    solv.assert_fact (syntax.mk_eq (v, z), env)
    m = {}
    assert solv.check_hyp (false_term, {}, model = m,
                           force_solv = fs) == 'sat'
    assert m.get ('v') == z, m

def test ():
    solverlist = find_solverlist_file ()
    print 'Loaded solver list from %s' % solverlist
    quick_test ()
    quick_test (force_solv = 'Slow')
    print 'Solver self-test successful'

if __name__ == "__main__":
    import sys, target_objects
    if sys.argv[1:] == ['testq']:
        target_objects.tracer[0] = lambda x, y: ()
        test ()
    elif sys.argv[1:] == ['test']:
        test ()
    elif sys.argv[1:] == ['ctest']:
        cond_tests ()


