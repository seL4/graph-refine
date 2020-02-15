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

from syntax import mk_var

from target_objects import functions, trace, pairings, pre_pairings, printout
import target_objects

import re

reg_aliases = {'sb': 'r9', 'sl': 'r10', 'fp': 'r11', 'ip': 'r12',
               'sp': 'r13', 'lr': 'r14', 'pc': 'r15'}

reg_set = set (['r%d' % i for i in range (16)])

inst_split_re = re.compile('[_,]*')
crn_re = re.compile('cr[0123456789][0123456789]*')
pn_re = re.compile('p[0123456789][0123456789]*')
def split_inst_name_regs (nm):
    #assert False
    bits = inst_split_re.split (nm)
    fin_bits = []
    regs = []
    if len (bits) > 1 and pn_re.match (bits[1]):
        bits[1] = bits[1][1:]
    for bit in bits:
        bit2 = bit.lower ()
        bit2 = reg_aliases.get (bit, bit)
        if crn_re.match (bit2):
            assert bit2.startswith ('cr')
            bit2 = 'c' + bit2[2:]
        if bit2 in reg_set or bit2.startswith ('%'):
            regs.append (bit2)
            fin_bits.append ('argv%d' % (len (regs)))
        else:
            fin_bits.append (bit2)
    return (regs, '_'.join (fin_bits))

bin_globs = [('mem', syntax.builtinTs['Mem'])]
asm_globs = [('Mem', syntax.builtinTs['Mem'])]

def mk_fun (nm, word_args, ex_args, word_rets, ex_rets, globs):
    """wrapper for making a syntax.Function with standard args/rets."""
    #assert False
    #rv64_hack
    return syntax.Function (nm,
                            [(nm, syntax.word64T) for nm in word_args] + ex_args + globs,
                            [(nm, syntax.word64T) for nm in word_rets] + ex_rets + globs)

instruction_fun_specs = {
    'mcr' : ("impl'mcr", ["I"]),
    'mcr2' : ("impl'mcr", ["I"]),
    'mcrr' : ("impl'mcrr", ["I", "I"]),
    'mcrr2' : ("impl'mcrr", ["I", "I"]),
    'mrc': ("impl'mrc", ["O"]),
    'mrc2': ("impl'mrc", ["O"]),
    'mrrc': ("impl'mrrc", ["O", "O"]),
    'mrrc2': ("impl'mrrc", ["O", "O"]),
    'dsb': ("impl'dsb", []),
    'dmb': ("impl'dmb", []),
    'isb': ("impl'isb", []),
    'wfi': ("impl'wfi", []),
}

instruction_name_aliases = {
    'isb_sy': 'isb',
    'dmb_sy': 'dmb',
    'dsb_sy': 'dsb',
}

def add_impl_fun (impl_fname, regspecs):
    #assert  False
    l_fname = 'l_' + impl_fname
    r_fname = 'r_' + impl_fname
    if l_fname in functions:
        return
    assert r_fname not in functions

    ident_v = ("inst_ident", syntax.builtinTs['Token'])

    inps = [s for s in regspecs if s == 'I']
    inps = ['reg_val%d' % (i + 1) for (i, s) in enumerate (inps)]
    rets = [s for s in regspecs if s == 'O']
    rets = ['ret_val%d' % (i + 1) for (i, s) in enumerate (rets)]
    l_fun = mk_fun (l_fname, inps, [ident_v], rets, [], bin_globs)
    r_fun = mk_fun (r_fname, inps, [ident_v], rets, [], bin_globs)
    inp_eqs = [((mk_var (nm, typ), 'ASM_IN'), (mk_var (nm, typ), 'C_IN'))
               for (nm, typ) in l_fun.inputs]
    inp_eqs += [((logic.mk_rodata (mk_var (nm, typ)), 'ASM_IN'),
                 (syntax.true_term, 'C_IN')) for (nm, typ) in bin_globs]
    out_eqs = [((mk_var (nm, typ), 'ASM_OUT'), (mk_var (nm, typ), 'C_OUT'))
               for (nm, typ) in l_fun.outputs]
    out_eqs += [((logic.mk_rodata (mk_var (nm, typ)), 'ASM_OUT'),
                 (syntax.true_term, 'C_OUT')) for (nm, typ) in bin_globs]
    pair = logic.Pairing (['ASM', 'C'], {'ASM': l_fname, 'C': r_fname},
                          (inp_eqs, out_eqs))
    assert l_fname not in pairings
    assert r_fname not in pairings
    functions[l_fname] = l_fun
    functions[r_fname] = r_fun
    pairings[l_fname] = [pair]
    pairings[r_fname] = [pair]

inst_addr_re = re.compile('E[0123456789][0123456789]*')
def split_inst_name_addr (instname):
    bits = instname.split('_')
    assert bits, instname
    addr = bits[-1]
    assert inst_addr_re.match (addr), instname
    addr = int (addr[1:], 16)
    return ('_'.join (bits[:-1]), addr)

def mk_bin_inst_spec (fname):
    #rv64_hack
    return
    #print fname
    #assert False
    if not fname.startswith ("instruction'"):
        return
    if functions[fname].entry:
        return
    (_, ident) = fname.split ("'", 1)
    (ident, addr) = split_inst_name_addr (ident)
    (regs, ident) = split_inst_name_regs (ident)
    ident = instruction_name_aliases.get (ident, ident)
    base_ident = ident.split ("_")[0]
    if base_ident not in instruction_fun_specs:
        return
    (impl_fname, regspecs) = instruction_fun_specs[base_ident]
    add_impl_fun (impl_fname, regspecs)
    assert len (regspecs) == len (regs), (fname, regs, regspecs)
    inp_regs = [reg for (reg, d) in zip (regs, regspecs) if d == 'I']
    out_regs = [reg for (reg, d) in zip (regs, regspecs) if d == 'O']
    #print inp_regs
    #print out_regs
    #assert False
    call = syntax.Node ('Call', 'Ret', ('l_' + impl_fname,
                                        [syntax.mk_var (reg, syntax.word32T) for reg in inp_regs]
                                        + [syntax.mk_token (ident)]
                                        + [syntax.mk_var (nm, typ) for (nm, typ) in bin_globs],
                                        [(reg, syntax.word32T) for reg in out_regs] + bin_globs))
    assert not functions[fname].nodes
    functions[fname].nodes[1] = call
    functions[fname].entry = 1

def mk_asm_inst_spec (fname):

    if not fname.startswith ("asm_instruction'"):
        return
    if functions[fname].entry:
        return

    #print fname
    #assert False

    (_, ident) = fname.split ("'", 1)
    (args, ident) = split_inst_name_regs (ident)
    if not all ([arg.startswith ('%') for arg in args]):
        printout ('Warning: asm instruction name: formatting: %r'
                  % fname)
        return
    base_ident = ident.split ("_")[0]
    if base_ident not in instruction_fun_specs:
        return
    (impl_fname, regspecs) = instruction_fun_specs[base_ident]
    add_impl_fun (impl_fname, regspecs)
    (iscs, imems, _) = logic.split_scalar_pairs (functions[fname].inputs)
    (oscs, omems, _) = logic.split_scalar_pairs (functions[fname].outputs)
    call = syntax.Node ('Call', 'Ret', ('r_' + impl_fname,
                                        iscs + [syntax.mk_token (ident)] + imems,
                                        [(v.name, v.typ) for v in oscs + omems]))
    assert not functions[fname].nodes
    functions[fname].nodes[1] = call
    functions[fname].entry = 1

def add_inst_specs (report_problematic = True):
    for f in functions.keys ():
        mk_asm_inst_spec (f)
        mk_bin_inst_spec (f)
    if report_problematic:
        problematic_instructions ()

def problematic_instructions ():
    add_inst_specs (report_problematic = False)
    unhandled = {}
    for f in functions:
        for f2 in functions[f].function_calls ():
            if "instruction'" not in f2:
                continue
            if functions[f2].entry:
                continue
            unhandled.setdefault (f, [])
            unhandled[f].append (f2)
    for f in unhandled:
        printout ('Function %r contains unhandled instructions:' % f)
        printout ('  %s' % unhandled[f])
    return unhandled


