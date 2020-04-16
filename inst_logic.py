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

reg_aliases_armv7 = {'sb': 'r9', 'sl': 'r10', 'fp': 'r11', 'ip': 'r12',
                     'sp': 'r13', 'lr': 'r14', 'pc': 'r15'}

reg_aliases_rv64 = {
    'zero': 'r0',
    'ra': 'r1',
    'sp': 'r2',
    'gp': 'r3',
    'tp': 'r4',
    't0': 'r5',
    't1': 'r6',
    't2': 'r7',
    'fp': 'r8',
    's0': 'r8',
    's1': 'r9',
    'a0': 'r10',
    'a1': 'r11',
    'a2': 'r12',
    'a3': 'r13',
    'a4': 'r14',
    'a5': 'r15',
    'a6': 'r16',
    'a7': 'r17',
    's2': 'r18',
    's3': 'r19',
    's4': 'r20',
    's5': 'r21',
    's6': 'r22',
    's7': 'r23',
    's8': 'r24',
    's9': 'r25',
    's10': 'r26',
    's11': 'r27',
    't3':  'r28',
    't4': 'r29',
    't5': 'r30',
    't6': 'r31'
}

csrs_rv64 = (
    'sstatus',
    'stvec',
    'sip',
    'sie',
    'scounteren',
    'sscratch',
    'sepc',
    'scause',
    'stval',
    'satp',
)

reg_set = set (['r%d' % i for i in range (16)])

reg_set_rv64 = set(['x%d' % i for i in range(32)])

inst_split_re = re.compile('[_,]*')

def split_inst_name_regs_rv64(nm):
    print 'splitinst'
    print nm

    reg_aliases = reg_aliases_rv64
    bits = inst_split_re.split(nm)
    print bits
    fin_bits = []
    regs = []
    print 'bits:'
    print bits
    for i in range(len(bits)):
        if bits[i] in reg_aliases_rv64.keys():
            if bits[i] == 'zero' and bits[0] == 'sfence':
                print bits[i]
                fin_bits.append(bits[i])
                #assert False
            else:
                regs.append(reg_aliases_rv64.get(bits[i]))
                fin_bits.append('-argv%d' % len(regs))

        elif bits[0] == 'ecall':
            fin_bits.append(bits[0])
            regs.append('r10')

            fin_bits.append('-argv%d' % len(regs))

            regs.append('r11')

            fin_bits.append('-argv%d' % len(regs))

            regs.append('r12')

            fin_bits.append('-argv%d' % len(regs))

            regs.append('r13')

            fin_bits.append('-argv%d' % len(regs))

            regs.append('r10')
            fin_bits.append('-ret%d' % len(regs))
#            regs.append('r14')

#            fin_bits.append('-argv%d' % len(regs))

#            regs.append('r15')

#            fin_bits.append('-argv%d' % len(regs))

        elif bits[i] == 'x0' and bits[0] == 'sfence.vma':
            fin_bits.append(bits[i])
            print fin_bits
        elif bits[i] in reg_set_rv64:
            regs.append('r' + bits[i][1:])
            fin_bits.append('-argv%d' % len(regs))
        elif bits[i] in csrs_rv64:
            #regs.append(bits[i])
            fin_bits.append(bits[i])
        elif bits[i].startswith('%'):
            regs.append(bits[i])
            fin_bits.append('-argv%d' % len(regs))
        else:
            fin_bits.append(bits[i])

    print 'dada'
    print regs
    for f in fin_bits:
        if f.startswith('-argv'):
            fin_bits.remove(f)
            fin_bits.append(f)

    print fin_bits
    #print fin_bits
    #print '_'.join(fin_bits)
    return (regs, '_'.join (fin_bits))


crn_re = re.compile('cr[0123456789][0123456789]*')
pn_re = re.compile('p[0123456789][0123456789]*')

def split_inst_name_regs_armv7 (nm):
    reg_aliases = reg_aliases_armv7
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


def split_inst_name_regs(nm):
    if syntax.arch == 'armv7':
        return split_inst_name_regs_armv7(nm)
    elif syntax.arch == 'rv64':
        return split_inst_name_regs_rv64(nm)
    else:
        assert False

bin_globs = [('mem', syntax.builtinTs['Mem'])]
asm_globs = [('Mem', syntax.builtinTs['Mem'])]

def mk_fun (nm, word_args, ex_args, word_rets, ex_rets, globs):
    """wrapper for making a syntax.Function with standard args/rets."""
    #assert False
    #rv64_hack
    if syntax.is_64bit:
        wordT = syntax.word64T
    else:
        wordT = syntax.word32T

    return syntax.Function (nm,
                            [(nm, wordT) for nm in word_args] + ex_args + globs,
                            [(nm, wordT) for nm in word_rets] + ex_rets + globs)

instruction_fun_specs_armv7 = {
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

instruction_fun_specs_rv64 = {

    'fence_i': 	        ("impl'fence_i", []),
    'sfence_vma': 	    ("impl'sfence_vma", []),
    'sfence_vma_zero':  ("impl'sfence_vma_zero", ["I"]),
    'sfence.vma':       ("impl'sfence_vma", []),
    'sfence.vma_x0':    ("impl'sfence_vma_zero", ["I"]),
    'csrr_sip': 	    ("impl'csrr_sip", ["O"]),
    'csrr_sepc':        ("impl'csrr_sepc", ["O"]),
    'csrr_scause':      ("impl'csrr_scause", ["O"]),
    'csrr_sstatus':     ("impl'csrr_sstatus", ["O"]),
    'csrr_sscratch':    ("impl'csrr_sscratch", ["O"]),
    'csrr_stval':       ("impl'csrr_stval", ["O"]),
    'csrr_sbadaddr':    ("impl'csrr_sbadaddr", ["O"]),
    'csrw_sptbr':       ("impl'csrw_sptbr", ["I"]),
    'csrw_stvec':       ("impl'csrw_stvec", ["I"]),
    'csrw_satp':        ("impl'csrw_satp", ["I"]),
    'csrw_sscratch':    ("impl'csrw_sscratch", ["I"]),
    'csrrc_sie':	    ("impl'csrrc_sie", ["O", "I"]),
    'csrrs_sie':	    ("impl'csrrs_sie", ["O", "I"]),
    'csrrw_sscratch':	("impl'csrrw_sscratch", ["O", "I"]),
    'wfi':		        ("impl'wfi", []),
    #'ecall': 	        ("impl'ecall", []),
    'ebreak':           ("impl'ebreak", []),
    'ecall':            ("impl'ecall", ["I", "I", "I", "I", "O"]),
    'rdtime': 	        ("impl'rdtime", ["O"]),
    'unimp':	        ("unimp", []),
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
        print 'skip_add %s' % l_fname
        return

    assert r_fname not in functions

    ident_v = ("inst_ident", syntax.builtinTs['Token'])

    inps = [s for s in regspecs if s == 'I']
    inps = ['reg_val%d' % (i + 1) for (i, s) in enumerate (inps)]
    rets = [s for s in regspecs if s == 'O']
    rets = ['ret_val%d' % (i + 1) for (i, s) in enumerate (rets)]

    print 'addimpl'
    print l_fname
    print r_fname
    print inps
    print rets

    l_fun = mk_fun (l_fname, inps, [ident_v], rets, [], bin_globs)
    r_fun = mk_fun (r_fname, inps, [ident_v], rets, [], bin_globs)

    print l_fun.inputs
    print r_fun.inputs
    print 'kk'

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

    print inp_eqs
    print out_eqs
    print 'kkk'

    assert l_fname not in pairings
    assert r_fname not in pairings
    functions[l_fname] = l_fun
    functions[r_fname] = r_fun
    pairings[l_fname] = [pair]
    pairings[r_fname] = [pair]
    print 'addpairing %s %s' % (l_fname, r_fname)

inst_addr_re_armv7 = re.compile('E[0123456789][0123456789]*')
# Note that the decompiler seems ignore the top 4 bytes which
# are 0xfffffff for rv64. So we just use the least significant
# 4 bytes at the moment. We lock the 0x84xxxxxx addresses.
inst_addr_re_rv64 = re.compile('84[0123456789ABCDEF]*')

def split_inst_name_addr (instname):
    bits = instname.split('_')
    assert bits, instname
    addr = bits[-1]
    if syntax.arch == 'armv7':
        inst_addr_re = inst_addr_re_armv7
    elif syntax.arch == 'rv64':
        inst_addr_re = inst_addr_re_rv64
    else:
        assert False

    assert inst_addr_re.match(addr), instname

    #addr = int (addr[1:], 16)
    #rv64_hack
    addr = int(addr, 16)
    return ('_'.join (bits[:-1]), addr)

def mk_bin_inst_spec (fname):
    #rv64_hack
    if syntax.arch == 'armv7':
        instruction_fun_specs = instruction_fun_specs_armv7
        wordT = syntax.word32T
    elif syntax.arch == 'rv64':
        instruction_fun_specs = instruction_fun_specs_rv64
        wordT = syntax.word64T
    else:
        assert False

    if not fname.startswith ("instruction'"):
        return

    if functions[fname].entry:
        print 'binalready %s %s' % (fname, functions[fname].entry)
        return

    (_, ident) = fname.split ("'", 1)
    print '1'
    print ident
    (ident, addr) = split_inst_name_addr (ident)
    print '2'
    print ident
    print addr
    (regs, ident) = split_inst_name_regs (ident)

    print 'be'
    print regs
    print ident

    ident = instruction_name_aliases.get (ident, ident)
    if syntax.arch == 'armv7':
        base_ident = ident.split ("_")[0]
    else:
        tmp = ident.split('-')
        if len(tmp) > 1:
            base_ident = ident.split('-')[0][:-1]
        else:
            base_ident = tmp[0]

    print 'ident'
    print base_ident
    if base_ident not in instruction_fun_specs:
        print base_ident
        assert False
        return

    (impl_fname, regspecs) = instruction_fun_specs[base_ident]

    print 'asmimpl %s' % impl_fname
    #impl_fname = impl_fname + '@' + str(hex(addr))
    add_impl_fun (impl_fname, regspecs)

    print impl_fname
    print regspecs

    assert len (regspecs) == len (regs), (fname, regs, regspecs)
    inp_regs = [reg for (reg, d) in zip (regs, regspecs) if d == 'I']
    out_regs = [reg for (reg, d) in zip (regs, regspecs) if d == 'O']

    #print inp_regs
    #print out_regs
    #assert False

    call = syntax.Node ('Call', 'Ret', ('l_' + impl_fname,
                                        [syntax.mk_var (reg, wordT) for reg in inp_regs]
                                        + [syntax.mk_token (ident)]
                                        + [syntax.mk_var (nm, typ) for (nm, typ) in bin_globs],
                                        [(reg, wordT) for reg in out_regs] + bin_globs))
    assert not functions[fname].nodes
    print 'binfname %s' % fname
    functions[fname].nodes[1] = call
    functions[fname].entry = 1

# inline assembly from C-refine
def mk_asm_inst_spec (fname):

    if not fname.startswith ("asm_instruction'"):
        return

    if syntax.arch == 'armv7':
        instruction_fun_specs = instruction_fun_specs_armv7
    elif syntax.arch == 'rv64':
        instruction_fun_specs = instruction_fun_specs_rv64
    else:
        assert False

    if functions[fname].entry:
        print 'already %s %s' % (fname, functions[fname].entry)
        #assert False
        return

    #	assert False

    (_, ident) = fname.split ("'", 1)
    (args, ident) = split_inst_name_regs (ident)

    print 'args'
    print ident
    print args

    if syntax.arch == 'armv7':
        if not all ([arg.startswith ('%') for arg in args]):
            printout ('Warning: asm instruction name: formatting: %r'
                      % fname)
            return

    if syntax.arch == 'armv7':
        base_ident = ident.split ("_")[0]
    else:
        tmp = ident.split('-')
        if len(tmp) > 1:
            base_ident = tmp[0][:-1]
        else:
            base_ident = tmp[0]

    print 'ident %s' % base_ident
    if base_ident not in instruction_fun_specs:
        print base_ident
        assert False
        return

    (impl_fname, regspecs) = instruction_fun_specs[base_ident]

#    impl_fname = 'asm_' + impl_fname
    print 'implfun %s' % impl_fname
    add_impl_fun (impl_fname, regspecs)

    (iscs, imems, _) = logic.split_scalar_pairs (functions[fname].inputs)
    (oscs, omems, _) = logic.split_scalar_pairs (functions[fname].outputs)

    call = syntax.Node ('Call', 'Ret', ('r_' + impl_fname,
                                        iscs + [syntax.mk_token (ident)] + imems,
                                        [(v.name, v.typ) for v in oscs + omems]))
    assert not functions[fname].nodes
    print 'asmfname %s' % fname
    functions[fname].nodes[1] = call
    functions[fname].entry = 1

def add_inst_specs (report_problematic = True):
    for f in functions.keys ():
        print 'func %s' % f
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

    print 'unhandled'
    print unhandled

    for f in unhandled:
        printout ('Function %r contains unhandled instructions:' % f)
        printout ('  %s' % unhandled[f])
    return unhandled


