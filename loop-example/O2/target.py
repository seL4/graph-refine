#
# Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

from target_objects import target_dir, structs, functions, const_globals
from target_objects import symbols, sections, rodata, pairings, danger_set
import target_objects

import syntax
import pseudo_compile
import objdump
import logic
import re

f = open ('%s/loop-O2.elf.symtab' % target_dir)
(lsymbs, lsects) = objdump.build_syms (f)
f.close ()
symbols.update (lsymbs)
sections.update (lsects)

f = open ('%s/CFunDump.txt' % target_dir)
syntax.parse_and_install_all (f, 'C')
f.close ()

f = open ('%s/ASMO2Funs.txt' % target_dir)
(astructs, afunctions, aconst_gs) = syntax.parse_and_install_all (f, 'ASM')
f.close ()
assert not astructs
assert not aconst_gs

assert logic.aligned_address_sanity (afunctions, symbols, 4)

print 'Pseudo-Compiling.'
pseudo_compile.compile_funcs (functions)

print 'Checking.'
syntax.check_funs (functions)

def asm_split_pairings ():
    pairs = [(s, 'Loop.' + s) for s in afunctions]
    target_objects.use_hooks.add ('stack_logic')
    import stack_logic
    stack_bounds = '%s/StackBounds.txt' % target_dir
    new_pairings = stack_logic.mk_stack_pairings (pairs, stack_bounds)
    pairings.update (new_pairings)

asm_split_pairings ()


