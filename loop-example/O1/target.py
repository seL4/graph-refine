# * Copyright 2015, NICTA
# *
# * This software may be distributed and modified according to the terms of
# * the BSD 2-Clause license. Note that NO WARRANTY is provided.
# * See "LICENSE_BSD2.txt" for details.
# *
# * @TAG(NICTA_BSD)

from target_objects import target_dir, structs, functions, const_globals
from target_objects import symbols, sections, rodata, pairings, danger_set
import target_objects

import syntax
import pseudo_compile
import objdump
import logic
import re

f = open ('%s/loop-O1.elf.symtab' % target_dir)
(lsymbs, lsects) = objdump.build_syms (f)
f.close ()
symbols.update (lsymbs)
sections.update (lsects)

f = open ('%s/CFunDump.txt' % target_dir)
syntax.parse_and_install_all (f, 'C')
f.close ()

f = open ('%s/ASMO1Funs.txt' % target_dir)
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
	pairs = [(s, 'Loop.' + s) for s in ['f', 'g']]
	target_objects.use_hooks.add ('stack_logic')
	import stack_logic
	stack_bounds = '%s/StackBounds.txt' % target_dir
	new_pairings = stack_logic.mk_stack_pairings (pairs, stack_bounds)
	pairings.update (new_pairings)

asm_split_pairings ()


