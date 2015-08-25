# * Copyright 2015, NICTA
# *
# * This software may be distributed and modified according to the terms of
# * the BSD 2-Clause license. Note that NO WARRANTY is provided.
# * See "LICENSE_BSD2.txt" for details.
# *
# * @TAG(NICTA_BSD)

from target_objects import target_dir, structs, functions
from target_objects import symbols, sections, rodata, pairings
import target_objects

import syntax
import pseudo_compile
import objdump
import logic
import re

f = open ('%s/kernel.elf.symtab' % target_dir)
(lsymbs, lsects) = objdump.build_syms (f)
f.close ()
symbols.update (lsymbs)
sections.update (lsects)

f = open ('%s/CFunctions.txt' % target_dir)
syntax.parse_and_install_all (f, 'C')
f.close ()

f = open ('%s/ASMFunctions.txt' % target_dir)
(astructs, afunctions, aconst_globals) = syntax.parse_and_install_all (f, 'ASM')
f.close ()
assert not astructs
assert not aconst_globals

assert logic.aligned_address_sanity (afunctions, symbols, 4)

f = open ('%s/kernel.elf.rodata' % target_dir)
rodata[:] = objdump.build_rodata (f)
f.close ()

print 'Pseudo-Compiling.'
pseudo_compile.compile_funcs (functions)

def make_pairings ():
	pairs = [(s, 'Kernel_C.' + s) for s in functions
		if ('Kernel_C.' + s) in functions]
	target_objects.use_hooks.add ('stack_logic')
	import stack_logic
	stack_bounds = '%s/StackBounds.txt' % target_dir
	new_pairings = stack_logic.mk_stack_pairings (pairs, stack_bounds)
	pairings.update (new_pairings)

make_pairings ()

print 'Checking.'
syntax.check_funs (functions)


