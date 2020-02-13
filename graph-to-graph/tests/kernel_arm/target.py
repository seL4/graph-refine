from target_objects import target_dir, structs, functions, const_globals
from target_objects import symbols, sections, rodata, pairings, danger_set
import target_objects

import syntax
import pseudo_compile
import objdump
import logic
import re

#f = open ('%s/kernel.elf.symtab' % target_dir)
#(lsymbs, lsects) = objdump.build_syms (f)
#f.close ()
#symbols.update (lsymbs)
#sections.update (lsects)

#syntax.set_arch('armv7')

f = open ('%s/CFuns.txt' % target_dir)
syntax.parse_and_install_all (f, 'C')
f.close ()

f = open('%s/ASMFuns.txt' % target_dir)
(asstructs, afunctions, asconst_gs) = syntax.parse_and_install_all(f, 'ASM')
f.close()

#assert logic.aligned_address_sanity (afunctions, symbols, 4)

print 'Pseudo-Compiling.'
pseudo_compile.compile_funcs (functions)
#pseudo_compile.compile_funcs(afunctions)

print 'Checking.'
syntax.check_funs (functions)

'''
def run_pairings ():
	for f in functions:
		if f.startswith ('C.'):
			f2 = 'mc_' + f[2:]
		else:
			f2 = f + '_refine'
		if f2 in functions:
			pair = logic.mk_pairing (functions, f, f2)
			pairings[f] = [pair]
			pairings[f2] = [pair]
	print '%d pairing halves built.' % (len (pairings))

run_pairings ()
'''

def asm_split_pairings ():
	pairs = [(s, 'tmp.' + s) for s in afunctions]
	print pairs
	target_objects.use_hooks.add ('stack_logic')
	import stack_logic
	stack_bounds = '%s/StackBounds.txt' % target_dir
	print stack_bounds
	new_pairings = stack_logic.mk_stack_pairings (pairs, stack_bounds, False)
#	new_pairings = stack_logic.mk_stack_pairings(pairs, None, False)
	for p in new_pairings:
		print p
		print new_pairings[p]
	print new_pairings
	#assert None
	pairings.update (new_pairings)

asm_split_pairings ()
import inst_logic
inst_logic.add_inst_specs()

def add_pairing_by_as(functions):
	import stack_logic
	pairs = [(s, 'c_' + s) for s in functions]
	stack_logic.add_pairings(pairs)

#add_pairing_by_as(afunctions)

