# * Copyright 2015, NICTA
# *
# * This software may be distributed and modified according to the terms of
# * the BSD 2-Clause license. Note that NO WARRANTY is provided.
# * See "LICENSE_BSD2.txt" for details.
# *
# * @TAG(NICTA_BSD)

from target_objects import target_dir, structs, functions, const_globals
from target_objects import symbols, sections, rodata, pairings, danger_set

import syntax
import objdump
import logic

f = open ('%s/Functions.txt' % target_dir)
syntax.parse_and_install_all (f, None)
f.close ()

print 'Checking.'
syntax.check_funs (functions)

#print 'Pseudo-Compiling.'
#pseudo_compile.compile_funcs (functions)

#print 'Duplicate-sharing.'
#pseudo_compile.combine_function_duplicates (functions)

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


