# * Copyright 2015, NICTA
# *
# * This software may be distributed and modified according to the terms of
# * the BSD 2-Clause license. Note that NO WARRANTY is provided.
# * See "LICENSE_BSD2.txt" for details.
# *
# * @TAG(NICTA_BSD)

# parsing code for objdump files. used on a symtab dump to build a python
# symbol table and on a disassembly of the .rodata section to build a
# summary of the read-only data

from syntax import structs, fresh_name, Struct, mk_word32
from target_objects import sections, trace
import re

def build_syms (symtab):
	syms = {}
	for line in symtab:
		bits = line.split ()
		try:
			addr = int (bits[0], 16)
			size = int (bits[-2], 16)
			section = bits[-3]
			syms[bits[-1]] = (addr, size, section)
		except ValueError:
			pass
		except IndexError:
			pass

	sections = {}
	for (addr, size, section) in syms.itervalues ():
		if not size:
			continue
		(start, end) = sections.get (section, (addr, addr))
		start = min (addr, start)
		end = max (addr + size - 1, end)
		sections[section] = (start, end)

	return (syms, sections)

is_rodata_line = re.compile('^\s*[0123456789abcdefABCDEF]+:\s')

def build_rodata (rodata_stream):
	rodata = {}
	for line in rodata_stream:
		if not is_rodata_line.match (line):
			continue
		bits = line.split ()
		rodata[int (bits[0][:-1], 16)] = int (bits[1], 16)

	rodata_min = min (rodata.keys ())
	rodata_max = max (rodata.keys ()) + 4
	assert rodata_min % 4 == 0

	rodata_range = range (rodata_min, rodata_max, 4)
	for x in rodata_range:
		if x not in rodata:
			trace ('.rodata section gap at address %x' % x)

	struct_name = fresh_name ('rodata', structs)
	struct = Struct (struct_name, rodata_max - rodata_min, 1)
	structs[struct_name] = struct

	(start, end) = sections['.rodata']
	assert start <= rodata_min
	assert end + 1 >= rodata_max

	return (rodata, mk_word32 (rodata_min), struct.typ)


# the prunes file isn't really an objdump file, but this seems the best place

non_var_re = re.compile('[(),\s\[\]]+')

def parse_prunes (prune_stream):
	prunes = {}
	for l in prune_stream:
		[lname, rhs] = l.split ('from [')
		bits = lname.split ()
		assert bits[:3] == ['Pruned', 'inputs', 'of']
		name = bits[3]
		[lvars, rvars] = rhs.split ('] to [')
		lvars = [v for v in non_var_re.split (lvars) if v]
		rvars = [v for v in non_var_re.split (rvars) if v]
		if not (lvars[-2:] == ['dm', 'm']
				and rvars[-2:] == ['dm', 'm']):
			continue
		lvars = lvars[:-2]
		rvars = rvars[:-2]
		prunes['DecompiledFuns.' + name + '_step'] = (lvars, rvars)
	return prunes

# likewise the signatures produced by the c-parser

def parse_sigs (sig_stream):
	sigs = {}
	for l in sig_stream:
		bits = l.split ()
		if not bits:
			continue
		ret = int (bits[0])
		nm = bits[1]
		args = [int(bit) for bit in bits[2:]]
		sigs[nm] = (args, ret)
	return sigs

