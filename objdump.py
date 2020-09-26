#
# Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

# parsing code for objdump files. used on a symtab dump to build a python
# symbol table and on a disassembly of the .rodata section to build a
# summary of the read-only data

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

def install_syms (symtab):
    (syms, sects) = build_syms (symtab)
    import target_objects
    target_objects.symbols.update (syms)
    target_objects.sections.update (sects)

is_rodata_line = re.compile('^\s*[0-9a-fA-F]+:\s+[0-9a-fA-F]+\s+')

def build_rodata (rodata_stream, rodata_ranges = [('Section', '.rodata')]):
    from syntax import structs, fresh_name, Struct, mk_word64, mk_word32, mk_word16
    import syntax
    from target_objects import symbols, sections, trace

    act_rodata_ranges = []
    for (kind, nm) in rodata_ranges:
        print "kind %s nm %s" % (kind, nm)
        if kind == 'Symbol':
            (addr, size, _) = symbols[nm]
            act_rodata_ranges.append ((addr, addr + size - 1))
        elif kind == 'Section':
            if nm in sections:
                act_rodata_ranges.append (sections[nm])
            else:
                # it's reasonable to supply .rodata as the
                # expected section only for it to be missing
                trace ('No %r section in objdump.' % nm)
        else:
            assert kind in ['Symbol', 'Section'], rodata_ranges

    comb_ranges = []
    for (start, end) in sorted (act_rodata_ranges):
        if comb_ranges and comb_ranges[-1][1] + 1 == start:
            (start, _) = comb_ranges[-1]
            comb_ranges[-1] = (start, end)
        else:
            comb_ranges.append ((start, end))

    rodata = {}
    print 'FIXME LOADING RODATA'
    print rodata_ranges
    print sections
    print symbols
    for (s, e) in act_rodata_ranges:
        print "%s -- %s" % (hex(s), hex(e))
    for line in rodata_stream:
        if not is_rodata_line.match (line):
            continue
        bits = line.split ()
        (addr, v) = (int (bits[0][:-1], 16), int (bits[1], 16))
        if [1 for (start, end) in comb_ranges
                if start <= addr and addr <= end]:
            # rv64_hack
            #if not addr % 4 == 0:
            #print 'waring %s not aligned' % addr
            #assert addr % 4 == 0, addr

            #rv64_hack
            if len(bits[1]) > 4:
                # RISC-V rodata is little-endian
                rodata[addr] = v & 0xffff
                rodata[addr + 2] = v >> 16
                print 'addr %s val %s' % (hex(addr), hex(rodata[addr]))
                print 'addr %s val %s' % (hex(addr + 2), hex(rodata[addr + 2]))
            else:
                rodata[addr] = v
                print 'addr %s val %s' % (hex(addr), hex(rodata[addr]))

    print comb_ranges
    print len(comb_ranges)
    if len (comb_ranges) == 1:
        rodata_names = ['rodata_struct']
    else:
        rodata_names = ['rodata_struct_%d' % (i + 1)
                        for (i, _) in enumerate (comb_ranges)]

    rodata_ptrs = []
    for ((start, end), name) in zip (comb_ranges, rodata_names):
        struct_name = fresh_name (name, structs)
        struct = Struct (struct_name, (end - start) + 1, 1)
        structs[struct_name] = struct
        typ = syntax.get_global_wrapper (struct.typ)
        if syntax.is_64bit:
            mk_word = mk_word16
        else:
            mk_word = mk_word32
        rodata_ptrs.append ((mk_word(start), typ))

    return (rodata, comb_ranges, rodata_ptrs)

def install_rodata (rodata_stream, rodata_ranges = [('Section', '.rodata')]):
    import target_objects
    rodata = build_rodata (rodata_stream, rodata_ranges)
    target_objects.rodata[:] = rodata

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

