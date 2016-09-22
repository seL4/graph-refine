# * Copyright 2014, NICTA
# *
# * This software may be distributed and modified according to the terms
# of
# * the BSD 2-Clause license. Note that NO WARRANTY is provided.
# * See "LICENSE_BSD2.txt" for details.
# *
# * @TAG(NICTA_BSD)
#!/usr/bin/env python

import os
import re
import sys
import copy
from subprocess import Popen, PIPE

#so we can use addrs_to_f
from elf_file import elfFile
import elf_parser

global path_counts
path_counts = {}
global b_id_counts
b_id_counts = {}

global tcfg_paths
tcfg_paths = {}

global tcfg_to_bb_map
tcfg_to_bb_map = {}

global total_edges
total_edges = 0

global id_to_context
id_to_context = {}

global elf_file

def buildBBAddrToSize():
    ret = {}
    global tcfg_to_bb_map
    for bb_id in tcfg_to_bb_map:
        (bb_addr, bb_size, bb_contexts, loop_id) = tcfg_to_bb_map[bb_id]
        #print "bb_addr: %x, bb_size: %x" % (bb_addr, bb_size)
        if bb_addr not in ret or (ret[bb_addr] < bb_size):
            ret[bb_addr] = bb_size
    return ret

def read_variables(input_filename):
    var_re = re.compile(r'^d(\d+|Sta)_(\d+)\s+([\d.]+)$')
    b_var_re = re.compile(r'^b(\d+)\s+([\d.]+)$')

    f = open(input_filename)
    global path_counts
    global total_edges
    global b_id_counts
    while True:
        s = f.readline()
        if s == '':
            break
        g = var_re.match(s.strip())
        if not g:
	 	b_match = b_var_re.match(s.strip())
		if b_match:
		  b_id, count = b_match.groups()
		  b_id_counts[int(b_id)] = int(float(count))
		continue
        from_id, to_id, count = g.groups()
        if from_id not in path_counts:
            path_counts[from_id] = {}

        if to_id in path_counts[from_id]:
            raise Exception("Variable from %s to %s mentioned more than once." % (from_id, to_id))

        count = int(round(float(count)))
        if count == 0:
            continue

        path_counts[from_id][to_id] = count
        total_edges += count

    f.close()
    if not path_counts:
        raise Exception("No variables found in solution.")

def print_context(ctx_list):
    for x in ctx_list[:-1]:
      print '%s' % elfFile().addrs_to_f[x],
    print ''

def read_tcfg_map(input_filename):
    '''
    Sets up some global states and return the tcfg_to_bb_map
    '''
    tcfg_re = re.compile(
        r'''^
            (\d+)
            \( \d+ \. \d+ \)
            \(
                (0x[0-9a-f]+)
                \+
                (0x[0-9a-f]+)
            \):
            \s
            \[\s
                ([\d\s]*)
            \](.*$)''',
            re.VERBOSE)

    f = open(input_filename)
    global tcfg_paths
    global tcfg_to_bb_map
    global id_to_bb_addr
    id_to_bb_addr = {}
    while True:
        s = f.readline()
        if s == '':
            break
        g = tcfg_re.match(s.strip())
        if not g:
            continue

        bb_id, bb_addr, bb_size, bb_dests, bb_aux = g.groups()

        bb_addr = int(bb_addr, 16)
        bb_size = int(bb_size, 16)
        bb_dests = [ x.strip() for x in bb_dests.split() if x.strip() ]
        ctx_str = list(bb_aux.split(' '))
        ctx_list = [ int(x, 16) for x in ctx_str if x <> '' ]
        #get rid of the loop_id
        ctx_list = ctx_list[1:]
        id_to_context[bb_id] = ctx_list 
        bb_aux = bb_aux.split()
        loop_id = bb_aux[0]
        if loop_id == '0':
            loop_id = None
        bb_context = reversed ([int (addr, 16) for addr in bb_aux[1:-1]])

        assert bb_id not in tcfg_paths

        tcfg_paths[bb_id] = bb_dests
        tcfg_to_bb_map[bb_id] = (bb_addr, bb_size, list (bb_context), loop_id)
        id_to_bb_addr[bb_id] = bb_addr
        '''
        if not bb_addr in bb_addr_to_ids:
          bb_addr_to_ids[bb_addr] = [bb_id]
        else:
          bb_addr_to_ids[bb_addr].append(bb_id)
        '''
    f.close()
    if not tcfg_paths:
        raise Exception("No nodes found in tcfg map.")
    return tcfg_to_bb_map

global addr2line_proc
addr2line_proc = None
def addr2line(addr):
    global addr2line_proc
    if addr2line_proc is None:
        addr2line_proc = Popen(
            ['arm-none-eabi-addr2line', '-fe',
            elf_file],
            stdin=PIPE, stdout=PIPE, close_fds=True
        )

    addr2line_proc.stdin.write('%#x\n' % addr)
    func = addr2line_proc.stdout.readline().strip()
    line = addr2line_proc.stdout.readline().strip()
    return func

compound_ids = {}

def simplify():
    rev = {}
    for i in path_counts:
        for j in path_counts[i]:
            rev.setdefault(j, [])
            rev[j].append(i)
    simps = [i for i in path_counts if len(path_counts[i]) == 1
        if len(rev.get(i, [])) == 1]
    for i in simps:
        [j] = rev[i]
        assert path_counts[j].keys() == [i]
        count = path_counts[j][i]
        assert path_counts[i].values() == [count]
        compound_ids.setdefault(j, [j])
        compound_ids[j].extend(compound_ids.get(i, [i]))
        path_counts[j] = path_counts[i]
        del path_counts[i]

def print_block(node_id):
    if node_id == 'Sta':
        return
    addr, size, _, _ = tcfg_to_bb_map[node_id]
    for i in xrange(0, size, 4):
        print '%#x %s' % (addr + i, addr2line(addr + i))

def print_block2(node_id):
    assert node_id != 'Sta', node_id
    addr, size, _, _ = tcfg_to_bb_map[node_id]
    print '%#x - %#x' % (addr, addr + size - 4)

def count_arc(local_path_counts, arc):
    arc_steps = zip(arc, arc[1:] + [arc[0]])
    arc_counts = [local_path_counts[i][j] for (i, j) in arc_steps]
    count = min(arc_counts)
    for (i, j) in arc_steps:
        local_path_counts[i][j] -= count
    return (count, arc)

def grab_arcs(local_path_counts, start):
    stack = [start]
    stack_set = set(stack)

    arcs = []
    decisions = []

    while True:
        node_id = stack[-1]

        # have we reached the exit?
        if node_id not in local_path_counts:
            assert stack[0] == 'Sta'
            for (i, node_id) in enumerate (stack):
                if node_id in local_path_counts:
                    local_path_counts[node_id][stack[i + 1]] -= 1
            arcs.append ((1, stack))
            return (arcs, decisions)

        succs = [k for (k, count) in local_path_counts[node_id].iteritems()
            if count > 0]
        next_id = succs.pop()
        if succs:
            decisions.append (node_id)

        if next_id in stack_set:
            # we've found a loop
            i = [j for (j, elt) in enumerate(stack) if elt == next_id][0]
            arc = stack[i:]
            stack = stack[:i]
            stack_set = set(stack)
            arcs.append (count_arc (local_path_counts, arc))
        
            if stack == []:
                return (arcs, decisions)
        else:
            stack.append (next_id)
            stack_set.add (next_id)

def dict_list(xs):
    d = {}
    for (x, y) in xs:
        d.setdefault (x, [])
        d[x].append(y)
    return d

def follow2():
    # Find an eulerian path through the graph.

    local_path_counts = copy.deepcopy(path_counts)

    (arcs, decisions) = grab_arcs(local_path_counts, 'Sta')
    live = [x for x in decisions
        if [y for y in local_path_counts[x] if local_path_counts[x][y] > 0]]
    while live:
        x = live[0]
        (arcs2, decisions) = grab_arcs(local_path_counts, x)
        arcs.extend(arcs2)
        live = [x for x in live if [y for y in local_path_counts[x]
            if local_path_counts[x][y] > 0]]

    arc_heads = dict_list([(arc[0], (count, arc)) for (count, arc) in arcs])

    [(_, top_arc)] = arc_heads['Sta']
    for (count, arc) in arcs:
        print 'Arc (%d iterations): {' % count
        if arc[0] == 'Sta':
            arc = arc[1:]
        print_arc_rec(arc, [], count, {})
        print '}'

def print_arc_rec(arc, init_ctxt, count, arc_heads):
    ctxt_depth = len(init_ctxt)
    for node_id in arc:
        xs = arc_heads.get(node_id, [])
        for (count2, arc2) in xs:
            arc_heads[node_id] = []
            assert count2 % count == 0, (count2, count)
            print 'Loop (%d iterations) {' % (count2 / count)
            print_arc_rec(arc2, ctxt, count2, arc_heads)
        _, _, ctxt, _ = tcfg_to_bb_map[node_id]
        for call_addr in ctxt[ctxt_depth:]:
            print 'Function call at %#x: {' % call_addr
        for i in range(ctxt_depth - len(ctxt)):
            print '}'
        ctxt_depth = len(ctxt)
        print_block2(node_id)
    for i in range(ctxt_depth - len(init_ctxt)):
        print '}'
    print '}'

def dot():
    print 'digraph imm {'
    for i in path_counts:
        for j in path_counts[i]:
            if i != 'Sta' and type(j) != 'Sta':
              print '%s -> %s [label = \"%d %s -> %s\"];' % (i, j, path_counts[i][j], elfFile().addrs_to_f[id_to_bb_addr[i]], elfFile().addrs_to_f[id_to_bb_addr[j]])
            else: 
              print '%s -> %s [label = \"%d\"];' % (i, j, path_counts[i][j])

    print '}'

def local_loop_id(i):
    _, _, ctxt, lid = tcfg_to_bb_map[i]
    if lid == None:
        return i
    else:
        _, _, ctxt2, _ = tcfg_to_bb_map[lid]
        if ctxt2 == ctxt:
            return lid
        else:
            return i

def refutable():
    print 'Refutable paths:'
    node_ids = set(list(path_counts)
        + [j for i in path_counts for j in path_counts[i]]) 
    node_ids -= set (['Sta'])
    ctxts = dict_list([(tuple(tcfg_to_bb_map[i][2]), i) for i in node_ids])
    for (ctxt, nodes) in ctxts.iteritems():
        if not ctxt:
            continue
        print 'Funcall context %r {' % list(ctxt)
        outgoing = {}
        rev_graph = {}
        for i in nodes:
            li = local_loop_id (i)
            outgoing.setdefault(li, 0)
            for (j, count) in path_counts.get(i, {}).iteritems():
                outgoing[li] += count
                if tcfg_to_bb_map[j][2] != list(ctxt):
                    continue
                lj = local_loop_id (j)
                if li != lj:
                    rev_graph.setdefault(lj, {})
                    rev_graph[lj][li] = count
        print_backtracks(outgoing, rev_graph)
        print '}'

def print_backtracks(outgoing, rev_graph):
    covered = set()
    for i in rev_graph:
        if i in covered:
            continue
        tracks = print_backtracks_rec([i], outgoing[i], rev_graph)
        covered.update([x for xs in tracks for x in xs])
    for i in outgoing:
        if i not in covered:
            if outgoing[i] > 0:
                print 'Arc: %r' % [tcfg_to_bb_map[i][0]]

def print_backtracks_rec(chunk, count, rev_graph):
    chunk = list(chunk)
    if count <= 0:
        return []
    while True:
        node_id = chunk[-1]
        rev_opts = rev_graph.get(node_id, {}).items()
        sum_opts = sum([c for (_, c) in rev_opts])
        opts = [(next_id, count - (sum_opts - c)) for (next_id, c) in rev_opts]
        opts = [opt for opt in opts if opt[1] > 0]
        if len(opts) > 1:
            return [track for (next_id, count) in opts
                for track in print_backtracks_rec(chunk + [next_id],
                    count, rev_graph)]
        elif not opts:
            arc_addrs = [tcfg_to_bb_map[i][0] for i in reversed(chunk)]
            print 'Arc: %r' % arc_addrs
            return [chunk]
        else:
            [(next_id, count)] = opts
            chunk.append(next_id)

def parse(elf_file_name, fun_name):
    sol_file_name = fun_name + '.imm.sol'
    map_file_name = fun_name + '.imm.map'
    elf_file = elf_file_name
    read_variables(sol_file_name)
    read_tcfg_map()

def profile():
    bb_addr_to_count = {}
    funs_to_bb_addrs = {}
    funs_to_count = {}
    total_inst_ran = 0
    global tcfg_to_bb_map
    maxi = 0
    for i in path_counts:
      for j in path_counts[i]:

        bb_addr = id_to_bb_addr[j]
        inst_count = path_counts[i][j] * tcfg_to_bb_map[j][1]
        total_inst_ran += inst_count
        if inst_count == 0:
            continue
        if (bb_addr not in bb_addr_to_count):
            bb_addr_to_count[bb_addr] = 0
        bb_addr_to_count[bb_addr] += inst_count

        if path_counts[i][j] > maxi:
            maxi = path_counts[i][j]
            max_edge = (i,j)

    for bb_addr in bb_addr_to_count:
        fun = elfFile().addrs_to_f[bb_addr]
        if fun not in funs_to_count:
            funs_to_count[fun] = 0
            funs_to_bb_addrs[fun] = []
        funs_to_bb_addrs[fun].append( bb_addr )
        funs_to_count[fun] += bb_addr_to_count[bb_addr]

    bb_addr_to_size = buildBBAddrToSize()
    for fun in sorted(funs_to_count, key= lambda x: funs_to_count[x], reverse=True):
        count = funs_to_count[fun]
        print "%s: %u insturctions / %.2f %%" % (fun, count, float (count) / total_inst_ran * 100)
        for bb_addr in sorted(funs_to_bb_addrs[fun]):
            print "     %x-%x : %u " % (bb_addr, bb_addr + bb_addr_to_size[bb_addr] -4, bb_addr_to_count[bb_addr])

    print "\n\n Dominating executing path:"
    i,j = max_edge
    print 'max edge %d -> %d : %d' % (int(i),int(j), maxi)
    i_bb = id_to_bb_addr[i]
    j_bb = id_to_bb_addr[j]
    print '         %x -> %x '% (i_bb,j_bb)
    print '         %s -> %s ' %  (elfFile().addrs_to_f[i_bb],elfFile().addrs_to_f[j_bb]) 
    print '         context:'
    print_context(id_to_context[i])
    maxi=0

    for b_id in b_id_counts:
      count = b_id_counts[b_id]
      if count > maxi:
	max_id = b_id
	maxi = count
	print 't: max_id b%d, count %d' % (max_id, maxi)
    print 'max_id b%d, count %d' % (max_id, maxi)
    print 'max_bb_addr: %x' % id_to_bb_addr[str(max_id)]
    
    print_context(id_to_context[str(max_id)])

if __name__ == '__main__':
	argv = list(sys.argv)
	opt = '--follow'
	
	if len(argv) != 6:
		print 'len(argv): %d' % len(argv)
		print "Usage: reconstruct [OPTION] <dir_name> sol_file map elf_file"
		print 'reconstruction options: --refutable, --follow, --dot, --profile'
		sys.exit(1)

	if argv[1].startswith ('--'):
		opt = argv[1]
		argv = argv[:1] + argv[2:]
	#print 'Reading data'
	dir_name = argv[1]
	sol_file = argv[2]
	tcfg_map_f = argv[3]
	elf_file = argv[4]
	read_variables(sol_file)
	#print 'Reading tcfg'
	read_tcfg_map(tcfg_map_f)
	#print ' .. done reading'
	#initialise elfFile and parse the objdump 
	elfFile(dir_name=dir_name,elf_only=True)
	elf_parser.parseTxt()
	#print 'Simplifying'
	#simplify()
	#print ' .. done simplifying'
	if opt == '--follow':
		follow2()
	elif opt == '--dot':
		dot()
	elif opt == '--refutable':
		refutable()
	elif opt == '--profile':
		profile()
	else:
		print 'Unknown reconstruction type: %r' % opt

