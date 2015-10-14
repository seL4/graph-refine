# * Copyright 2015, NICTA
# *
# * This software may be distributed and modified according to the terms of
# * the BSD 2-Clause license. Note that NO WARRANTY is provided.
# * See "LICENSE_BSD2.txt" for details.
# *
# * @TAG(NICTA_BSD)

# trace_refute: refutations of traces, useful for WCET

import syntax
import solver
import problem
import rep_graph
import search
import logic
import check
import stack_logic

from target_objects import functions, trace, pairings, symbols
import target_objects

from logic import azip

def parse_num_list (s):
	s = s.strip()
	assert s[0] == '[', s
	assert s[-1] == ']', s
	inner = s[1:-1].strip ()
	if not inner:
		return []
	return map (int, inner.split(','))

def parse_ctxt_arcs (f):
	ctxt = None
	fc_len = len ('Funcall context')
	arcs = {}
	for line in f:
		if line.startswith('Funcall context'):
			line = line.strip()
			assert line[-1] == '{'
			context = line[fc_len:-1].strip()
			ctxt = tuple (parse_num_list (context))
			arcs.setdefault (ctxt, [])
		elif line.startswith('}'):
			ctxt = None
		elif line.startswith('Arc:'):
			assert ctxt, line
			arc = parse_num_list (line[4:])
			arcs[ctxt].append (arc)
	assert not ctxt, ctxt
	return arcs

body_addrs = {}

def is_addr (n):
	return n % 4 == 0

def setup_body_addrs ():
	for f in stack_logic.get_functions_with_tag ('ASM'):
		for n in functions[f].nodes:
			if is_addr (n):
				body_addrs[n] = f
	# just in case there aren't any
	body_addrs['Loaded'] = True

def get_body_addrs_fun (n):
	"""get the function a given body address is within."""
	if not body_addrs:
		setup_body_addrs ()
	return body_addrs.get (n)

def build_compound_problem (fnames):
	"""mirrors build_problem from check for multiple functions"""
	print fnames
	p = problem.Problem (None, name = ', '.join(fnames))
	fun_tag_pairs = []

	all_tags = {}
	for fn in fnames:
		[pair] = pairings[fn]
		next_tags = {}
		for (pair_tag, fname) in pair.funs.items ():
			# FIXME: assuming we never repeat functions
			tag = fname + '_' + pair_tag
			tag = syntax.fresh_name (tag, all_tags)
			next_tags[pair_tag] = tag
			p.add_entry_function (functions[fname], tag)
			p.hook_tag_hints[tag] = pair_tag
		fun_tag_pairs.append ((next_tags, pair))

	p.do_analysis ()

	# FIXME: the inlining is heuristic and belongs in 'search'
	check.inline_completely_unmatched (p, ref_tags = ['ASM', 'C'],
		skip_underspec = True)
	
	# now do any C inlining
	for (tags, _) in fun_tag_pairs:
		assert set (tags) == set (['ASM', 'C']), tags
		check.inline_reachable_unmatched (p, tags['C'], tags['ASM'],
			skip_underspec = True)

	p.pad_merge_points ()
	p.do_analysis ()

	free_hyps = []
	for (tags, pair) in fun_tag_pairs:
		(inp_eqs, _) = pair.eqs
		free_hyps += check.inst_eqs (p, (), inp_eqs, tags)
		err_vis_opts = rep_graph.vc_options ([0, 1, 2], [1])
		err_vis_vc = tuple ([(n, err_vis_opts) for n in p.loop_heads ()
			if p.node_tags[n][0] == tags['C']])
		err_vis = (('Err', err_vis_vc), tags['C'])
		free_hyps.append (rep_graph.pc_false_hyp (err_vis))

	addr_map = {}
	for n in p.nodes:
		if not p.node_tags[n][0].endswith ('_ASM'):
			continue
		if type (p.node_tags[n][1]) == tuple:
			(fname, data) = p.node_tags[n][1]
			if logic.is_int (data) and is_addr (data):
				assert data not in addr_map, data
				addr_map[data] = n

	return (p, free_hyps, addr_map, fun_tag_pairs)


def get_vis (p, n, tag = None):
	# assuming no loops
	(n, vc) = stack_logic.default_n_vc (p, n)
	if not tag:
		tag = p.node_tags[n][0]
	return ((n, vc), tag)

def get_pc_hyp_local (rep, n):
	return rep_graph.pc_true_hyp (get_vis (rep.p, n))

def find_actual_call_node (p, n):
	"""we're getting call addresses from the binary trace, and using the
	node naming convention to find a relevant graph node, but it might not
	be the actual call node. a short breadth-first-search should hopefully
	find it."""
	stack = [(n, 3)]
	init_n = n
	while stack:
		(n, limit) = stack.pop (0)
		if limit < 0:
			continue
		if p.nodes[n].kind == 'Call':
			return n
		else:
			for c in p.nodes[n].get_conts ():
				stack.append ((c, limit -1))
	trace ('failed to find Call node near %s' % init_n)
	return None

def adj_eq_seq_for_asm_fun_link (fname):
	cc = stack_logic.get_asm_calling_convention (fname)
	if not cc:
		return None
	addrs = [(p, v.typ) for arg in cc['args']
		for (_, p, v, _) in arg.get_mem_accesses ()]
	inps = functions[fname].inputs
	[stack_idx] = [i for (i, (nm, _)) in enumerate (inps)
		if nm == 'stack']
	def adj (seq):
		(x_stack, y_stack) = seq[stack_idx]
		xsub = dict ([(v, xv) for (v, (xv, _)) in azip (inps, seq)])
		ysub = dict ([(v, yv) for (v, (_, yv)) in azip (inps, seq)])
		from logic import var_subst
		stk_eqs = [(syntax.mk_memacc (x_stack, var_subst (p, xsub), t),
			syntax.mk_memacc (y_stack, var_subst (p, ysub), t))
			for (p, t) in addrs]
		return seq[:stack_idx] + seq[stack_idx + 1:] + stk_eqs
	return adj

def get_call_link_hyps (p, n, (from_tags, from_pair), (to_tags, to_pair)):
	n = find_actual_call_node (p, n)
	fname = p.nodes[n].fname
	assert fname == to_pair.funs['ASM']
	vis = get_vis (p, n)
	hyps = rep_graph.mk_function_link_hyps (p, vis, to_tags['ASM'],
		adjust_eq_seq = adj_eq_seq_for_asm_fun_link (fname))

	c_fname = to_pair.funs['C']
	ns = [n for n in p.nodes if p.nodes[n].kind == 'Call'
		if p.nodes[n].fname == c_fname
		if p.node_tags[n][0] == from_tags['C']]
	if len (ns) == 1:
		[cn] = ns
		vis = get_vis (p, cn)
		hyps += rep_graph.mk_function_link_hyps (p, vis, to_tags['C'])

	return hyps

def refute_minimise_vis_hyps (rep, free_hyps, call_hyps, vis_pcs):
	def test (call_hyps, vis_pcs):
		hs = [h for grp in call_hyps for h in grp] + [
			h for (h, _) in vis_pcs] + free_hyps
		return rep.test_hyp_whyps (syntax.false_term, hs)

	if not test (call_hyps, vis_pcs):
		return None
	for i in range (len (call_hyps)):
		if test (call_hyps [ - i : ], vis_pcs):
			call_hyps = call_hyps [ - i : ]
			break
	i = 0
	while i < len (vis_pcs):
		while i < len (vis_pcs) and test (call_hyps,
				vis_pcs[:i] + vis_pcs[i + 1 :]):
			vis_pcs = vis_pcs[:i] + vis_pcs[i + 1 :]
		i += 1

	return (call_hyps, vis_pcs)

verdicts = {}

new_refutes = {}

def previous_verdict (call_stack, f, arc):
	for (stack, points, verdict) in verdicts.get (f, []):
		suffix = call_stack[len (call_stack) - len (stack) : ]
		if tuple (suffix) == tuple (stack):
			if verdict == 'impossible':
				if set (points) <= set (arc):
					return True
			if verdict == 'possible':
				if set (arc) <= set (points):
					return False
	return None

def identify_function (call_stack, addrs):
	fs = set ([get_body_addrs_fun (addr) for addr in addrs]) - set ([None])
	assert len (fs) <= 1, (fs, addrs)
	if fs:
		[f] = list (fs)
		return f
	call = call_stack[-1]
	prev_fn = get_body_addrs_fun (call)
	cn = find_actual_call_node (functions[prev_fn], call)
	fn = functions[prev_fn].nodes[cn].fname
	return fn

def build_compound_problem_with_links (call_stack, f):
	funs = [get_body_addrs_fun (addr) for addr in call_stack] + [f]
	(p, hyps, addr_map, tag_pairs) = build_compound_problem (funs)
	call_tags = zip (tag_pairs[:-1], tag_pairs[1:])
	call_hyps = [get_call_link_hyps (p, addr_map[n], from_tp, to_tp)
		for (n, (from_tp, to_tp)) in zip (call_stack, call_tags)]
	wcet_hyps = []
	from rep_graph import eq_hyp
	for (entry, tag, _, inputs) in p.entries:
		entry_vis = ((entry, ()), tag)
		for f in target_objects.hooks ('extra_wcet_assertions'):
			for assn in f (inputs):
				wcet_hyps.append (eq_hyp ((assn, entry_vis),
					(syntax.true_term, entry_vis)))
	return (p, hyps + [h for hs in call_hyps for h in hs]
		+ wcet_hyps, addr_map)

def refute_function_arcs (call_stack, arcs):
	f = identify_function (call_stack,
		[addr for arc in arcs for addr in arc])

	# how much stack to use?
	stack = list (call_stack [ -3: ])

	arcs = [arc for arc in arcs
		if previous_verdict (call_stack, f, arc) == None]
	if not arcs:
		return

	(p, hyps, addr_map) = build_compound_problem_with_links (call_stack, f)
	rep = rep_graph.mk_graph_slice (p)

	for arc in arcs:
		if previous_verdict (call_stack, f, arc) != None:
			continue
		print 'fresh %s arc %s: %s' % (f, call_stack, arc)
		vis_pcs = [(get_pc_hyp_local (rep, addr_map[addr]), addr)
			for addr in arc]
		vis_pcs = dict (vis_pcs).items ()

		res = refute_minimise_vis_hyps (rep, hyps, call_hyps, vis_pcs)
		if res == None:
			verdicts.setdefault (f, [])
			verdicts[f].append ((stack, list (arc), 'possible'))
			continue

		(used_call_hyps, used_vis_pcs) = res
		stack = stack [ - len (used_call_hyps) : ]
		used_vis = [addr for (_, addr) in used_vis_pcs]
		verdicts.setdefault (f, [])
		verdicts[f].append ((stack, used_vis, 'impossible'))
		new_refutes[f] = True
		print 'added %s refutation %s: %s' % (f, stack, used_vis)

def serialise_verdicts (fname):
	f = open (fname, 'w')
	for (_, vs) in verdicts.iteritems ():
		for (stack, visits, verdict) in vs:
			f.write ('%s: %s: %s\n' % (list (stack), list (visits),
				verdict))
	f.close ()

def load_verdicts (fname):
	f = open (fname)
	for l in f:
		bits = l.split(':')
		if len (bits) < 3:
			bits = set ([bit for bit in bits if bit.strip ()])
			assert not bits, bits
		[stack, visits, verdict] = bits
		stack = parse_num_list (stack)
		visits = parse_num_list (visits)
		verdict = verdict.strip ()
		assert verdict in ['possible', 'impossible'], verdict
		fn = identify_function (stack, visits)
		verdicts.setdefault (fn, [])
		verdicts[fn].append ((stack, visits, verdict))
	f.close ()

last_report = [0]

def refute (inp_fname, out_fname, prev_fnames):
	f = open (inp_fname)
	arcs = parse_ctxt_arcs (f)
	f.close ()
	body_addrs.clear ()
	setup_body_addrs ()
	verdicts.clear ()
	new_refutes.clear ()
	for fn in prev_fnames:
		load_verdicts (fn)
	report = {}
	last_report[0] = report
	for (ctxt, arcs) in arcs.iteritems ():
		try:
			refute_function_arcs (ctxt, arcs)
			report[ctxt] = 'Success'
		except problem.Abort:
			report[ctxt] = 'ProofAbort'
		except Exception, e:
			import sys, traceback
			exception = sys.exc_info ()
			(etype, evalue, tb) = exception
			ss = traceback.format_exception (etype, evalue, tb)
			report[ctxt] = '\n'.join (['EXCEPTION'] + ss)
	serialise_verdicts (out_fname)
	print 'Found new refutations: %s' % bool (new_refutes)
	return (bool (new_refutes), report)

if __name__ == '__main__':
	import sys
	args = target_objects.load_target ()
	prevs = [arg[5:] for arg in args if arg.startswith ('prev:')]
	args = [arg for arg in args if 'prev:' not in arg]
	if len (args) < 2:
		print 'Usage: python trace_refute <target> <refutables> [prev:output] <output>'
		print 'where <target> as per graph-refine, <refutables> from reconstruct.py'
		print 'and <output> is output filename.'
		print 'Optional previous output may be loaded.'
		print 'e.g. python trace_refute new-gcc-O2 new-gcc-O2/ctxt_arcs.txt prev:refutes.txt refutes.txt'
		sys.exit (1)
	else:
		(new, _) = refute (args[0], args[1], prevs)
		if new:
			sys.exit (127)
		else:
			sys.exit (0)


