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

from target_objects import functions, trace, pairings, symbols, printout
import target_objects

from logic import azip
import sys

def parse_num_list (s):
	s = s.strip()
	assert s[0] == '[', s
	assert s[-1] == ']', s
	inner = s[1:-1].strip ()
	if not inner:
		return []
	return map (int, inner.split(','))

def parse_num_arrow_list (s):
	s = s.strip()
	assert s[0] == '[', s
	assert s[-1] == ']', s
	inner = s[1:-1].strip ()
	if not inner:
		return []
	bits = inner.split(',')
	res = []
	for bit in bits:
		if '<-' in bit:
			[l, r] = bit.split('<-')
			res.append ((int (l), int(r)))
		else:
			res.append ((int (bit), 0))
	return res

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

problem_inline_scripts = {}

def get_problem_inline_scripts (pair):
	if pair.name in problem_inline_scripts:
		return problem_inline_scripts[pair.name]
	p = check.build_problem (pair, avoid_abort = True)
	scripts = p.inline_scripts
	problem_inline_scripts[pair.name] = scripts
	return scripts

last_compound_problem_req = [0]

def build_compound_problem (fnames):
	"""mirrors build_problem from check for multiple functions"""
	printout ('Building compound problem for %s' % fnames)
	last_compound_problem_req[0] = list (fnames)
	p = problem.Problem (None, name = ', '.join(fnames))
	fun_tag_pairs = []

	all_tags = {}
	for (i, fn) in enumerate (fnames):
		i = len (fnames) - i
		[pair] = pairings[fn]
		next_tags = {}
		scripts = get_problem_inline_scripts (pair)
		for (pair_tag, fname) in pair.funs.items ():
			tag = '%s_%d_%s' % (fname, i, pair_tag)
			tag = syntax.fresh_name (tag, all_tags)
			next_tags[pair_tag] = tag
			p.add_entry_function (functions[fname], tag)
			p.hook_tag_hints[tag] = pair_tag
			p.replay_inline_script (tag, scripts[pair_tag])
		fun_tag_pairs.append ((next_tags, pair))

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
			if (logic.is_int (data) and is_addr (data)
					and not fname.startswith ("instruction'")):
				assert data not in addr_map, data
				addr_map[data] = n

	return (p, free_hyps, addr_map, fun_tag_pairs)

def get_uniform_loop_vc (p, n):
	l_id = p.loop_id (n)
	assert l_id != None, n
	if n == l_id:
		restrs = tuple ([(l_id, rep_graph.vc_offs (0))])
	else:
		restrs = tuple ([(l_id, rep_graph.vc_offs (1))])
	restrs = search.restr_others_both (p, restrs, 2, 2)
	return restrs

def get_vis (p, n, tag = None, focused_loops = None):
	# not well configured for loops except in the 'uniform' case
	if not tag:
		tag = p.node_tags[n][0]
	if focused_loops and tag in focused_loops:
		l_id = focused_loops[tag]
		assert p.loop_id (n) == l_id, (n, tag, l_id)
		vc = get_uniform_loop_vc (p, n)
	else:
		(n, vc) = stack_logic.default_n_vc (p, n)
	return ((n, vc), tag)

def get_pc_hyp_local (rep, n, focused_loops = None):
	return rep_graph.pc_true_hyp (get_vis (rep.p, n,
		focused_loops = focused_loops))

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

def get_unique_call_site (p, fname, tag):
	ns = [n for n in p.nodes if p.nodes[n].kind == 'Call'
		if p.nodes[n].fname == fname
		if p.node_tags[n][0] == tag]
	if len (ns) == 1:
		[n] = ns
		return n
	else:
		return None

def get_call_link_hyps (p, n, (from_tags, from_pair), (to_tags, to_pair),
		focused_loops = None):
	n = find_actual_call_node (p, n)
	fname = p.nodes[n].fname
	assert fname == to_pair.funs['ASM']
	vis = get_vis (p, n, focused_loops = focused_loops)
	hyps = rep_graph.mk_function_link_hyps (p, vis, to_tags['ASM'],
		adjust_eq_seq = adj_eq_seq_for_asm_fun_link (fname))

	c_fname = to_pair.funs['C']
	cn = get_unique_call_site (p, c_fname, from_tags['C'])
	if cn != None:
		vis = get_vis (p, cn, focused_loops = focused_loops)
		hyps += rep_graph.mk_function_link_hyps (p, vis, to_tags['C'])
	return hyps

def refute_minimise_vis_hyps (rep, free_hyps, call_hyps, vis_pcs):
	def test (call_hyps, vis_pcs):
		hs = [h for grp in call_hyps for h in grp] + [
			h for (h, _) in vis_pcs] + free_hyps
		return rep.test_hyp_whyps (syntax.false_term, hs)

	if not test (call_hyps, vis_pcs):
		return None
	for i in range (1, len (call_hyps)):
		vis_pcs2 = [(h, (addr, j)) for (h, (addr, j)) in vis_pcs
			if j < i]
		if test (call_hyps [ - i : ], vis_pcs2):
			call_hyps = call_hyps [ - i : ]
			vis_pcs = vis_pcs2
			break

	vis_pcs.sort (cmp = lambda (h, (addr, i)), (h2, (addr2, j)): j - i)
	kept = []
	for i in range (len (vis_pcs)):
		if not test (call_hyps, kept + vis_pcs[i + 1 :]):
			kept.append (vis_pcs[i])

	return (call_hyps, kept)

verdicts = {}

new_refutes = {}

def previous_verdict (call_stack, f, arc):
	for (stack, points, verdict) in verdicts.get (f, []):
		suffix = call_stack[len (call_stack) - len (stack) : ]
		if tuple (suffix) == tuple (stack):
			if verdict in ('impossible', 'impossible_in_loop'):
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

def all_reachable (p, addrs):
	assert set (addrs) <= set (p.nodes)
	return all ([p.is_reachable_from (addrs[i], addrs[j]) or
			p.is_reachable_from (addrs[j], addrs[i])
		for i in range (len (addrs))
		for j in range (i + 1, len (addrs))])

parent_ctxt_limit = 3

def call_stack_parent_arc_extras (stack, ctxt_arcs, max_length, top_loop):
	rng = range (1, len (stack))[ - parent_ctxt_limit : ][ - max_length : ]
	arc_extras = []
	for i in rng:
		prev_stack = stack[:i]
		f = body_addrs[stack[i]]
		p = functions[f].as_problem (problem.Problem)
		arcs = ctxt_arcs[tuple (prev_stack)]
		if top_loop != None and i == rng[0]:
			assert uniform_loop_id (stack[i]) == top_loop, (stack, i)
			arcs = [[x for x in a if uniform_loop_id (x) == top_loop]
				for a in arcs]
			arcs = [a for a in arcs if a]
		arcs = [a for a in arcs if all_reachable (p, a + [stack[i]])]
		arcs = sorted ([(len (a), a) for a in arcs])
		if arcs:
			(_, arc) = arcs[-1]
			arc_extras.extend ([(addr, len (stack) - i)
				for addr in arc])
	return arc_extras 

def add_arc_extras (arc, extras):
	return [(addr, 0) for addr in arc] + extras

last_refute_attempt = [None]

has_complex_loop_cache = {}

def has_complex_loop (fname):
	if fname in has_complex_loop_cache:
		return has_complex_loop_cache[fname]
	p = functions[fname].as_problem (problem.Problem)
	p.do_analysis ()
	result = bool ([h for h in p.loop_heads ()
		if problem.has_inner_loop (p, h)])
	has_complex_loop_cache[fname] = result
	return result

def pick_stack_setup (call_stack):
	# how much stack to use?
	stack = list (call_stack [ - parent_ctxt_limit : ])
	for (i, addr) in reversed (list (enumerate (stack))):
		f2 = get_body_addrs_fun (addr)
		if should_avoid_fun (f2) or has_complex_loop (f2):
			return (None, stack [ i + 1 : ])
		if uniform_loop_id (addr) != None:
			return (uniform_loop_id (addr), stack [ i : ])
		elif addr_in_loop (addr):
			return (None, stack [ i + 1 : ])
	return (None, stack)

loops_info_cache = {}

def fun_loops_info (fname):
	if fname in loops_info_cache:
		return loops_info_cache[fname]
	p = functions[fname].as_problem (problem.Problem)
	p.do_analysis ()
	info = {}
	for l_id in p.loop_heads ():
		ext_reachable = [n for n in p.loop_body (l_id)
			if [n2 for n2 in p.preds[n] if p.loop_id (n2) != l_id]]
		if ext_reachable != [l_id]:
			trace ("Loop in %s non-uniform, additional entries %s."
				% (fname, ext_reachable))
			uniform = False
		elif problem.has_inner_loop (p, l_id):
			trace ("Loop in %s non-uniform, inner loop." % fname)
			uniform = False
		else:
			assert is_addr (l_id), (fname, l_id)
			uniform = True
		for n in p.loop_body (l_id):
			info[n] = (l_id, uniform)
	loops_info_cache[fname] = info
	return info

def addr_in_loop (addr):
	fname = get_body_addrs_fun (addr)
	info = fun_loops_info (fname)
	if addr not in info:
		return None
	(l_id, uniform) = info[addr]
	return (l_id != None)

def uniform_loop_id (addr):
	fname = get_body_addrs_fun (addr)
	info = fun_loops_info (fname)
	if addr not in info:
		return None
	(l_id, uniform) = info[addr]
	if not uniform:
		return None
	return l_id

def refute_function_arcs (call_stack, arcs, ctxt_arcs):
	last_refute_attempt[0] = (call_stack, arcs, ctxt_arcs)
	f = identify_function (call_stack,
		[(addr, 0) for arc in arcs for addr in arc])

	# easy function limit refutations
	if not (ctxt_within_function_limits (call_stack)
			and function_reachable_within_limits (f)):
		verdicts.setdefault (f, [])
		if call_stack:
			vdct = (call_stack, [], 'impossible')
		else:
			min_addr = min ([addr for arc in arcs for addr in arc])
			vdct = ([], [min_addr], 'impossible')
		verdicts[f].append (vdct)
		new_refutes[f] = True
		print 'added %s refutation %s: %s' % (f, vdct[0], vdct[1])
		return

	# ignore complex loops
	if has_complex_loop (f):
		print 'has complex loop: %s, skipping' % f
		return

	(top_loop, stack) = pick_stack_setup (call_stack)
	arc_extras = call_stack_parent_arc_extras (call_stack, ctxt_arcs,
		len (stack), top_loop)

	arcs = [arc for arc in arcs
		if previous_verdict (stack, f,
			add_arc_extras (arc, arc_extras)) == None]
	if not arcs:
		return

	funs = [body_addrs[addr] for addr in stack] + [f]
	(p, hyps, addr_map, tag_pairs) = build_compound_problem (funs)

	focused_loops = {}
	if top_loop != None:
		top_loop_split = p.loop_id (addr_map[top_loop])
		top_loop_tag = p.node_tags[top_loop_split][0]
		assert top_loop_tag in tag_pairs[0][0].values ()
		focused_loops[top_loop_tag] = top_loop_split

	rep = rep_graph.mk_graph_slice (p)
	call_tags = zip (tag_pairs[:-1], tag_pairs[1:])
	call_hyps = [get_call_link_hyps (p, addr_map[n], from_tp, to_tp,
			focused_loops = focused_loops)
		for (n, (from_tp, to_tp)) in zip (stack, call_tags)]

	for arc in arcs:
		arc2 = add_arc_extras (arc, arc_extras)
		if previous_verdict (stack, f, arc2) != None:
			continue
		print 'fresh %s arc %s: %s' % (f, stack, arc)
		vis_pcs = [(get_pc_hyp_local (rep, addr_map[addr],
				focused_loops = focused_loops), (addr, i))
			for (addr, i) in arc2]
		vis_pcs = dict (vis_pcs).items ()

		res = refute_minimise_vis_hyps (rep, hyps, call_hyps, vis_pcs)
		if res == None:
			verdicts.setdefault (f, [])
			verdicts[f].append ((stack, list (arc2), 'possible'))
			continue

		(used_call_hyps, used_vis_pcs) = res
		stack2 = stack [ - len (used_call_hyps) : ]
		used_vis = [(addr, i) for (_, (addr, i)) in used_vis_pcs]
		verdicts.setdefault (f, [])
		if len (stack2) == len (stack) and top_loop != None:
			vdct = 'impossible_in_loop'
		else:
			vdct = 'impossible'
		verdicts[f].append ((stack2, used_vis, vdct))
		new_refutes[f] = True
		print 'added %s refutation %s: %s' % (f, stack, used_vis)

# function limits. mostly used by loop_bounds, but also present here
def function_limit (fname):
	for hook in target_objects.hooks ('wcet_function_limits'):
		if fname in hook:
			return hook[fname]
	return None

# functions to avoid. won't ever include these in parent contexts for
# arc refutations
def should_avoid_fun (fname):
	for hook in target_objects.hooks ('wcet_functions_to_avoid'):
		if fname in hook:
			return True
	return False

reachable_functions = {}

def build_reachable_functions ():
	fcall_graph = dict ([(fname, functions[fname].function_calls ())
		for fname in functions])
	is_reachable = dict ([(fname, False) for fname in functions])
	called = set ([f for fs in fcall_graph.itervalues () for f in fs])
	uncalled = set (fcall_graph) - called
	frontier = uncalled
	while frontier:
		f = frontier.pop ()
		if is_reachable[f]:
			continue
		elif function_limit (f) == 0:
			continue
		else:
			is_reachable[f] = True
			frontier.update (fcall_graph[f])
	reachable_functions.update (is_reachable)
	reachable_functions[('IsLoaded', None)] = True

def function_reachable_within_limits (fname):
	if fname not in reachable_functions:
		build_reachable_functions ()
	return reachable_functions[fname]

def ctxt_within_function_limits (call_ctxt):
	for (i, addr) in enumerate (call_ctxt):
		fname = identify_function (call_ctxt[:i], [addr])
		if not function_reachable_within_limits (fname):
			return False
	return True

def serialise_verdicts (fname):
	f = open (fname, 'w')
	for (_, vs) in verdicts.iteritems ():
		for (stack, visits, verdict) in vs:
			visit_str = '[%s]' % (','.join (['%d<-%d' % (addr, i)
				for (addr, i) in visits]))
			f.write ('%s: %s: %s\n' % (list (stack), visit_str,
				verdict))
	f.close ()

def load_verdicts (fname):
	f = open (fname)
	for l in f:
		bits = l.split(':')
		if len (bits) < 3:
			bits = set ([bit for bit in bits if bit.strip()])
			assert not bits, bits
		[stack, visits, verdict] = bits
		stack = parse_num_list (stack)
		visits = parse_num_arrow_list (visits)
		verdict = verdict.strip ()
		assert verdict in ('possible', 'impossible',
			'impossible_in_loop'), verdict
		fn = identify_function (stack, visits)
		verdicts.setdefault (fn, [])
		verdicts[fn].append ((stack, visits, verdict))
	f.close ()

last_report = [0]
exceptions = []

def refute (inp_fname, out_fname, prev_fnames, instance = None):
	f = open (inp_fname)
	ctxt_arcs = parse_ctxt_arcs (f)
	f.close ()
	body_addrs.clear ()
	setup_body_addrs ()
	verdicts.clear ()
	new_refutes.clear ()
	for fn in prev_fnames:
		load_verdicts (fn)
	report = {}
	last_report[0] = report
	for (ctxt, arcs) in ctxt_arcs.iteritems ():
		if instance:
			(a, b) = instance
			if hash (('foo', tuple (ctxt))) % b != a:
				continue
		try:
			refute_function_arcs (ctxt, arcs, ctxt_arcs)
			report[ctxt] = 'Success'
		except problem.Abort:
			report[ctxt] = 'ProofAbort'
		except Exception, e:
			import sys, traceback
			exceptions.append ((ctxt, arcs, ctxt_arcs))
			exception = sys.exc_info ()
			(etype, evalue, tb) = exception
			ss = traceback.format_exception (etype, evalue, tb)
			report[ctxt] = '\n'.join (['EXCEPTION'] + ss)
			print 'EXCEPTION in handling %s, %s' % (ctxt, arcs)
			for s in ss[:3]:
				print s
			if len (ss) > 3:
				print '...'
	serialise_verdicts (out_fname)
	print 'Found new refutations: %s' % bool (new_refutes)
	return (bool (new_refutes), report)

if __name__ == '__main__':
	args = target_objects.load_target_args ()
	prevs = [arg[5:] for arg in args if arg.startswith ('prev:')]
	args = [arg for arg in args if not arg.startswith ('prev:')]
	insts = [arg for arg in args if arg.startswith ('instance:')]
	if insts:
		args = [arg for arg in args if not arg.startswith ('instance:')]
		assert len (insts) == 1, insts
		[inst] = insts
		bits = inst.split(':')
		assert len (bits) == 3, (insts, bits)
		[_, a, b] = bits
		instance = (int (a), int (b))
	else:
		instance = None
	if len (args) < 2:
		print 'Usage: python trace_refute <target> <refutables> [prev:output] <output>'
		print 'where <target> as per graph-refine, <refutables> from reconstruct.py'
		print 'and <output> is output filename.'
		print 'Optional previous output may be loaded.'
		print 'e.g. python trace_refute new-gcc-O2 new-gcc-O2/ctxt_arcs.txt prev:refutes.txt refutes.txt'
		sys.exit (1)
	else:
		(new, _) = refute (args[0], args[1], prevs,
			instance = instance)
		import sys
		if new:
			sys.exit (127)
		else:
			sys.exit (0)


