# * Copyright 2015, NICTA
# *
# * This software may be distributed and modified according to the terms of
# * the BSD 2-Clause license. Note that NO WARRANTY is provided.
# * See "LICENSE_BSD2.txt" for details.
# *
# * @TAG(NICTA_BSD)

from target_objects import functions, pairings
import target_objects
from problem import Problem
import problem
import logic
import syntax
import solver
import search
import rep_graph
import check

import random

def check_entry_var_deps (f):
	if not f.entry:
		return set ()
	p = f.as_problem (Problem)
	diff = check_problem_entry_var_deps (p)

	return diff

def check_problem_entry_var_deps (p, var_deps = None):
	if var_deps == None:
		var_deps = p.compute_var_dependencies ()
	for (entry, tag, _, inputs) in p.entries:
		if entry not in var_deps:
			print 'Entry missing from var_deps: %d' % entry
			continue
		diff = set (var_deps[entry]) - set (inputs)
		if diff:
			print 'Vars deps escaped in %s in %s: %s' % (tag,
				p.name, diff)
			return diff
	return set ()

def check_all_var_deps ():
	return [f for f in functions if check_entry_var_deps(functions[f])]

def walk_var_deps (p, n, v, var_deps = None,
			interest = set (), symmetric = False):
	if var_deps == None:
		var_deps = p.compute_var_dependencies ()
	while True:
		if n == 'Ret' or n == 'Err':
			print n
			return n
		if symmetric:
			opts = set ([n2 for n2 in p.preds[n] if n2 in p.nodes])
		else:
			opts = set ([n2 for n2 in p.nodes[n].get_conts ()
				if n2 in p.nodes])
		choices = [n2 for n2 in opts if v in var_deps[n2]]
		if not choices:
			print 'Walk ends at %d.' % n
			return
		if len (choices) > 1:
			print 'choices %s, gambling' % choices
			random.shuffle (choices)
			print ' ... rolled a %s' % choices[0]
		elif len (opts) > 1:
			print 'picked %s from %s' % (choices[0], opts)
		n = choices[0]
		if n in interest:
			print '** %d' % n
		else:
			print n

def diagram_var_deps (p, fname, v, var_deps = None):
	if var_deps == None:
		var_deps = p.compute_var_dependencies ()
	cols = {}
	for n in p.nodes:
		if n not in var_deps:
			cols[n] = 'darkgrey'
		elif v not in var_deps[n]:
			cols[n] = 'darkblue'
		else:
			cols[n] = 'orange'
	problem.save_graph (p.nodes, fname, cols = cols)

def trace_model (rep, m, simplify = True):
	p = rep.p
	tags = set ([tag for (tag, n, vc) in rep.node_pc_env_order])
	if p.pairing and tags == set (p.pairing.tags):
		tags = reversed (p.pairing.tags)
	for tag in tags:
		print "Walking %s in model" % tag
		n_vcs = walk_model (rep, tag, m)
		for (i, (n, vc)) in enumerate (n_vcs):
			if n in ['Ret', 'Err']:
				print 'ends at %s' % n
				break
			node = logic.simplify_node_elementary (p.nodes[n])
			if node.kind != 'Cond':
				continue
			if i + 1 >= len (n_vcs):
				continue
			if n_vc_era (n_vcs[i + 1]) != n_vc_era ((n, vc)):
				continue
			name = rep.cond_name ((n, vc))
			cond = m[name] == syntax.true_term
			print '%s: %s' % (name, cond)
			investigate_cond (rep, m, name, simplify)

def walk_model (rep, tag, m):
	n_vcs = [(n, vc) for (tag2, n, vc) in rep.node_pc_env_order
		if tag2 == tag
		if search.eval_model_expr (m, rep.solv,
				rep.get_pc ((n, vc), tag))
			== syntax.true_term]

	era_sort (rep, n_vcs)

	return n_vcs

def investigate_cond (rep, m, cond, simplify = True, rec = True):
	cond_def = rep.solv.defs[cond]
	while rec and type (cond_def) == str and cond_def in rep.solv.defs:
		cond_def = rep.solv.defs[cond_def]
	bits = solver.split_hyp_sexpr (cond_def, [])
	for bit in bits:
		if bit == 'true':
			continue
		valid = eval_model_bool (m, bit)
		if simplify:
			# looks a bit strange to do this now but some pointer
			# lookups have to be done with unmodified s-exprs
			bit = simplify_sexp (bit, rep, m, flatten = False)
		print '  %s: %s' % (valid, solver.flat_s_expression (bit))

def eval_model_bool (m, x):
	if hasattr (x, 'typ'):
		x = solver.smt_expr (x, {}, None)
		x = solver.parse_s_expression (x)
	try:
		r = search.eval_model (m, x)
		assert r in [syntax.true_term, syntax.false_term], r
		return r == syntax.true_term
	except:
		return 'EXCEPT'

def funcall_name (rep):
	return lambda n_vc: "%s @%s" % (rep.p.nodes[n_vc[0]].fname,
		rep.node_count_name (n_vc))

def n_vc_era ((n, vc)):
	era = 0
	for (split, vcount) in vc:
		(ns, os) = vcount.get_opts ()
		if len (ns + os) > 1:
			era += 3
		elif ns:
			era += 1
		elif os:
			era += 2
	return era

def era_sort (rep, n_vcs):
	with_eras = [(n_vc_era (n_vc), n_vc) for n_vc in n_vcs]
	with_eras.sort (key = lambda x: x[0])
	for i in range (len (with_eras) - 1):
		(e1, n_vc1) = with_eras[i]
		(e2, n_vc2) = with_eras[i + 1]
		if e1 != e2:
			continue
		if n_vc1[0] in ['Ret', 'Err']:
			assert not 'Era issues', n_vcs
		assert rep.is_cont (n_vc1, n_vc2), [n_vc1, n_vc2]
	return [n_vc for (_, n_vc) in with_eras]

def investigate_funcalls (rep, m, verbose = False, verbose_imp = False,
		simplify = True, pairing = 'Eras'):
	l_tag, r_tag = rep.p.pairing.tags
	l_ns = walk_model (rep, l_tag, m)
	r_ns = walk_model (rep, r_tag, m)
	nodes = rep.p.nodes

	l_calls = [n_vc for n_vc in l_ns if n_vc in rep.funcs]
	r_calls = [n_vc for n_vc in r_ns if n_vc in rep.funcs]
	print '%s calls: %s' % (l_tag, map (funcall_name (rep), l_calls))
	print '%s calls: %s' % (r_tag, map (funcall_name (rep), r_calls))

	if pairing == 'Eras':
		fc_pairs = pair_funcalls_by_era (rep, l_calls, r_calls)
	elif pairing == 'Seq':
		fc_pairs = pair_funcalls_sequential (rep, l_calls, r_calls)
	elif pairing == 'All':
		fc_pairs = [(lc, rc) for lc in l_calls for rc in r_calls]
	else:
		assert pairing in ['Eras', 'Seq', 'All'], pairing

	for (l_n_vc, r_n_vc) in fc_pairs:
		if not rep.get_func_pairing (l_n_vc, r_n_vc):
			print 'call seq mismatch: (%s, %s)' % (l_n_vc, r_n_vc)
			continue
		investigate_funcall_pair (rep, m, l_n_vc, r_n_vc,
			verbose, verbose_imp, simplify)

def pair_funcalls_by_era (rep, l_calls, r_calls):
	eras = sorted (set (map (n_vc_era, l_calls + r_calls)))
	pairs = []
	for era in eras:
		ls = [n_vc for n_vc in l_calls if n_vc_era (n_vc) == era]
		rs = [n_vc for n_vc in r_calls if n_vc_era (n_vc) == era]
		if len (ls) != len (rs):
			print 'call seq length mismatch in era %d:' % era
			print map (funcall_name (rep), ls)
			print map (funcall_name (rep), rs)
		pairs.extend (zip (ls, rs))
	return pairs

def pair_funcalls_sequential (rep, l_calls, r_calls):
	if len (l_calls) != len (r_calls):
		print 'call seq tail mismatch'
		if len (l_calls) > len (r_calls):
			print 'dropping lhs: %s' % map (funcall_name (rep),
				l_calls[len (r_calls):])
		else:
			print 'dropping rhs: %s' % map (funcall_name (rep),
				r_calls[len (l_calls):])
	# really should add some smarts to this to 'recover' from upsets or
	# reorders, but maybe not worth it.
	return zip (l_calls, r_calls)

def investigate_funcall_pair (rep, m, l_n_vc, r_n_vc,
		verbose = False, verbose_imp = False, simplify = True):

	l_nm = "%s @ %s" % (rep.p.nodes[l_n_vc[0]].fname, rep.node_count_name (l_n_vc))
	r_nm = "%s @ %s" % (rep.p.nodes[r_n_vc[0]].fname, rep.node_count_name (r_n_vc))
	print 'Attempt match %s -> %s' % (l_nm, r_nm)
	imp = rep.get_func_assert (l_n_vc, r_n_vc)
	if verbose_imp:
		imp2 = logic.weaken_assert (imp)
		imp2 = solver.smt_expr (imp2, {}, rep.solv)
		if simplify:
			imp2 = simplify_sexp (imp2, rep, m)
		print imp2
	assert imp.is_op ('Implies'), imp
	[pred, concl] = imp.vals
	pred = solver.smt_expr (pred, {}, rep.solv)
	pred = solver.parse_s_expression (pred)
	bits = solver.split_hyp_sexpr (pred, [])
	xs = [eval_model_bool (m, v) for v in bits]
	print '  %s' % xs
	for (v, bit) in zip (xs, bits):
		if v != True or verbose:
			print '  %s: %s' % (v, bit)
			if bit[0] == 'word32-eq':
				vs = [model_sx_word (m, x)
					for x in bit[1:]]
				print '    (%s = %s)' % tuple (vs)

def model_sx_word (m, sx):
	v = search.eval_model (m, sx)
	assert v.typ.kind == 'Word'
	x = v.val & ((1 << v.typ.num) - 1)
	return solver.smt_num (x, v.typ.num)

def m_var_name (expr):
	while expr.is_op ('MemUpdate'):
		[expr, p, v] = expr.vals
	if expr.kind == 'Var':
		return expr.name
	elif expr.kind == 'Op':
		return '<Op %s>' % op.name
	else:
		return '<Expr %s>' % expr.kind

def trace_mem (rep, tag, m, verbose = False, simplify = True):
	p = rep.p
	ns = walk_model (rep, tag, m)
	trace = []
	def eval (expr, env):
		s = solver.smt_expr (expr, env, rep.solv)
		s_x = solver.parse_s_expression (s)
		return search.eval_model (m, s_x).val
	for (n, vc) in ns:
		if (n, vc) not in rep.arc_pc_envs:
			# this n_vc has a pre-state, but has not been emitted.
			# no point trying to evaluate its expressions, the
			# solve won't have seen them yet.
			continue
		n_nm = rep.node_count_name ((n, vc))
		node = p.nodes[n]
		if node.kind == 'Call':
			msg = '<function call to %s at %s>' % (node.fname, n_nm)
			print msg
			trace.append (msg)
		if node.kind == 'Basic':
			exprs = [expr for (_, expr) in node.upds]
		elif node.kind == 'Cond':
			exprs = [node.cond]
		else:
			continue
		env = rep.node_pc_envs[(tag, n, vc)][1]
		accs = list (set ([acc for expr in exprs
			for acc in expr.get_mem_accesses ()]))
		for (kind, addr, v, mem) in accs:
			addr_s = solver.smt_expr (addr, env, rep.solv)
			v_s = solver.smt_expr (v, env, rep.solv)
			addr = eval (addr, env)
			v = eval (v, env)
			m_nm = m_var_name (mem)
			print '%s: %s @ <0x%08x>   -- 0x%08x -- %s' % (kind, m_nm, addr, v, n_nm)
			if simplify:
				addr_s = simplify_sexp (addr_s, rep, m)
				v_s = simplify_sexp (v_s, rep, m)
			if verbose:
				print '\t %s -- %s' % (addr_s, v_s)
			trace.extend(accs)
	return trace

def simplify_sexp (smt_xp, rep, m, flatten = True):
	if type (smt_xp) == str:
		smt_xp = solver.parse_s_expression (smt_xp)
	if smt_xp[0] == 'ite':
		(_, c, x, y) = smt_xp
		if eval_model_bool (m, c):
			return simplify_sexp (x, rep, m, flatten)
		else:
			return simplify_sexp (y, rep, m, flatten)
	if type (smt_xp) == tuple:
		smt_xp = tuple ([simplify_sexp (x, rep, m, False)
			for x in smt_xp])
	if flatten:
		return solver.flat_s_expression (smt_xp)
	else:
		return smt_xp

def trace_mems (rep, m, verbose = False):
	for tag in reversed (rep.p.pairing.tags):
		print '%s mem trace:' % tag
		trace_mem (rep, tag, m, verbose = verbose)

def trace_var (rep, tag, m, v):
	p = rep.p
	ns = walk_model (rep, tag, m)
	trace = []
	def eval (expr, env):
		try:
			s = solver.smt_expr (expr, env, rep.solv)
			s_x = solver.parse_s_expression (s)
			ev = search.eval_model (m, s_x)
			return (s, solver.smt_expr (ev, {}, None))
		except solver.EnvMiss, e:
			return None
		except AssertionError, e:
			return None
	val = None
	for (n, vc) in ns:
		(_, env) = rep.get_node_pc_env ((n, vc), tag)
		n_nm = rep.node_count_name ((n, vc))
		val2 = eval (v, env)
		if val2 != val:
			print 'at %s:\t\t%s:\t\t%s' % (n_nm, val2[0], val2[1])
			val = val2
			trace.append (((n, vc), val))
		if n not in p.nodes:
			break
		node = p.nodes[n]
		if node.kind == 'Call':
			msg = '<function call to %s at %s>' % (node.fname,
				rep.node_count_name ((n, vc)))
			print msg
			trace.append (msg)
	return trace

def check_pairings ():
	for p in pairings.itervalues ():
		print p['C'], p['ASM']
		as_args = functions[p['ASM']].inputs
		c_args = functions[p['C']].inputs
		print as_args, c_args
		logic.mk_fun_inp_eqs (as_args, c_args, True)

def loop_var_deps (p):
	return [(n, [v for v in p.var_deps[n]
			if p.var_deps[n][v] == 'LoopVariable'])
		for n in p.loop_data]

def find_symbol (n):
	from target_objects import symbols, sections
	for (s, (addr, size, _)) in symbols.iteritems ():
		if addr <= n and n < addr + size:
			print '%x in %s (%x - %x)' % (n, s, addr, addr + size - 1)
	for (s, (start, end)) in sections.iteritems ():
		if start <= n and n <= end:
			print '%x in section %s (%x - %x)' % (n, s, start, end)

def assembly_point (p, n):
	(_, hints) = p.node_tags[n]
	if type (hints) != tuple or not logic.is_int (hints[1]):
		return None
	while p.node_tags[n][1][1] % 4 != 0:
		[n] = p.preds[n]
	return p.node_tags[n][1][1]

def assembly_points (p, ns):
	ns = [assembly_point (p, n) for n in ns]
	ns = [n for n in ns if n != None]
	return ns

def disassembly_lines (addrs):
	f = open ('%s/kernel.elf.txt' % target_objects.target_dir)
	addr_set = set (['%x' % addr for addr in addrs])
	ss = [l.strip ()
		for l in f if ':' in l and l.split(':', 1)[0] in addr_set]
	return ss

def disassembly (p, n):
	if hasattr (n, '__iter__'):
		ns = set (n)
	else:
		ns = [n]
	addrs = sorted (set ([assembly_point (p, n) for n in ns])
		- set ([None]))
	print 'asm %s' % ', '.join (['0x%x' % addr for addr in addrs])
	for s in disassembly_lines (addrs):
		print s

def disassembly_loop (p, n):
	head = p.loop_id (n)
	loop = p.loop_body (n)
	ns = sorted (set (assembly_points (p, loop)))
	entries = assembly_points (p, [n for n in p.preds[head]
		if n not in loop])
	print 'Loop: [%s]' % ', '.join (['%x' % addr for addr in ns])
	for s in disassembly_lines (ns):
		print s
	print 'entry from %s' % ', '.join (['%x' % addr for addr in entries])
	for s in disassembly_lines (entries):
		print s

def try_interpret_hyp (rep, hyp):
	try:
		expr = rep.interpret_hyp (hyp)
		solver.smt_expr (expr, {}, rep.solv)
		return None
	except:
		return ('Broken Hyp', hyp)

def check_checks ():
	p = problem.last_problem[0]
	rep = rep_graph.mk_graph_slice (p)
	proof = search.last_proof[0]
	checks = check.proof_checks (p, proof)
	all_hyps = set ([hyp for (_, hyp, _) in checks]
		+ [hyp for (hyps, _, _) in checks for hyp in hyps])
	results = [try_interpret_hyp (rep, hyp) for hyp in all_hyps]
	return [r[1] for r in results if r]

def proof_failed_groups (p = None, proof = None):
	if p == None:
		p = problem.last_problem[0]
	if proof == None:
		proof = search.last_proof[0]
	checks = check.proof_checks (p, proof)
	groups = check.proof_check_groups (checks)
	failed = []
	for group in groups:
		rep = rep_graph.mk_graph_slice (p)
		if not check.test_hyp_group (rep, group):
			failed.append (group)
	failed_nms = set ([s for group in failed for (_, _, s) in group])
	print 'Failed: %s' % failed_nms
	return failed

def read_summary (f):
	results = {}
	times = {}
	for line in f:
		if not line.startswith ('Time taken to'):
			continue
		bits = line.split ()
		assert bits[:4] == ['Time', 'taken', 'to', 'check']
		res = bits[4]
		[ref] = [i for (i, b) in enumerate (bits) if b == '<=']
		f = bits[ref + 1]
		[pair] = [pair for pair in pairings[f]
			if pair.name in line]
		time = float (bits[-1])
		results[pair] = res
		times[pair] = time
	return (results, times)


