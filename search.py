# * Copyright 2015, NICTA
# *
# * This software may be distributed and modified according to the terms of
# * the BSD 2-Clause license. Note that NO WARRANTY is provided.
# * See "LICENSE_BSD2.txt" for details.
# *
# * @TAG(NICTA_BSD)

import solver
from solver import mk_smt_expr, to_smt_expr, smt_expr
import check
from check import restr_others, loops_to_split, ProofNode
from rep_graph import (mk_graph_slice, vc_num, vc_offs, vc_upto,
	vc_double_range, VisitCount, vc_offset_upto)
from syntax import (mk_and, mk_cast, mk_implies, mk_not, mk_uminus, mk_var,
	foldr1, boolT, word32T, word8T, builtinTs, true_term, false_term,
	mk_word32, mk_word8, mk_times, Expr, Type, mk_or, mk_eq, mk_memacc)
import syntax
import logic

from target_objects import trace, printout
import target_objects

last_knowledge = [1]

class NoSplit(Exception):
	pass

def get_loop_var_analysis_at (p, n):
	for hook in target_objects.hooks ('loop_var_analysis'):
		res = hook (p, n)
		if res != None:
			return res
	var_deps = p.compute_var_dependencies ()
	return p.get_loop_var_analysis (var_deps, n)

def get_loop_vars_at (p, n):
	vs = [var for (var, data) in get_loop_var_analysis_at (p, n)
			if data == 'LoopVariable'] + [mk_word32 (0)]
	vs.sort ()
	return vs

default_loop_N = 3

last_proof = [None]

def build_proof (p):
	init_hyps = check.init_point_hyps (p)
	proof = build_proof_rec (default_searcher, p, (), list (init_hyps))

	trace ('Built proof for %s' % p.name)
	printout (repr (proof))
	last_proof[0] = proof

	return proof

def split_sample_set (bound):
	ns = (range (10) + range (10, 20, 2)
		+ range (20, 40, 5) + range (40, 100, 10)
		+ range (100, 1000, 50))
	return [n for n in ns if n < bound]

def find_split_limit (p, n, restrs, hyps, kind, bound = 51, must_find = True,
		hints = [], use_rep = None):
	tag = p.node_tags[n][0]
	trace ('Finding split limit: %d (%s) %s' % (n, tag, restrs))
	trace ('  (restrs = %s)' % (restrs, ))
	trace ('  (hyps = %s)' % (hyps, ), push = 1)
	if use_rep == None:
		rep = mk_graph_slice (p, fast = True)
	else:
		rep = use_rep
	check_order = hints + [i for i in split_sample_set (bound)
		if i not in hints]
	for i in check_order:
		restrs2 = restrs + ((n, VisitCount (kind, i)), )
		pc = rep.get_pc ((n, restrs2))
		restrs3 = restr_others (p, restrs2, 2)
		epc = rep.get_pc (('Err', restrs3), tag = tag)
		hyp = mk_implies (mk_not (epc), mk_not (pc))
		if rep.test_hyp_whyps (hyp, hyps):
			trace ('split limit found: %d' % i, push = -1)
			return i

	trace ('No split limit found for %d (%s).' % (n, tag), push = -1)
	if must_find:
		assert not 'split limit found'
	return None

def get_var_pc_var_list (knowledge, v_i):
	(rep, (restrs, _, _, _), _, _) = knowledge
	(v_i, i, i_offs, i_step) = v_i
	def get_var (k):
		head = rep.p.loop_id (i)
		if i != head:
			k += 1
		restrs2 = restrs + ((head, vc_num (k)), )
		(pc, env) = rep.get_node_pc_env ((i, restrs2))
		return (to_smt_expr (pc, env, rep.solv),
			to_smt_expr (v_i, env, rep.solv))
	return [get_var (i_offs + (k * i_step))
		for k in [0, 1, 2]]

def expand_var_eqs (knowledge, (v_i, v_j)):
	(rep, (restrs, _, _, _), _, _) = knowledge

	if v_j == 'Const':
		pc_vs = get_var_pc_var_list (knowledge, v_i)
		(_, v0) = pc_vs[0]
		return [mk_implies (pc, mk_eq (v, v0))
			for (pc, v) in pc_vs[1:]]
	# sorting the vars guarantees we generate the same
	# mem eqs each time which is important for the solver
	(v_i, v_j) = sorted ([v_i, v_j])
	pc_vs = zip (get_var_pc_var_list (knowledge, v_i),
		get_var_pc_var_list (knowledge, v_j))
	return [pred for ((pc_i, v_i), (pc_j, v_j)) in pc_vs
		for pred in [mk_eq (pc_i, pc_j),
			mk_implies (pc_i, logic.mk_eq_with_cast (v_i, v_j))]]

word_ops = {'bvadd':lambda x, y: x + y, 'bvsub':lambda x, y: x - y,
	'bvmul':lambda x, y: x * y, 'bvurem':lambda x, y: x % y,
	'bvudiv':lambda x, y: x / y, 'bvand':lambda x, y: x & y,
	'bvor':lambda x, y: x | y, 'bvxor': lambda x, y: x ^ y,
	'bvnot': lambda x: ~ x, 'bvneg': lambda x: - x,
	'bvshl': lambda x, y: x << y, 'bvlshr': lambda x, y: x >> y}

bool_ops = {'=>':lambda x, y: (not x) or y, '=': lambda x, y: x == y,
	'not': lambda x: not x, 'true': lambda: True, 'false': lambda: False}

word_ineq_ops = {'=': (lambda x, y: x == y, 'Unsigned'),
	'bvult': (lambda x, y: x < y, 'Unsigned'),
	'word32-eq': (lambda x, y: x == y, 'Unsigned'),
	'bvule': (lambda x, y: x <= y, 'Unsigned'),
	'bvsle': (lambda x, y: x <= y, 'Signed'),
	'bvslt': (lambda x, y: x < y, 'Signed'),
}

def eval_model (m, s, toplevel = None):
	if s in m:
		return m[s]
	if toplevel == None:
		toplevel = s
	if type (s) == str:
		try:
			result = solver.smt_to_val (s)
		except Exception, e:
			trace ('Error with eval_model')
			trace (toplevel)
			raise e
		return result

	op = s[0]

	if op == 'ite':
		[_, b, x, y] = s
		b = eval_model (m, b, toplevel)
		assert b in [false_term, true_term]
		if b == true_term:
			result = eval_model (m, x, toplevel)
		else:
			result = eval_model (m, y, toplevel)
		m[s] = result
		return result
	
	xs = [eval_model (m, x, toplevel) for x in s[1:]]

	if op[0] == '_' and op[1] == 'zero_extend':
		[_, _, n_extend] = op
		n_extend = int (n_extend)
		[x] = xs
		assert x.typ.kind == 'Word' and x.kind == 'Num'
		result = Expr ('Num', Type ('Word', x.typ.num + n_extend),
			val = x.val)
	elif op[0] == '_' and op[1] == 'extract':
		[_, _, n_top, n_bot] = op
		n_top = int (n_top)
		n_bot = int (n_bot)
		[x] = xs
		assert x.typ.kind == 'Word' and x.kind == 'Num'
		length = (n_top - n_bot) + 1
		result = Expr ('Num', Type ('Word', length),
			val = (x.val >> n_bot) & ((1 << length) - 1))
	elif op[0] == 'store-word32':
		(m, p, v) = xs
		(naming, eqs) = m
		eqs = dict (eqs)
		eqs[p.val] = v.val
		eqs = tuple (sorted (eqs.items ()))
		result = (naming, eqs)
	elif op[0] == 'store-word8':
		(m, p, v) = xs
		p_al = p.val & -4
		shift = (p.val & 3) * 8
		(naming, eqs) = m
		eqs = dict (eqs)
		prev_v = eqs[p_al]
		mask_v = prev_v & (((1 << 32) - 1) ^ (255 << shift))
		new_v = mask_v | ((v.val & 255) << shift)
		eqs[p.val] = new_v
		eqs = tuple (sorted (eqs.items ()))
		result = (naming, eqs)
	elif op[0] == 'load-word32':
		(m, p) = xs
		(naming, eqs) = m
		eqs = dict (eqs)
		result = syntax.mk_word32 (eqs[p.val])
	elif op[0] == 'load-word8':
		(m, p) = xs
		p_al = p.val & -4
		shift = (p.val & 3) * 8
		(naming, eqs) = m
		eqs = dict (eqs)
		v = (eqs[p_al] >> shift) & 255
		result = syntax.mk_word8 (v)
	elif xs and xs[0].typ.kind == 'Word' and op in word_ops:
		for x in xs:
			assert x.kind == 'Num', (s, op, x)
		result = word_ops[op](* [x.val for x in xs])
		result = result & ((1 << xs[0].typ.num) - 1)
		result = Expr ('Num', xs[0].typ, val = result)
	elif xs and xs[0].typ.kind == 'Word' and op in word_ineq_ops:
		(oper, signed) = word_ineq_ops[op]
		if signed == 'Signed':
			result = oper (* map (get_signed_val, xs))
		else:
			assert signed == 'Unsigned'
			result = oper (* [x.val for x in xs])
		result = {True: true_term, False: false_term}[result]
	elif op == 'and':
		result = all ([x == true_term for x in xs])
		result = {True: true_term, False: false_term}[result]
	elif op == 'or':
		result = bool ([x for x in xs if x == true_term])
		result = {True: true_term, False: false_term}[result]
	elif op in bool_ops:
		assert all ([x.typ == boolT for x in xs])
		result = bool_ops[op](* [x == true_term for x in xs])
		result = {True: true_term, False: false_term}[result]
	else:
		assert not 's_expr handled', (s, op)
	m[s] = result
	return result

def get_signed_val (x):
	assert x.typ.kind == 'Word'
	bits = x.typ.num
	v = x.val & ((1 << bits) - 1)
	if v >= (1 << (bits - 1)):
		v = v - (1 << bits)
	return v

def short_array_str (arr):
	items = [('%x: %x' % (p.val * 4, v.val))
		for (p, v) in arr.iteritems ()
		if type (p) != str]
	items.sort ()
	return '{' + ', '.join (items) + '}'

def eval_model_expr (m, solv, v):
	s = solver.smt_expr (v, {}, solv)
	s_x = solver.parse_s_expression (s)

	return eval_model (m, s_x)

def model_equal (m, knowledge, vpair):
	(rep, _, _, _) = knowledge
	preds = expand_var_eqs (knowledge, vpair)
	for pred in preds:
		x = eval_model_expr (m, rep.solv, pred)
		assert x in [syntax.true_term, syntax.false_term]
		if x == syntax.false_term:
			return False
	return True

def get_model_trace (knowledge, m, v):
	(rep, _, _, _) = knowledge
	pc_vs = get_var_pc_var_list (knowledge, v)
	trace = []
	for (pc, v) in pc_vs:
		x = eval_model_expr (m, rep.solv, pc)
		assert x in [syntax.true_term, syntax.false_term]
		if x == syntax.false_term:
			trace.append (None)
		else:
			trace.append (eval_model_expr (m, rep.solv, v))
	return tuple (trace)

def split_group (knowledge, m, group):
	group = list (set (group))
	if group[0][0][0].typ == syntax.builtinTs['Mem']:
		bins = []
		for (v, const) in group:
			for i in range (len (bins)):
				if model_equal (m, knowledge,
						(v, bins[i][1][0])):
					bins[i][1].append (v)
					break
			else:
				if const:
					const = model_equal (m, knowledge,
						(v, 'Const'))
				bins.append ((const, [v]))
		return bins
	else:
		bins = {}
		for (v, const) in group:
			trace = get_model_trace (knowledge, m, v)
			if trace not in bins:
				tconst = len (set (trace) - set ([None])) <= 1
				bins[trace] = (const and tconst, [])
			bins[trace][1].append (v)
		return bins.values ()

def update_knowledge_for_model (knowledge, m):
	(rep, _, (pairs, vs), _) = knowledge
	# first update the live variables
	groups = {}
	for v in vs:
		(k, const) = vs[v]
		groups.setdefault (k, [])
		groups[k].append ((v, const))
	k_counter = 1
	vs.clear ()
	for k in groups:
		for (const, xs) in split_group (knowledge, m, groups[k]):
			for x in xs:
				vs[x] = (k_counter, const)
			k_counter += 1
	# then figure out which pairings are still viable
	needed_ks = set ()
	for (pair, data) in pairs.items ():
		if data[0] == 'Failed':
			continue
		(lvs, rvs) = data
		lv_ks = set ([vs[v][0] for v in lvs if not vs[v][1]])
		rv_ks = set ([vs[v][0] for v in rvs])
		miss_vars = lv_ks - rv_ks
		if miss_vars:
			lv_miss = [v[0] for v in lvs if vs[v][0] in miss_vars]
			pairs[pair] = ('Failed', lv_miss.pop ())
		else:
			needed_ks.update ([vs[v][0] for v in lvs + rvs])
	# then drop any vars which are no longer relevant
	for v in vs.keys ():
		if vs[v][0] not in needed_ks:
			del vs[v]

def init_knowledge_pairs (rep, loop_elts, cand_r_loop_elts):
	v_is = [(i, i_offs, i_step,
		[(v, i, i_offs, i_step) for v in get_loop_vars_at (rep.p, i)])
		for (i, i_offs, i_step) in sorted (loop_elts)]
	l_vtyps = set ([v[0].typ for (_, _, _, vs) in v_is for v in vs])
	v_js = [(j, j_offs, j_step,
		[(v, j, j_offs, j_step) for v in get_loop_vars_at (rep.p, j)
			if v.typ in l_vtyps])
		for (j, j_offs, j_step) in sorted (cand_r_loop_elts)]
	vs = {}
	for (_, _, _, var_vs) in v_is + v_js:
		for v in var_vs:
			vs[v] = (v[0].typ, True)
	pairs = {}
	for (i, i_offs, i_step, i_vs) in v_is:
		for (j, j_offs, j_step, j_vs) in v_js:
			pair = ((i, i_offs, i_step), (j, j_offs, j_step))
			pairs[pair] = (i_vs, j_vs)
	return (pairs, vs)

def debug_pair_eqs (knowledge, pair):
	(rep, data, _, _) = knowledge
	p = rep.p

	((i, i_offs, i_step), (j, j_offs, j_step)) = pair
	v_is = [(v, i, i_offs, i_step) for v in get_loop_vars_at (p, i)]
	v_js = [(v, j, j_offs, j_step) for v in get_loop_vars_at (p, j)]

	vs = {}
	for v in v_is + v_js:
		vs[v] = (v[0].typ, True)

	knowledge2 = (rep, data, ({pair: (v_is, v_js)}, vs), set ())
	eqs = unknown_eqs (knowledge2, 10000)
	preds = [pred for vpair in eqs
		for pred in expand_var_eqs (knowledge2, vpair)]

	return (eqs, preds)

def add_model (knowledge, preds):
	(rep, (_, _, _, premise), _, facts) = knowledge
	if preds:
		pred_expr = foldr1 (mk_and, preds)
	else:
		# we want to learn something, either a new model, or that
		# all of our predicates are true. if there are no predicates,
		# ''all our predicates are true'' is trivially true. instead
		# we must want a model (counterexample of false)
		pred_expr = false_term
	m = {}
	r = rep.solv.check_hyp (mk_implies (premise, pred_expr), {}, model = m)
	if r == 'unsat':
		if not preds:
			trace ('WARNING: unsat with no extra assertions.')
			trace ("  ... learning procedure isn't going to work.")
		for pred in preds:
			facts.add (pred)
	else:
		assert r == 'sat'
		update_knowledge_for_model (knowledge, m)

def add_model_wrapper (knowledge, eqs):
	(_, _, _, facts) = knowledge
	preds = [pred for vpair in eqs
		for pred in expand_var_eqs (knowledge, vpair)
		if pred not in facts]

	add_model (knowledge, preds)

def mk_pairing_v_eqs (knowledge, pair):
	(_, _, (pairs, vs), _) = knowledge
	v_eqs = []
	(lvs, rvs) = pairs[pair]
	zero = mk_word32 (0)
	for v_i in lvs:
		(k, const) = vs[v_i]
		if const and v_i[0] != zero:
			if eq_known (knowledge, (v_i, 'Const')):
				v_eqs.append ((v_i, 'Const'))
				continue
		vs_j = [v_j for v_j in rvs if vs[v_j][0] == k]
		vs_j = [v_j for v_j in vs_j
			if eq_known (knowledge, (v_i, v_j))]
		if not vs_j:
			return None
		if v_i[0] == zero:
			continue
		v_j = vs_j[0]
		v_eqs.append ((v_i, v_j))
	return v_eqs

def unknown_eqs (knowledge, number_eqs):
	(rep, _, (pairs, vs), _) = knowledge
	eq_sets = {}
	eqs = []
	for (pair, data) in pairs.iteritems ():
		if data[0] == 'Failed':
			continue
		(lvs, rvs) = data
		for lv in lvs:
			(k, const) = vs[lv]
			eq_sets.setdefault (k, set ())
			for rv in rvs:
				if vs[rv][0] == k:
					eq_sets[k].add ((1, lv, rv))
			if const:
				eq_sets[k].add ((2, lv, 'Const'))
	eq_sets = [[(lv, rv) for (_, lv, rv) in sorted (eq_sets[k])]
		for k in sorted (eq_sets)]
	# pick some equalities from various sets
	while eq_sets and len (eqs) < number_eqs:
		eq_set = eq_sets.pop (0)
		if not eq_set:
			continue
		vpair = eq_set.pop ()
		if eq_set:
			eq_sets.append(eq_set)
		if not eq_known (knowledge, vpair):
			eqs.append (vpair)
	return eqs

def eq_known (knowledge, vpair):
	preds = expand_var_eqs (knowledge, vpair)
	(rep, _, _, facts) = knowledge
	return set (preds) <= facts

def find_split_loop (p, head, restrs, hyps):
	assert p.loop_data[head][0] == 'Head'
	assert p.node_tags[head][0] == p.pairing.tags[0]
	
	# the idea is to loop through testable hyps, starting with ones that
	# need smaller models (the most unfolded models will time out for
	# large problems like finaliseSlot)

	rep = mk_graph_slice (p, fast = True)
	
	i_seq_opts = [(0, 1), (1, 1), (2, 1), (3, 1)]
	j_seq_opts = [(0, 1), (0, 2), (1, 1), (1, 2), (2, 1), (2, 2), (3, 1)]
	opts_by_lim = {}
	for (start, step) in i_seq_opts:
		limit = start + (2 * step) + 1
		opts_by_lim.setdefault (limit, ([], []))
		opts_by_lim[limit][0].append ((start, step))
	for (start, step) in j_seq_opts:
		limit = start + (2 * step) + 1
		opts_by_lim.setdefault (limit, ([], []))
		opts_by_lim[limit][1].append ((start, step))

	ind_fails = []

	i_opts = []
	j_opts = []
	for unfold_limit in sorted (opts_by_lim):
		trace ('Split search at %d with unfold limit %d.' % (head,
			unfold_limit), push = 1)
		i_opts.extend (opts_by_lim[unfold_limit][0])
		j_opts.extend (opts_by_lim[unfold_limit][1])
		result = find_split (rep, head, restrs, hyps,
			i_opts, j_opts, unfold_limit)
		trace ('Split search with unfold limit %d result: %r'
			% (unfold_limit, result), push = -1)
		if result[0] != None:
			return result
		ind_fails.extend (result[1])

	result = find_case_split (p, head, restrs, hyps)
	if result[0] != None:
		return result

	trace ('All split strategies exhausted.')
	if ind_fails:
		trace ('Warning: inductive failures: %s' % ind_fails)
	raise NoSplit ()

last_failed_pairings = []

def find_split (rep, head, restrs, hyps, i_opts, j_opts, unfold_limit,
		tags = None):
	p = rep.p

	if tags:
		l_tag, r_tag = tags
	else:
		l_tag, r_tag = p.pairing.tags
	loop_elts = [(n, start, step) for n in p.loop_data[head][1]
		if p.loop_splittables[n]
		for (start, step) in i_opts]
	init_to_split = init_loops_to_split (p, restrs)
	r_to_split = [n for n in init_to_split if p.node_tags[n][0] == r_tag] 
	cand_r_loop_elts = [(n2, start, step) for n in r_to_split
		for n2 in p.loop_data[n][1]
		if p.loop_splittables[n2]
		for (start, step) in j_opts]

	err_restrs = restr_others (p, tuple ([(sp, vc_upto (unfold_limit))
		for sp in r_to_split]) + restrs, 1)
	nrerr_pc = mk_not (rep.get_pc (('Err', err_restrs), tag = r_tag))

	def get_pc (n, k):
		head = p.loop_id (n)
		assert head in init_to_split
		if n != head:
			k += 1
		restrs2 = restrs + ((head, vc_num (k)), )
		return rep.get_pc ((n, restrs2))

	for n in r_to_split:
		get_pc (n, unfold_limit)
	get_pc (head, unfold_limit)

	premise = foldr1 (mk_and, [nrerr_pc] + map (rep.interpret_hyp, hyps))
	premise = logic.weaken_assert (premise)

	knowledge = (rep, (restrs, loop_elts, cand_r_loop_elts, premise),
		init_knowledge_pairs (rep, loop_elts, cand_r_loop_elts), set ())
	last_knowledge[0] = knowledge

	# make sure the representation is in sync
	rep.test_hyp_whyps (true_term, hyps)

	# make sure all mem eqs are being tracked
	(_, _, (pairs, vs), _) = knowledge
	mem_vs = [v for v in vs if v[0].typ == builtinTs['Mem']]
	for (i, v) in enumerate (mem_vs):
		for v2 in mem_vs[:i]:
			for pred in expand_var_eqs (knowledge, (v, v2)):
				smt_expr (pred, {}, rep.solv)
	for v in vs:
		for pred in expand_var_eqs (knowledge, (v, 'Const')):
			smt_expr (pred, {}, rep.solv)

	# start the process with a model
	add_model (knowledge, [mk_not (get_pc (head, unfold_limit))])

	num_eqs = 3
	while True:
		trace ('Search at unfold limit %d' % unfold_limit)
		trace ('Computing live pairings')
		pair_eqs = [(pair, mk_pairing_v_eqs (knowledge, pair))
			for pair in sorted (pairs)
			if pairs[pair][0] != 'Failed']
		endorsed = [(pair, eqs) for (pair, eqs) in pair_eqs
			if eqs != None]
		trace (' ... %d live pairings, %d endorsed' %
			(len (pair_eqs), len (endorsed)))
		for (pair, eqs) in endorsed:
			split = v_eqs_to_split (p, pair, eqs, restrs, hyps)
			if split == None:
				pairs[pair] = ('Failed', 'SplitWeak', eqs)
				continue
			if check_split_induct (p, restrs, hyps, split):
				trace ('Tested v_eqs!')
				return ('Split', split)
			else:
				pairs[pair] = ('Failed', 'InductFailed', eqs)

		u_eqs = unknown_eqs (knowledge, num_eqs)
		if not u_eqs:
			trace (('Exhausted split candidates for loop at %d,'
				+ ' unfold limit %d') % (head, unfold_limit))
			fails = [it for it in pairs.items ()
				if it[1][0] == 'Failed']
			fails10 = fails[:10]
			trace ('  %d of %d failed pairings:' % (len (fails10),
				len (fails)))
			last_failed_pairings.append (fails)
			del last_failed_pairings[:-10]
			for f in fails:
				trace ('    %s' % (f,))
			ind_fails = [it for it in fails
				if str (it[1][1]) == 'InductFailed']
			if ind_fails:
				trace (  'Inductive failures!')
			for f in ind_fails:
				trace ('    %s' % (f,))
			return (None, ind_fails)
		
		add_model_wrapper (knowledge, u_eqs)
		num_eqs = 4 - num_eqs # oscillate between 3, 1

def find_case_split (p, head, restrs, hyps):
	# are there multiple paths to the loop head 'head' and can we
	# restrict to one of them?
	preds = set ()
	frontier = [n2 for n2 in p.preds[head]
		if p.loop_id (n2) != head]
	while frontier:
		n2 = frontier.pop ()
		if n2 in preds:
			continue
		preds.add (n2)
		frontier.extend (p.preds[n2])
	divs = [n2 for n2 in preds if len (set ([n3
		for n3 in p.nodes[n2].get_conts ()
			if n3 in preds or n3 == head])) > 1
		if n2 not in p.loop_data]

	rep = mk_graph_slice (p)
	err_restrs = restr_others (p, restrs, 2)
	l_tag, r_tag = p.pairing.tags
	nrerr_pc = mk_not (rep.get_pc (('Err', err_restrs), tag = r_tag))

	# for this to be a usable case split, both paths must be possible
	for div in divs:
		assert p.nodes[div].kind == 'Cond'
		(_, env) = rep.get_node_pc_env ((div, restrs))
		c = to_smt_expr (p.nodes[div].cond, env, rep.solv)
		if (rep.test_hyp_whyps (mk_implies (nrerr_pc, c), hyps)
			or rep.test_hyp_whyps (mk_implies (nrerr_pc,
				mk_not (c)), hyps)):
			continue
		trace ("attempting case split at %d" % div)
		sides = [n for n in p.nodes[div].get_conts ()
			if n not in p.loop_data
			if p.preds[n] == [div]]
		if not sides:
			trace ("skipping case split, no notable succ")
		n = sides[0]
		return ('CaseSplit', (n, p.node_tags[n][0]))
	trace ('find_case_split: no case splits possible')
	return (None, ())

def mk_seq_eqs (p, split, step, with_rodata):
	# eqs take the form of a number of constant expressions
	eqs = []

	# the variable 'loop' will be converted to the point in
	# the sequence - note this should be multiplied by the step size
	loop = mk_var ('%i', word32T)
	if step == 1:
		minus_loop_step = mk_uminus (loop)
	else:
		minus_loop_step = mk_times (loop, mk_word32 (- step))

	for (var, data) in get_loop_var_analysis_at (p, split):
		if data == 'LoopVariable':
			if with_rodata and var.typ == builtinTs['Mem']:
				eqs.append (logic.mk_rodata (var))
		elif data == 'LoopConst':
			if var.typ not in syntax.phantom_types:
				eqs.append (var)
		elif data == 'LoopLeaf':
			continue
		elif data[0] == 'LoopLinearSeries':
			(_, form, _) = data
			eqs.append (form (var, minus_loop_step))
		else:
			assert not 'var_deps type understood'

	return eqs

def c_memory_loop_invariant (p, c_sp, a_sp):
	def mem_vars (split):
		return [v for (v, data) in get_loop_var_analysis_at (p, split)
			if v.typ == builtinTs['Mem']
			if data == 'LoopVariable']

	if mem_vars (a_sp):
		return []
	# if ASM keeps memory constant through the loop, it is implying this
	# is semantically possible in C also, though it may not be
	# syntactically the case
	# anyway, we have to assert C memory equals *something* inductively
	# so we pick C initial memory.
	return mem_vars (c_sp)

def v_eqs_to_split (p, pair, v_eqs, restrs, hyps):
	trace ('v_eqs_to_split: (%s, %s)' % pair)

	((l_n, l_init, l_step), (r_n, r_init, r_step)) = pair
	l_details = (l_n, (l_init, l_step), mk_seq_eqs (p, l_n, l_step, True)
		+ [v_i[0] for (v_i, v_j) in v_eqs if v_j == 'Const'])
	r_details = (r_n, (r_init, r_step), mk_seq_eqs (p, r_n, r_step, False)
		+ c_memory_loop_invariant (p, r_n, l_n))

	eqs = [(v_i[0], mk_cast (v_j[0], v_i[0].typ))
		for (v_i, v_j) in v_eqs if v_j != 'Const']

	n = 2
	split = (l_details, r_details, eqs, n, (n * r_step) - 1)
	trace ('Split: %s' % (split, ))
	hyps = hyps + check.split_loop_hyps (p.pairing.tags, split,
		restrs, exit = True)

	r_max = find_split_limit (p, r_n, restrs, hyps, 'Offset',
		bound = (n + 2) * r_step, must_find = False,
		hints = [n * r_step, n * r_step + 1])
	if r_max == None:
		trace ('v_eqs_to_split: no RHS limit')
		return None

	if r_max > n * r_step:
		trace ('v_eqs_to_split: RHS limit not %d' % (n * r_step))
		return None
	trace ('v_eqs_to_split: split %s' % (split,))
	return split

def get_n_offset_successes (rep, sp, step, restrs):
	loop = rep.p.loop_body (sp)
	ns = [n for n in loop if rep.p.nodes[n].kind == 'Call']
	succs = []
	for i in range (step):
		for n in ns:
			vc = vc_offs (i + 1)
			if n == sp:
				vc = vc_offs (i)
			n_vc = (n, restrs + tuple ([(sp, vc)]))
			(_, _, succ) = rep.get_func (n_vc)
			pc = rep.get_pc (n_vc)
			succs.append (syntax.mk_implies (pc, succ))
	return succs

def check_split_induct (p, restrs, hyps, split):
	"""perform both the induction check and a function-call based check
	on successes which can avoid some problematic inductions."""
	((l_split, (_, l_step), _), (r_split, (_, r_step), _), _, n, _) = split
	tags = p.pairing.tags

	err_hyp = check.split_r_err_pc_hyp (p, split, restrs)
	hyps = [err_hyp] + hyps + check.split_loop_hyps (tags, split,
		restrs, exit = False)

	rep = mk_graph_slice (p)

	if not check.check_split_induct_step_group (rep, restrs, hyps, split):
		return False

	l_succs = get_n_offset_successes (rep, l_split, l_step, restrs)
	r_succs = get_n_offset_successes (rep, r_split, r_step, restrs)

	if not l_succs:
		return True

	hyp = syntax.foldr1 (syntax.mk_and, l_succs)
	if r_succs:
		hyp = syntax.mk_implies (foldr1 (syntax.mk_and, r_succs), hyp)

	return rep.test_hyp_whyps (hyp, hyps)

def init_loops_to_split (p, restrs):
	to_split = loops_to_split (p, restrs)

	rep = mk_graph_slice (p)
	return [n for n in to_split
		if not [n2 for n2 in to_split if n2 != n
			and rep.get_reachable (n2, n)]]

def restr_others_both (p, restrs, n, m):
	extras = [(sp, vc_double_range (n, m))
		for sp in loops_to_split (p, restrs)]
	return restrs + tuple (extras)

def loop_no_match_unroll (rep, restrs, hyps, split, other_tag, unroll):
	p = rep.p
	assert p.node_tags[split][0] != other_tag
	restr = ((split, vc_num (unroll)), )
	restrs2 = restr_others (p, restr + restrs, 2)
	loop_cond = rep.get_pc ((split, restr + restrs))
	ret_cond = rep.get_pc (('Ret', restrs2), tag = other_tag)
	# loop should be reachable
	if rep.test_hyp_whyps (mk_not (loop_cond), hyps):
		trace ('Loop weak at %d (unroll count %d).' %
			(split, unroll))
		return True
	# reaching the loop should imply reaching a loop on the other side
	hyp = mk_not (mk_and (loop_cond, ret_cond))
	if not rep.test_hyp_whyps (hyp, hyps):
		trace ('Loop independent at %d (unroll count %d).' %
			(split, unroll))
		return True
	return False

def loop_no_match (rep, restrs, hyps, split, other_tag):
	if not loop_no_match_unroll (rep, restrs, hyps, split, other_tag, 4):
		return False
	return loop_no_match_unroll (rep, restrs, hyps, split, other_tag, 8)

last_searcher_results = []

def build_proof_rec (searcher, p, restrs, hyps):
	trace ('doing build proof rec with restrs = %r, hyps = %r' % (restrs, hyps))

	(kind, details) = searcher (p, restrs, hyps)
	last_searcher_results.append ((p, restrs, hyps, kind, details))
	del last_searcher_results[:-10]
	trace ('proof searcher found %s, %s' % (kind, details))
	if kind == 'Restr':
		(restr_kind, restr_points) = details
		return build_proof_rec_with_restrs (restr_points, restr_kind,
			searcher, p, restrs, hyps)
	elif kind == 'Leaf':
		return ProofNode ('Leaf', None, ())
	assert kind in ['CaseSplit', 'Split']
	split = details
	[(_, hyps1, _), (_, hyps2, _)] = check.proof_subproblems (p, kind,
		split, restrs, hyps, '')
	if kind == 'CaseSplit':
		return ProofNode ('CaseSplit', split,
			[build_proof_rec (searcher, p, restrs, hyps1),
				build_proof_rec (searcher, p, restrs, hyps2)])
	split_points = check.split_heads (split)
	no_loop_proof = build_proof_rec_with_restrs (split_points,
		'Number', searcher, p, restrs, hyps1)
	loop_proof = build_proof_rec_with_restrs (split_points,
		'Offset', searcher, p, restrs, hyps2)
	return ProofNode ('Split', split,
		[no_loop_proof, loop_proof])

def build_proof_rec_with_restrs (split_points, kind, searcher, p, restrs, hyps):
	sp = split_points[0]
	use_hyps = list (hyps)
	if p.node_tags[sp][0] != p.pairing.tags[1]:
		nrerr_hyp = check.non_r_err_pc_hyp (p.pairing.tags,
			restr_others (p, restrs, 2))
		use_hyps = use_hyps + [nrerr_hyp]
	limit = find_split_limit (p, sp, restrs, use_hyps, kind)
	# double-check this limit with a rep constructed without the 'fast' flag
	limit = find_split_limit (p, sp, restrs, use_hyps, kind,
		hints = [limit], use_rep = mk_graph_slice (p),
		bound = limit + 3)
	if kind == 'Number':
		vc_opts = vc_upto (limit + 1)
	else:
		vc_opts = vc_offset_upto (limit + 1)
	restrs = restrs + ((sp, vc_opts), )
	if len (split_points) == 1:
		subproof = build_proof_rec (searcher, p, restrs, hyps)
	else:
		subproof = build_proof_rec_with_restrs (split_points[1:],
			kind, searcher, p, restrs, hyps)

	return ProofNode ('Restr', (sp, (kind, (0, limit + 1))), [subproof])

def default_searcher (p, restrs, hyps):
	# detect any un-split loops
	to_split_init = init_loops_to_split (p, restrs)
	rep = mk_graph_slice (p, fast = True)

	l_tag, r_tag = p.pairing.tags
	l_to_split = [n for n in to_split_init if p.node_tags[n][0] == l_tag]
	r_to_split = [n for n in to_split_init if p.node_tags[n][0] == r_tag]
	l_ep = p.get_entry (l_tag)
	r_ep = p.get_entry (r_tag)

	for r_sp in r_to_split:
		trace ('checking loop_no_match at %d' % r_sp, push = 1)
		if loop_no_match (rep, restrs, hyps, r_sp, l_tag):
			trace ('loop does not match!', push = -1)
			return ('Restr', ('Number', [r_sp]))
		trace (' .. done checking loop no match', push = -1)

	if l_to_split and not r_to_split:
		n = l_to_split[0]
		trace ('lhs loop alone, limit must be found.')
		return ('Restr', ('Number', [n]))

	if l_to_split:
		n = l_to_split[0]
		trace ('checking lhs loop_no_match at %d' % n, push = 1)
		if loop_no_match (rep, restrs, hyps, n, r_tag):
			trace ('loop does not match!', push = -1)
			return ('Restr', ('Number', [n]))
		trace (' .. done checking loop no match', push = -1)

		(kind, split) = find_split_loop (p, n, restrs, hyps)
		return (kind, split)

	if r_to_split:
		n = r_to_split[0]
		trace ('rhs loop alone, limit must be found.')
		return ('Restr', ('Number', [n]))

	return ('Leaf', None)

def use_split_searcher (p, split):
	xs = set ([p.loop_id (h) for h in check.split_heads (split)])
	def searcher (p, restrs, hyps):
		ys = set ([p.loop_id (h)
			for h in init_loops_to_split (p, restrs)])
		if xs <= ys:
			return ('Split', split)
		else:
			return default_searcher (p, restrs, hyps)		
	return searcher

