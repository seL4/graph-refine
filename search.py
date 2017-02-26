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
import rep_graph
from syntax import (mk_and, mk_cast, mk_implies, mk_not, mk_uminus, mk_var,
	foldr1, boolT, word32T, word8T, builtinTs, true_term, false_term,
	mk_word32, mk_word8, mk_times, Expr, Type, mk_or, mk_eq, mk_memacc,
	mk_num, mk_minus, mk_plus)
import syntax
import logic

from target_objects import trace, printout
import target_objects
import itertools

last_knowledge = [1]

class NoSplit(Exception):
	pass

def get_loop_var_analysis_at (p, n):
	k = ('search_loop_var_analysis', n)
	if k in p.cached_analysis:
		return p.cached_analysis[k]
	for hook in target_objects.hooks ('loop_var_analysis'):
		res = hook (p, n)
		if res != None:
			p.cached_analysis[k] = res
			return res
	var_deps = p.compute_var_dependencies ()
	res = p.get_loop_var_analysis (var_deps, n)
	p.cached_analysis[k] = res
	return res

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

last_find_split_limit = [0]

def find_split_limit (p, n, restrs, hyps, kind, bound = 51, must_find = True,
		hints = [], use_rep = None):
	tag = p.node_tags[n][0]
	trace ('Finding split limit: %d (%s)' % (n, tag))
	last_find_split_limit[0] = (p, n, restrs, hyps, kind)
	if use_rep == None:
		rep = mk_graph_slice (p, fast = True)
	else:
		rep = use_rep
	check_order = hints + split_sample_set (bound) + [bound]
	# bounds strictly outside this range won't be considered
	bound_range = [0, bound]
	best_bound_found = [None]
	def check (i):
		if i < bound_range[0]:
			return True
		if i > bound_range[1]:
			return False
		restrs2 = restrs + ((n, VisitCount (kind, i)), )
		pc = rep.get_pc ((n, restrs2))
		restrs3 = restr_others (p, restrs2, 2)
		epc = rep.get_pc (('Err', restrs3), tag = tag)
		hyp = mk_implies (mk_not (epc), mk_not (pc))
		res = rep.test_hyp_whyps (hyp, hyps)
		if res:
			trace ('split limit found: %d' % i)
			bound_range[1] = i - 1
			best_bound_found[0] = i
		else:
			bound_range[0] = i + 1
		return res

	map (check, check_order)
	while bound_range[0] <= bound_range[1]:
		split = (bound_range[0] + bound_range[1]) / 2
		check (split)

	bound = best_bound_found[0]
	if bound == None:
		trace ('No split limit found for %d (%s).' % (n, tag))
		if must_find:
			assert not 'split limit found'
	return bound

def get_split_limit (p, n, restrs, hyps, kind, bound = 51,
		must_find = True, est_bound = 1, hints = None):
	k = ('SplitLimit', n, restrs, tuple (hyps), kind)
	if k in p.cached_analysis:
		(lim, prev_bound) = p.cached_analysis[k]
		if lim != None or bound <= prev_bound:
			return lim
	if hints == None:
		hints = [est_bound, est_bound + 1, est_bound + 2]
	res = find_split_limit (p, n, restrs, hyps, kind,
		hints = hints, must_find = must_find, bound = bound)
	p.cached_analysis[k] = (res, bound)
	return res

def init_case_splits (p, hyps, tags = None):
	if 'init_case_splits' in p.cached_analysis:
		return p.cached_analysis['init_case_splits']
	if tags == None:
		tags = p.pairing.tags
	poss = logic.possible_graph_divs (p)
	if len (set ([p.node_tags[n][0] for n in poss])) < 2:
		return None
	rep = rep_graph.mk_graph_slice (p)
	assert all ([p.nodes[n].kind == 'Cond' for n in poss])
	pc_map = logic.dict_list ([(rep.get_pc ((c, ())), c)
		for n in poss for c in p.nodes[n].get_conts ()
		if c not in p.loop_data])
	no_loop_restrs = tuple ([(n, vc_num (0)) for n in p.loop_heads ()])
	err_pc_hyps = [rep_graph.pc_false_hyp ((('Err', no_loop_restrs), tag))
		for tag in p.pairing.tags]
	knowledge = EqSearchKnowledge (rep, hyps + err_pc_hyps, list (pc_map))
	last_knowledge[0] = knowledge
	pc_ids = knowledge.classify_vs ()
	id_n_map = logic.dict_list ([(i, n) for (pc, i) in pc_ids.iteritems ()
		for n in pc_map[pc]])
	tag_div_ns = [[[n for n in ns if p.node_tags[n][0] == t] for t in tags]
		for (i, ns) in id_n_map.iteritems ()]
	split_pairs = [(l_ns[0], r_ns[0]) for (l_ns, r_ns) in tag_div_ns
		if l_ns and r_ns]
	p.cached_analysis['init_case_splits'] = split_pairs
	return split_pairs

case_split_tr = []

def init_proof_case_split (p, restrs, hyps):
	ps = init_case_splits (p, hyps)
	if ps == None:
		return None
	p.cached_analysis.setdefault ('finished_init_case_splits', [])
	fin = p.cached_analysis['finished_init_case_splits']
	known_s = set.union (set (restrs), set (hyps))
	for rs in fin:
		if rs <= known_s:
			return None
	rep = rep_graph.mk_graph_slice (p)
	no_loop_restrs = tuple ([(n, vc_num (0)) for n in p.loop_heads ()])
	err_pc_hyps = [rep_graph.pc_false_hyp ((('Err', no_loop_restrs), tag))
		for tag in p.pairing.tags]
	for (n1, n2) in ps:
		pc = rep.get_pc ((n1, ()))
		if rep.test_hyp_whyps (pc, hyps + err_pc_hyps):
			continue
		if rep.test_hyp_whyps (mk_not (pc), hyps + err_pc_hyps):
			continue
		case_split_tr.append ((n1, restrs, hyps))
		return ('CaseSplit', ((n1, p.node_tags[n1][0]), [n1, n2]))
	fin.append (known_s)
	return None

# TODO: deal with all the code duplication between these two searches
class EqSearchKnowledge:
	def __init__ (self, rep, hyps, vs):
		self.rep = rep
		self.hyps = hyps
		self.v_ids = dict ([(v, 1) for v in vs])
		self.model_trace = []
		self.facts = set ()
		self.premise = foldr1 (mk_and, map (rep.interpret_hyp, hyps))

	def add_model (self, m):
		self.model_trace.append (m)
		update_v_ids_for_model2 (self, self.v_ids, m)

	def hyps_add_model (self, hyps):
		if hyps:
			test_expr = foldr1 (mk_and, hyps)
		else:
			# we want to learn something, either a new model, or
			# that all hyps are true. if there are no hyps,
			# learning they're all true is learning nothing.
			# instead force a model
			test_expr = false_term
		test_expr = mk_implies (self.premise, test_expr)
		m = {}
		(r, _) = self.rep.solv.parallel_check_hyps ([(1, test_expr)],
			{}, model = m)
		if r == 'unsat':
			if not hyps:
				trace ('WARNING: EqSearchKnowledge: premise unsat.')
				trace ("  ... learning procedure isn't going to work.")
			for hyp in hyps:
				self.facts.add (hyp)
		else:
			assert r == 'sat', r
			self.add_model (m)

	def classify_vs (self):
		while not self.facts:
			hyps = v_id_eq_hyps (self.v_ids)
			if not hyps:
				break
			self.hyps_add_model (hyps)
		return self.v_ids

def update_v_ids_for_model2 (knowledge, v_ids, m):
	# first update the live variables
	ev = lambda v: eval_model_expr (m, knowledge.rep.solv, v)
	groups = logic.dict_list ([((k, ev (v)), v)
		for (v, k) in v_ids.iteritems ()])
	v_ids.clear ()
	for (i, kt) in enumerate (sorted (groups)):
		for v in groups[kt]:
			v_ids[v] = i

def v_id_eq_hyps (v_ids):
	groups = logic.dict_list ([(k, v) for (v, k) in v_ids.iteritems ()])
	hyps = []
	for vs in groups.itervalues ():
		for v in vs[1:]:
			hyps.append (mk_eq (v, vs[0]))
	return hyps

class SearchKnowledge:
	def __init__ (self, rep, name, restrs, hyps, tags, cand_elts = None):
		self.rep = rep
		self.name = name
		self.restrs = restrs
		self.hyps = hyps
		self.tags = tags
		if cand_elts != None:
			(loop_elts, r_elts) = cand_elts
		else:
			(loop_elts, r_elts) = ([], [])
		(pairs, vs) = init_knowledge_pairs (rep, loop_elts, r_elts)
		self.pairs = pairs
		self.v_ids = vs
		self.model_trace = []
		self.facts = set ()
		self.weak_splits = set ()
		self.premise = syntax.true_term

	def add_model (self, m):
		self.model_trace.append (m)
		update_v_ids_for_model (self, self.pairs, self.v_ids, m)

	def hyps_add_model (self, hyps, assert_progress = True):
		if hyps:
			test_expr = foldr1 (mk_and, hyps)
		else:
			# we want to learn something, either a new model, or
			# that all hyps are true. if there are no hyps,
			# learning they're all true is learning nothing.
			# instead force a model
			test_expr = false_term
		test_expr = mk_implies (self.premise, test_expr)
		m = {}
		(r, _) = self.rep.solv.parallel_check_hyps ([(1, test_expr)],
			{}, model = m)
		if r == 'unsat':
			if not hyps:
				trace ('WARNING: SearchKnowledge: premise unsat.')
				trace ("  ... learning procedure isn't going to work.")
				return
			if assert_progress:
				assert not (set (hyps) <= self.facts), hyps
			for hyp in hyps:
				self.facts.add (hyp)
		else:
			assert r == 'sat', r
			self.add_model (m)
			if assert_progress:
				assert self.model_trace[-2:-1] != [m]

	def eqs_add_model (self, eqs, assert_progress = True):
		preds = [pred for vpair in eqs
			for pred in expand_var_eqs (self, vpair)
			if pred not in self.facts]

		self.hyps_add_model (preds,
			assert_progress = assert_progress)

	def add_weak_split (self, eqs):
		preds = [pred for vpair in eqs
                        for pred in expand_var_eqs (self, vpair)]
		self.weak_splits.add (tuple (sorted (preds)))

	def is_weak_split (self, eqs):
		preds = [pred for vpair in eqs
                        for pred in expand_var_eqs (self, vpair)]
		return tuple (sorted (preds)) in self.weak_splits

def init_knowledge_pairs (rep, loop_elts, cand_r_loop_elts):
	trace ('Doing search knowledge setup now.')
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
	trace ('... done.')
	return (pairs, vs)

def update_v_ids_for_model (knowledge, pairs, vs, m):
	rep = knowledge.rep
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
	zero = syntax.mk_word32 (0)
	for (pair, data) in pairs.items ():
		if data[0] == 'Failed':
			continue
		(lvs, rvs) = data
		lv_ks = set ([vs[v][0] for v in lvs
			if v[0] == zero or not vs[v][1]])
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

def get_entry_visits_up_to (rep, head, restrs, hyps):
	"""get the set of nodes visited on the entry path entry
	to the loop, up to and including the head point."""
	k = ('loop_visits_up_to', head, restrs, tuple (hyps))
	if k in rep.p.cached_analysis:
		return rep.p.cached_analysis[k]

	[entry] = get_loop_entry_sites (rep, restrs, hyps, head)
	frontier = set ([entry])
	up_to = set ()
	loop = rep.p.loop_body (head)
	while frontier:
		n = frontier.pop ()
		if n == head:
			continue
		new_conts = [n2 for n2 in rep.p.nodes[n].get_conts ()
			if n2 in loop if n2 not in up_to]
		up_to.update (new_conts)
		frontier.update (new_conts)
	rep.p.cached_analysis[k] = up_to
	return up_to

def get_nth_visit_restrs (rep, restrs, hyps, i, visit_num):
	"""get the nth (visit_num-th) visit to node i, using its loop head
	as a restriction point. tricky because there may be a loop entry point
	that brings us in with the loop head before i, or vice-versa."""
	head = rep.p.loop_id (i)
	if i in get_entry_visits_up_to (rep, head, restrs, hyps):
		# node i is in the set visited on the entry path, so
		# the head is visited no more often than it
		offs = 0
	else:
		# these are visited after the head point on the entry path,
		# so the head point is visited 1 more time than it.
		offs = 1
	return ((head, vc_num (visit_num + offs)), ) + restrs

def get_var_pc_var_list (knowledge, v_i):
	rep = knowledge.rep
	(v_i, i, i_offs, i_step) = v_i
	def get_var (k):
		restrs2 = get_nth_visit_restrs (rep, knowledge.restrs,
				knowledge.hyps, i, k)
		(pc, env) = rep.get_node_pc_env ((i, restrs2))
		return (to_smt_expr (pc, env, rep.solv),
			to_smt_expr (v_i, env, rep.solv))
	return [get_var (i_offs + (k * i_step))
		for k in [0, 1, 2]]

def expand_var_eqs (knowledge, (v_i, v_j)):
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

	if op[0] == '_' and op[1] in ['zero_extend', 'sign_extend']:
		[_, ex_kind, n_extend] = op
		n_extend = int (n_extend)
		[x] = xs
		assert x.typ.kind == 'Word' and x.kind == 'Num'
		val = x.val
		if ex_kind == 'sign_extend':
			val = get_signed_val (x)
		result = mk_num (val, x.typ.num + n_extend)
	elif op[0] == '_' and op[1] == 'extract':
		[_, _, n_top, n_bot] = op
		n_top = int (n_top)
		n_bot = int (n_bot)
		[x] = xs
		assert x.typ.kind == 'Word' and x.kind == 'Num'
		length = (n_top - n_bot) + 1
		result = mk_num ((x.val >> n_bot) & ((1 << length) - 1), length)
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
	preds = expand_var_eqs (knowledge, vpair)
	for pred in preds:
		x = eval_model_expr (m, knowledge.rep.solv, pred)
		assert x in [syntax.true_term, syntax.false_term]
		if x == syntax.false_term:
			return False
	return True

def get_model_trace (knowledge, m, v):
	rep = knowledge.rep
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

def mk_pairing_v_eqs (knowledge, pair, endorsed = True):
	v_eqs = []
	(lvs, rvs) = knowledge.pairs[pair]
	zero = mk_word32 (0)
	for v_i in lvs:
		(k, const) = knowledge.v_ids[v_i]
		if const and v_i[0] != zero:
			if not endorsed or eq_known (knowledge, (v_i, 'Const')):
				v_eqs.append ((v_i, 'Const'))
				continue
		vs_j = [v_j for v_j in rvs if knowledge.v_ids[v_j][0] == k]
		if endorsed:
			vs_j = [v_j for v_j in vs_j
				if eq_known (knowledge, (v_i, v_j))]
		if not vs_j:
			return None
		v_j = vs_j[0]
		v_eqs.append ((v_i, v_j))
	return v_eqs

def eq_known (knowledge, vpair):
	preds = expand_var_eqs (knowledge, vpair)
	return set (preds) <= knowledge.facts

def find_split_loop (p, head, restrs, hyps, unfold_limit = 9,
		node_restrs = None, trace_ind_fails = None):
	assert p.loop_data[head][0] == 'Head'
	assert p.node_tags[head][0] == p.pairing.tags[0]

	# the idea is to loop through testable hyps, starting with ones that
	# need smaller models (the most unfolded models will time out for
	# large problems like finaliseSlot)

	rep = mk_graph_slice (p, fast = True)

	nec = get_necessary_split_opts (p, head, restrs, hyps)
	if nec and nec[0] in ['CaseSplit', 'LoopUnroll']:
		return nec
	elif nec:
		i_j_opts = nec
	else:
		i_j_opts = default_i_j_opts (unfold_limit)

	if trace_ind_fails == None:
		ind_fails = []
	else:
		ind_fails = trace_ind_fails
	for (i_opts, j_opts) in i_j_opts:
		result = find_split (rep, head, restrs, hyps,
			i_opts, j_opts, node_restrs = node_restrs)
		if result[0] != None:
			return result
		ind_fails.extend (result[1])

	if ind_fails:
		trace ('Warning: inductive failures: %s' % ind_fails)
	raise NoSplit ()

def default_i_j_opts (unfold_limit = 9):
	return mk_i_j_opts (unfold_limit = unfold_limit)

def mk_i_j_opts (i_seq_opts = None, j_seq_opts = None, unfold_limit = 9):
	if i_seq_opts == None:
		i_seq_opts = [(0, 1), (1, 1), (2, 1), (3, 1)]
	if j_seq_opts == None:
		j_seq_opts = [(0, 1), (0, 2), (1, 1), (1, 2),
			(2, 1), (2, 2), (3, 1)]
	all_opts = set (i_seq_opts + j_seq_opts)

	def filt (opts, lim):
		return [(start, step) for (start, step) in opts
			if start + (2 * step) + 1 <= lim]

	lims = [(filt (i_seq_opts, lim), filt (j_seq_opts, lim))
		for lim in range (unfold_limit)
		if [1 for (start, step) in all_opts
			if start + (2 * step) + 1 == lim]]
	lims = [(i_opts, j_opts) for (i_opts, j_opts) in lims
		if i_opts and j_opts]
	return lims

necessary_split_opts_trace = []

def get_interesting_linear_series_exprs (p, head):
	k = ('interesting_linear_series', head)
	if k in p.cached_analysis:
		return p.cached_analysis[k]
	res = logic.interesting_linear_series_exprs (p, head,
		get_loop_var_analysis_at (p, head))
	p.cached_analysis[k] = res
	return res

def split_opt_test (p, tags = None):
	if not tags:
		tags = p.pairing.tags
	heads = [head for head in init_loops_to_split (p, ())
		if p.node_tags[head][0] == tags[0]]
	hyps = check.init_point_hyps (p)
	return [(head, get_necessary_split_opts (p, head, (), hyps))
		for head in heads]

def interesting_linear_test (p):
	p.do_analysis ()
	for head in p.loop_heads ():
		inter = get_interesting_linear_series_exprs (p, head)
		hooks = target_objects.hooks ('loop_var_analysis')
		n_exprs = [(n, expr, offs) for (n, vs) in inter.iteritems ()
			if not [hook for hook in hooks if hook (p, n) != None]
			for (kind, expr, offs) in vs]
		if n_exprs:
			rep = rep_graph.mk_graph_slice (p)
		for (n, expr, offs) in n_exprs:
			restrs = tuple ([(n2, vc) for (n2, vc)
				in restr_others_both (p, (), 2, 2)
				if p.loop_id (n2) != p.loop_id (head)])
			vis1 = (n, ((head, vc_offs (1)), ) + restrs)
			vis2 = (n, ((head, vc_offs (2)), ) + restrs)
			pc = rep.get_pc (vis2)
			imp = mk_implies (pc, mk_eq (rep.to_smt_expr (expr, vis2),
				rep.to_smt_expr (mk_plus (expr, offs), vis1)))
			assert rep.test_hyp_whyps (imp, [])
	return True

last_necessary_split_opts = [0]

def get_necessary_split_opts (p, head, restrs, hyps, tags = None):
	if not tags:
		tags = p.pairing.tags
	[l_tag, r_tag] = tags
	last_necessary_split_opts[0] = (p, head, restrs, hyps, tags)

	rep = rep_graph.mk_graph_slice (p, fast = True)
	entries = get_loop_entry_sites (rep, restrs, hyps, head)
	if len (entries) > 1:
		return ('CaseSplit', ((entries[0], tags[0]), [entries[0]]))
	for n in init_loops_to_split (p, restrs):
		if p.node_tags[n][0] != r_tag:
			continue
		entries = get_loop_entry_sites (rep, restrs, hyps, n)
		if len (entries) > 1:
			return ('CaseSplit', ((entries[0], r_tag),
				[entries[0]]))

	stuff = linear_setup_stuff (rep, head, restrs, hyps, tags)
	if stuff == None:
		return None
	seq_eqs = get_matching_linear_seqs (rep, head, restrs, hyps, tags)

	vis = stuff['vis']
	for v in seq_eqs:
		if v[0] == 'LoopUnroll':
			(_, n, est_bound) = v
			lim = get_split_limit (p, n, restrs, hyps, 'Number',
				est_bound = est_bound, must_find = False)
			if lim != None:
				return ('LoopUnroll', n)
			continue
		((n, expr), (n2, expr2), (l_start, l_step), (r_start, r_step),
			_, _) = v
		eqs = [rep_graph.eq_hyp ((expr,
			(vis (n, l_start + (i * l_step)), l_tag)),
			(expr2, (vis (n2, r_start + (i * r_step)), r_tag)))
			for i in range (2)]
		eq = foldr1 (mk_and, map (rep.interpret_hyp, eqs))
		m = {}
		if rep.test_hyp_whyps (eq, stuff['hyps'], model = m):
			trace ('found necessary split info: (%s, %s), (%s, %s)'
				% (l_start, l_step, r_start, r_step))
			return mk_i_j_opts ([(l_start + i, l_step)
					for i in range (r_step + 1)],
				[(r_start + i, r_step)
					for i in range (l_step + 1)],
				unfold_limit = 100)
		n_vcs = entry_path_no_loops (rep, l_tag, m, head)
		path_hyps = [rep_graph.pc_true_hyp ((n_vc, l_tag)) for n_vc in n_vcs]
		if rep.test_hyp_whyps (eq, stuff['hyps'] + path_hyps):
			# immediate case split on difference between entry paths
			checks = [(stuff['hyps'], eq_hyp, 'eq')
				for eq_hyp in eqs]
			return derive_case_split (rep, n_vcs, checks)
		necessary_split_opts_trace.append ((n, expr, (l_start, l_step),
			(r_start, r_step), 'Seq check failed'))
	return None

def linear_setup_stuff (rep, head, restrs, hyps, tags):
	[l_tag, r_tag] = tags
	k = ('linear_seq setup', head, restrs, tuple (hyps), tuple (tags))
	p = rep.p
	if k in p.cached_analysis:
		return p.cached_analysis[k]

	assert p.node_tags[head][0] == l_tag
	l_seq_vs = get_interesting_linear_series_exprs (p, head)
	if not l_seq_vs:
		return None
	r_seq_vs = {}
	restr_env = {p.loop_id (head): restrs}
	for n in init_loops_to_split (p, restrs):
		if p.node_tags[n][0] != r_tag:
			continue
		vs = get_interesting_linear_series_exprs (p, n)
		r_seq_vs.update (vs)
	if not r_seq_vs:
		return None

	def vis (n, i):
		restrs2 = get_nth_visit_restrs (rep, restrs, hyps, n, i)
		return (n, restrs2)
	smt = lambda expr, n, i: rep.to_smt_expr (expr, vis (n, i))
	smt_pc = lambda n, i: rep.get_pc (vis (n, i))

	# remove duplicates by concretising
	l_seq_vs = dict ([(smt (expr, n, 2), (kind, n, expr, offs, oset))
		for n in l_seq_vs
		for (kind, expr, offs, oset) in l_seq_vs[n]]).values ()
	r_seq_vs = dict ([(smt (expr, n, 2), (kind, n, expr, offs, oset))
                for n in r_seq_vs
		for (kind, expr, offs, oset) in r_seq_vs[n]]).values ()

	hyps = hyps + [rep_graph.pc_triv_hyp ((vis (n, 3), r_tag))
		for n in set ([n for (_, n, _, _, _) in r_seq_vs])]
	hyps = hyps + [rep_graph.pc_triv_hyp ((vis (n, 3), l_tag))
		for n in set ([n for (_, n, _, _, _) in l_seq_vs])]
	hyps = hyps + [check.non_r_err_pc_hyp (tags,
			restr_others (p, restrs, 2))]

	r = {'l_seq_vs': l_seq_vs, 'r_seq_vs': r_seq_vs,
		'hyps': hyps, 'vis': vis, 'smt': smt, 'smt_pc': smt_pc}
	p.cached_analysis[k] = r
	return r

def get_matching_linear_seqs (rep, head, restrs, hyps, tags):
	k = ('matching linear seqs', head, restrs, tuple (hyps), tuple (tags))
	p = rep.p
	if k in p.cached_analysis:
		v = p.cached_analysis[k]
		(x, y) = itertools.tee (v[0])
		v[0] = x
		return y

	[l_tag, r_tag] = tags
	stuff = linear_setup_stuff (rep, head, restrs, hyps, tags)
	if stuff == None:
		return []

	hyps = stuff['hyps']
	vis = stuff['vis']

	def get_model (n, offs):
		m = {}
		offs_smt = stuff['smt'] (offs, n, 1)
		eq = mk_eq (mk_times (offs_smt, mk_num (4, offs_smt.typ)),
			mk_num (0, offs_smt.typ))
		ex_hyps = [rep_graph.pc_true_hyp ((vis (n, 1), l_tag)),
			rep_graph.pc_true_hyp ((vis (n, 2), l_tag))]
		res = rep.test_hyp_whyps (eq, hyps + ex_hyps, model = m)
		if not m:
			necessary_split_opts_trace.append ((n, kind, 'NoModel'))
			return None
		return m

	r = (seq_eq
		for (kind, n, expr, offs, oset) in sorted (stuff['l_seq_vs'])
		if [v for v in stuff['r_seq_vs'] if v[0] == kind]
		for m in [get_model (n, offs)]
		if m
		for seq_eq in [get_linear_seq_eq (rep, m, stuff,
					(kind, n, expr, offs, oset)),
			get_model_r_side_unroll (rep, tags, m,
				restrs, hyps, stuff)]
		if seq_eq != None)
	(x, y) = itertools.tee (r)
	p.cached_analysis[k] = [y]
	return x

def get_linear_seq_eq (rep, m, stuff, expr_t1):
	def get_int_min (expr):
		v = eval_model_expr (m, rep.solv, expr)
		assert v.kind == 'Num', v
		vs = [v.val + (i << v.typ.num) for i in range (-2, 3)]
		(_, v) = min ([(abs (v), v) for v in vs])
		return v
	(kind, n1, expr1, offs1, oset1) = expr_t1
	smt = stuff['smt']
	expr_init = smt (expr1, n1, 0)
	expr_v = get_int_min (expr_init)
	offs_v = get_int_min (smt (offs1, n1, 1))
	r_seqs = [(n, expr, offs, oset2,
			get_int_min (mk_minus (expr_init, smt (expr, n, 0))),
			get_int_min (smt (offs, n, 0)))
		for (kind2, n, expr, offs, oset2) in sorted (stuff['r_seq_vs'])
		if kind2 == kind]

	for (n, expr, offs2, oset2, diff, offs_v2) in sorted (r_seqs):
		mult = offs_v / offs_v2
		if offs_v % offs_v2 != 0 or mult > 8:
			necessary_split_opts_trace.append ((n, expr,
				'StepWrong', offs_v, offs_v2))
		if diff % offs_v2 != 0 or diff < 0 or (diff / offs_v2) > 8:
			necessary_split_opts_trace.append ((n, expr,
				'StartWrong', diff, offs_v2))
		return ((n1, expr1), (n, expr), (0, 1),
			(diff / offs_v2, mult), (offs1, offs2), (oset1, oset2))
	return None

def get_model_r_side_unroll (rep, tags, m, restrs, hyps, stuff):
	p = rep.p
	[l_tag, r_tag] = tags

	r_kinds = set ([kind for (kind, n, _, _, _) in stuff['r_seq_vs']])
	l_visited_ns_vcs = logic.dict_list ([(n, vc)
		for (tag, n, vc) in rep.node_pc_env_order
		if tag == l_tag
		if eval_pc (rep, m, (n, vc))])
	l_arc_interesting = [(n, vc, kind, expr)
		for (n, vcs) in l_visited_ns_vcs.iteritems ()
		if len (vcs) == 1
		for vc in vcs
		for (kind, expr)
			in logic.interesting_node_exprs (p, n, tags = tags)
		if kind in r_kinds
		if expr.typ.kind == 'Word']
	l_kinds = set ([kind for (n, vc, kind, _) in l_arc_interesting])

	# FIXME: cloned
	def canon_n (n, typ):
		vs = [n + (i << typ.num) for i in range (-2, 3)]
		(_, v) = min ([(abs (v), v) for v in vs])
		return v
	def get_int_min (expr):
		v = eval_model_expr (m, rep.solv, expr)
		assert v.kind == 'Num', v
		return canon_n (v.val, v.typ)
	def eval (expr, n, vc):
		expr = rep.to_smt_expr (expr, (n, vc))
		return get_int_min (expr)

	val_interesting_map = logic.dict_list ([((kind, eval (expr, n, vc)), n)
		for (n, vc, kind, expr) in l_arc_interesting])

	smt = stuff['smt']

	for (kind, n, expr, offs, _) in stuff['r_seq_vs']:
		if kind not in l_kinds:
			continue
		if expr.typ.kind != 'Word':
			continue
		expr_n = get_int_min (smt (expr, n, 0))
		offs_n = get_int_min (smt (offs, n, 0))
		hit = ([i for i in range (64)
			if (kind, canon_n (expr_n + (offs_n * i), expr.typ))
				in val_interesting_map])
		if [i for i in hit if i > 4]:
			return ('LoopUnroll', p.loop_id (n), max (hit))
	return None

last_failed_pairings = []

def setup_split_search (rep, head, restrs, hyps,
		i_opts, j_opts, unfold_limit = None, tags = None,
		node_restrs = None):
	p = rep.p

	if not tags:
		tags = p.pairing.tags
	if node_restrs == None:
		node_restrs = set (p.nodes)
	if unfold_limit == None:
		unfold_limit = max ([start + (2 * step) + 1
			for (start, step) in i_opts + j_opts])

	trace ('Split search at %d, unfold limit %d.' % (head, unfold_limit))

	l_tag, r_tag = tags
	loop_elts = [(n, start, step) for n in p.splittable_points (head)
		if n in node_restrs
		for (start, step) in i_opts]
	init_to_split = init_loops_to_split (p, restrs)
	r_to_split = [n for n in init_to_split if p.node_tags[n][0] == r_tag]
	cand_r_loop_elts = [(n2, start, step) for n in r_to_split
		for n2 in p.splittable_points (n)
		if n2 in node_restrs
		for (start, step) in j_opts]

	err_restrs = restr_others (p, tuple ([(sp, vc_upto (unfold_limit))
		for sp in r_to_split]) + restrs, 1)
	nrerr_pc = mk_not (rep.get_pc (('Err', err_restrs), tag = r_tag))

	def get_pc (n, k):
		restrs2 = get_nth_visit_restrs (rep, restrs, hyps, n, k)
		return rep.get_pc ((n, restrs2))

	for n in r_to_split:
		get_pc (n, unfold_limit)
	get_pc (head, unfold_limit)

	premise = foldr1 (mk_and, [nrerr_pc] + map (rep.interpret_hyp, hyps))
	premise = logic.weaken_assert (premise)

	knowledge = SearchKnowledge (rep,
		'search at %d (unfold limit %d)' % (head, unfold_limit),
		restrs, hyps, tags, (loop_elts, cand_r_loop_elts))
	knowledge.premise = premise
	last_knowledge[0] = knowledge

	# make sure the representation is in sync
	rep.test_hyp_whyps (true_term, hyps)

	# make sure all mem eqs are being tracked
	mem_vs = [v for v in knowledge.v_ids if v[0].typ == builtinTs['Mem']]
	for (i, v) in enumerate (mem_vs):
		for v2 in mem_vs[:i]:
			for pred in expand_var_eqs (knowledge, (v, v2)):
				smt_expr (pred, {}, rep.solv)
	for v in knowledge.v_ids:
		for pred in expand_var_eqs (knowledge, (v, 'Const')):
			smt_expr (pred, {}, rep.solv)

	return knowledge

def get_loop_entry_sites (rep, restrs, hyps, head):
	k = ('loop_entry_sites', restrs, tuple (hyps), rep.p.loop_id (head))
	if k in rep.p.cached_analysis:
		return rep.p.cached_analysis[k]
	ns = set ([n for n2 in rep.p.loop_body (head)
		for n in rep.p.preds[n2]
		if rep.p.loop_id (n) == None])
	def npc (n):
		return rep_graph.pc_false_hyp (((n, tuple ([(n2, restr)
			for (n2, restr) in restrs if n2 != n])),
				rep.p.node_tags[n][0]))
	res = [n for n in ns if not rep.test_hyp_imp (hyps, npc (n))]
	rep.p.cached_analysis[k] = res
	return res

def rebuild_knowledge (head, knowledge):
	i_opts = sorted (set ([(start, step)
		for ((_, start, step), _) in knowledge.pairs]))
	j_opts = sorted (set ([(start, step)
		for (_, (_, start, step)) in knowledge.pairs]))
	knowledge2 = setup_split_search (knowledge.rep, head, knowledge.restrs,
		knowledge.hyps, i_opts, j_opts)
	knowledge2.facts.update (knowledge.facts)
	for m in knowledge.model_trace:
		knowledge2.add_model (m)
	return knowledge2

def split_search (head, knowledge):
	rep = knowledge.rep
	p = rep.p

	# test any relevant cached solutions.
	p.cached_analysis.setdefault (('v_eqs', head), set ())
	v_eq_cache = p.cached_analysis[('v_eqs', head)]
	for (pair, eqs) in v_eq_cache:
		if pair in knowledge.pairs:
			knowledge.eqs_add_model (list (eqs),
				assert_progress = False)

	while True:
		trace ('In %s' % knowledge.name)
		trace ('Computing live pairings')
		pair_eqs = [(pair, mk_pairing_v_eqs (knowledge, pair))
			for pair in sorted (knowledge.pairs)
			if knowledge.pairs[pair][0] != 'Failed']
		if not pair_eqs:
			ind_fails = trace_search_fail (knowledge)
			return (None, ind_fails)

		endorsed = [(pair, eqs) for (pair, eqs) in pair_eqs
			if eqs != None]
		trace (' ... %d live pairings, %d endorsed' %
			(len (pair_eqs), len (endorsed)))
		for (pair, eqs) in endorsed:
			if knowledge.is_weak_split (eqs):
				trace ('  dropping endorsed - probably weak.')
				knowledge.pairs[pair] = ('Failed',
					'ExpectedSplitWeak', eqs)
				continue
			split = build_and_check_split (p, pair, eqs,
				knowledge.restrs, knowledge.hyps,
				knowledge.tags)
			if split == None:
				knowledge.pairs[pair] = ('Failed',
					'SplitWeak', eqs)
				knowledge.add_weak_split (eqs)
				continue
			elif split == 'InductFailed':
				knowledge.pairs[pair] = ('Failed',
					'InductFailed', eqs)
			else:
				v_eq_cache.add ((pair, tuple (eqs)))
				trace ('Found split!')
				return ('Split', split)
		if endorsed:
			continue

		(pair, _) = pair_eqs[0]
		trace ('Testing guess for pair: %s' % str (pair))
		eqs = mk_pairing_v_eqs (knowledge, pair, endorsed = False)
		assert eqs, pair
		knowledge.eqs_add_model (eqs)

def build_and_check_split (p, pair, eqs, restrs, hyps, tags):
	split = v_eqs_to_split (p, pair, eqs, restrs, hyps, tags = tags)
	if split == None:
		return None
	res = check_split_induct (p, restrs, hyps, split, tags = tags)
	if res:
		return split
	# induction has failed at this point, but we might be able to rescue
	# it with some extra linear series eqs
	((l_split, _, l_step), _) = pair
	k = ('extra_linear_seq_eqs', l_split, l_step)
	if k in p.cached_analysis:
		return 'InductFailed'
	if not [v for (v, data) in get_loop_var_analysis_at (p, l_split)
			if data[0] == 'LoopLinearSeries']:
		return 'InductFailed'
	import loop_bounds
	lin_series_eqs = loop_bounds.get_linear_series_eqs (p, l_split,
		restrs, [], omit_standard = True)
	p.cached_analysis[k] = lin_series_eqs
	if not lin_series_eqs:
		return 'InductFailed'
	return build_and_check_split (p, pair, eqs, restrs, hyps, tags)

def trace_search_fail (knowledge):
	trace (('Exhausted split candidates for %s' % knowledge.name))
	fails = [it for it in knowledge.pairs.items ()
		if it[1][0] == 'Failed']
	last_failed_pairings.append (fails)
	del last_failed_pairings[:-10]
	fails10 = fails[:10]
	trace ('  %d of %d failed pairings:' % (len (fails10),
		len (fails)))
	for f in fails10:
		trace ('    %s' % (f,))
	ind_fails = [it for it in fails
		if str (it[1][1]) == 'InductFailed']
	if ind_fails:
		trace (  'Inductive failures!')
	else:
		trace (  'No inductive failures.')
	for f in ind_fails:
		trace ('    %s' % (f,))
	return ind_fails

def find_split (rep, head, restrs, hyps, i_opts, j_opts,
		unfold_limit = None, tags = None,
		node_restrs = None):
	knowledge = setup_split_search (rep, head, restrs, hyps,
		i_opts, j_opts, unfold_limit = unfold_limit,
		tags = tags, node_restrs = node_restrs)

	res = split_search (head, knowledge)

	if res[0]:
		return res

	(models, facts, n_vcs) = most_common_path (head, knowledge)
	if not n_vcs:
		return res

	[tag, _] = knowledge.tags
	knowledge = setup_split_search (rep, head, restrs,
		hyps + [rep_graph.pc_true_hyp ((n_vc, tag)) for n_vc in n_vcs],
		i_opts, j_opts, unfold_limit, tags, node_restrs = node_restrs)
	knowledge.facts.update (facts)
	for m in models:
		knowledge.add_model (m)
	res = split_search (head, knowledge)

	if res[0] == None:
		return res
	(_, split) = res
	checks = check.split_init_step_checks (rep.p, restrs,
                        hyps, split)

	return derive_case_split (rep, n_vcs, checks)

def most_common_path (head, knowledge):
	rep = knowledge.rep
	[tag, _] = knowledge.tags
	data = logic.dict_list ([(tuple (entry_path_no_loops (rep,
			tag, m, head)), m)
		for m in knowledge.model_trace])
	if len (data) < 2:
		return (None, None, None)

	(_, path) = max ([(len (data[path]), path) for path in data])
	models = data[path]
	facts = knowledge.facts
	other_n_vcs = set.intersection (* [set (path2) for path2 in data
		if path2 != path])

	n_vcs = []
	pcs = set ()
	for n_vc in path:
		if n_vc in other_n_vcs:
			continue
		if rep.p.loop_id (n_vc[0]):
			continue
		pc = rep.get_pc (n_vc)
		if pc not in pcs:
			pcs.add (pc)
			n_vcs.append (n_vc)
	assert n_vcs

	return (models, facts, n_vcs)

def eval_pc (rep, m, n_vc, tag = None):
	hit = eval_model_expr (m, rep.solv, rep.get_pc (n_vc, tag = tag))
	assert hit in [syntax.true_term, syntax.false_term], (n_vc, hit)
	return hit == syntax.true_term

def entry_path (rep, tag, m, head):
	n_vcs = []
	for (tag2, n, vc) in rep.node_pc_env_order:
		if n == head:
			break
		if tag2 != tag:
			continue
		if eval_pc (rep, m, (n, vc), tag):
			n_vcs.append ((n, vc))
	return n_vcs

def entry_path_no_loops (rep, tag, m, head = None):
	n_vcs = entry_path (rep, tag, m, head)
	return [(n, vc) for (n, vc) in n_vcs
		if not rep.p.loop_id (n)]

last_derive_case_split = [0]

def derive_case_split (rep, n_vcs, checks):
	last_derive_case_split[0] = (rep.p, n_vcs, checks)
	# remove duplicate pcs
	n_vcs_uniq = dict ([(rep.get_pc (n_vc), (i, n_vc))
		for (i, n_vc) in enumerate (n_vcs)]).values ()
	n_vcs = [n_vc for (i, n_vc) in sorted (n_vcs_uniq)]
	assert n_vcs
	tag = rep.p.node_tags[n_vcs[0][0]][0]
	keep_n_vcs = []
	test_n_vcs = n_vcs
	mk_thyps = lambda n_vcs: [rep_graph.pc_true_hyp ((n_vc, tag))
		for n_vc in n_vcs]
	while len (test_n_vcs) > 1:
		i = len (test_n_vcs) / 2
		test_in = test_n_vcs[:i]
		test_out = test_n_vcs[i:]
		checks2 = [(hyps + mk_thyps (test_in + keep_n_vcs), hyp, nm)
			for (hyps, hyp, nm) in checks]
		(verdict, _) = check.test_hyp_group (rep, checks2)
		if verdict:
			# forget n_vcs that were tested out
			test_n_vcs = test_in
		else:
			# focus on n_vcs that were tested out
			test_n_vcs = test_out
			keep_n_vcs.extend (test_in)
	[(n, vc)] = test_n_vcs
	return ('CaseSplit', ((n, tag), [n]))

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
			eqs.append (form (var,
				mk_cast (minus_loop_step, var.typ)))
		else:
			assert not 'var_deps type understood'

	k = ('extra_linear_seq_eqs', split, step)
	eqs += p.cached_analysis.get (k, [])

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

def v_eqs_to_split (p, pair, v_eqs, restrs, hyps, tags = None):
	trace ('v_eqs_to_split: (%s, %s)' % pair)

	((l_n, l_init, l_step), (r_n, r_init, r_step)) = pair
	l_details = (l_n, (l_init, l_step), mk_seq_eqs (p, l_n, l_step, True)
		+ [v_i[0] for (v_i, v_j) in v_eqs if v_j == 'Const'])
	r_details = (r_n, (r_init, r_step), mk_seq_eqs (p, r_n, r_step, False)
		+ c_memory_loop_invariant (p, r_n, l_n))

	eqs = [(v_i[0], mk_cast (v_j[0], v_i[0].typ))
		for (v_i, v_j) in v_eqs if v_j != 'Const'
		if v_i[0] != syntax.mk_word32 (0)]

	n = 2
	split = (l_details, r_details, eqs, n, (n * r_step) - 1)
	trace ('Split: %s' % (split, ))
	if tags == None:
		tags = p.pairing.tags
	hyps = hyps + check.split_loop_hyps (tags, split, restrs, exit = True)

	r_max = get_split_limit (p, r_n, restrs, hyps, 'Offset',
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

def check_split_induct (p, restrs, hyps, split, tags = None):
	"""perform both the induction check and a function-call based check
	on successes which can avoid some problematic inductions."""
	((l_split, (_, l_step), _), (r_split, (_, r_step), _), _, n, _) = split
	if tags == None:
		tags = p.pairing.tags

	err_hyp = check.split_r_err_pc_hyp (p, split, restrs, tags = tags)
	hyps = [err_hyp] + hyps + check.split_loop_hyps (tags, split,
		restrs, exit = False)

	rep = mk_graph_slice (p)

	if not check.check_split_induct_step_group (rep, restrs, hyps, split,
			tags = tags):
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

	return [n for n in to_split
		if not [n2 for n2 in to_split if n2 != n
			and p.is_reachable_from (n2, n)]]

def restr_others_both (p, restrs, n, m):
	extras = [(sp, vc_double_range (n, m))
		for sp in loops_to_split (p, restrs)]
	return restrs + tuple (extras)

def restr_others_as_necessary (p, n, restrs, init_bound, offs_bound,
		skip_loops = []):
	extras = [(sp, vc_double_range (init_bound, offs_bound))
		for sp in loops_to_split (p, restrs)
		if sp not in skip_loops
		if p.is_reachable_from (sp, n)]
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

def restr_point_name (p, n):
	if p.loop_id (n):
		return '%s (loop head)' % n
	elif p.loop_id (n):
		return '%s (in loop %d)' % (n, p.loop_id (n))
	else:
		return str (n)

def build_proof_rec (searcher, p, restrs, hyps, name = "problem"):
	trace ('doing build proof rec with restrs = %r, hyps = %r' % (restrs, hyps))

	(kind, details) = searcher (p, restrs, hyps)
	last_searcher_results.append ((p, restrs, hyps, kind, details, name))
	del last_searcher_results[:-10]
	if kind == 'Restr':
		(restr_kind, restr_points) = details
		printout ("Discovered that points [%s] can be bounded"
			% ', '.join ([restr_point_name (p, n)
				for n in restr_points]))
		printout ("  (in %s)" % name)
		return build_proof_rec_with_restrs (restr_points, restr_kind,
			searcher, p, restrs, hyps, name = name)
	elif kind == 'Leaf':
		return ProofNode ('Leaf', None, ())
	assert kind in ['CaseSplit', 'Split']
	split = details
	if kind == 'CaseSplit':
		(split, hints) = details
	[(_, hyps1, nm1), (_, hyps2, nm2)] = check.proof_subproblems (p, kind,
		split, restrs, hyps, name)
	if kind == 'CaseSplit':
		printout ("Decided to case split at %s" % str (split))
		printout ("  (in %s)" % name)
		restr_points = hints
		kinds = ['Number', 'Number']
	else:
		restr_points = check.split_heads (split)
		kinds = ['Number', 'Offset']
		printout ("Discovered a loop relation for split points %s"
			% list (restr_points))
		printout ("  (in %s)" % name)
	printout ('Now doing proof search in %s.' % nm1)
	pf1 = build_proof_rec_with_restrs (restr_points, kinds[0], searcher,
		p, restrs, hyps1, must_find = False, name = nm1)
	printout ('Now doing proof search in %s.' % nm2)
	pf2 = build_proof_rec_with_restrs (restr_points, kinds[1], searcher,
		p, restrs, hyps2, must_find = False, name = nm2)
	return ProofNode (kind, split, [pf1, pf2])

def build_proof_rec_with_restrs (split_points, kind, searcher, p, restrs,
		hyps, must_find = True, name = "problem"):
	if not split_points:
		return build_proof_rec (searcher, p, restrs, hyps, name = name)

	sp = split_points[0]
	use_hyps = list (hyps)
	if p.node_tags[sp][0] != p.pairing.tags[1]:
		nrerr_hyp = check.non_r_err_pc_hyp (p.pairing.tags,
			restr_others (p, restrs, 2))
		use_hyps = use_hyps + [nrerr_hyp]

	if p.loop_id (sp):
		lim_pair = get_proof_split_limit (p, sp, restrs, use_hyps,
			kind, must_find = must_find)
	else:
		lim_pair = get_proof_visit_restr (p, sp, restrs, use_hyps,
			kind, must_find = must_find)

	if not lim_pair:
		assert not must_find
		return build_proof_rec_with_restrs (split_points[1:],
			kind, searcher, p, restrs, hyps, must_find = must_find,
			name = name)

	(min_v, max_v) = lim_pair
	if kind == 'Number':
		vc_opts = rep_graph.vc_options (range (min_v, max_v), [])
	else:
		vc_opts = rep_graph.vc_options ([], range (min_v, max_v))

	restrs = restrs + ((sp, vc_opts), )
	subproof = build_proof_rec_with_restrs (split_points[1:],
		kind, searcher, p, restrs, hyps, must_find = must_find,
		name = name)

	return ProofNode ('Restr', (sp, (kind, (min_v, max_v))), [subproof])

def get_proof_split_limit (p, sp, restrs, hyps, kind, must_find = False):
	limit = get_split_limit (p, sp, restrs, hyps, kind,
		must_find = must_find)
	if limit == None:
		return None
	# double-check this limit with a rep constructed without the 'fast' flag
	limit = find_split_limit (p, sp, restrs, hyps, kind,
		hints = [limit, limit + 1], use_rep = mk_graph_slice (p))
	return (0, limit + 1)

def get_proof_visit_restr (p, sp, restrs, hyps, kind, must_find = False):
	rep = rep_graph.mk_graph_slice (p)
	pc = rep.get_pc ((sp, restrs))
	if rep.test_hyp_whyps (pc, hyps):
		return (1, 2)
	elif rep.test_hyp_whyps (mk_not (pc), hyps):
		return (0, 1)
	else:
		assert not must_find
		return None

def default_searcher (p, restrs, hyps):
	# use any handy init splits
	res = init_proof_case_split (p, restrs, hyps)
	if res:
		return res

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
		if kind == 'LoopUnroll':
			return ('Restr', ('Number', [split]))
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

