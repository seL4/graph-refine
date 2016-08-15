# * Copyright 2015, NICTA
# *
# * This software may be distributed and modified according to the terms of
# * the BSD 2-Clause license. Note that NO WARRANTY is provided.
# * See "LICENSE_BSD2.txt" for details.
# *
# * @TAG(NICTA_BSD)

import syntax
from syntax import word32T, word8T, boolT, builtinTs, Expr, Node
from syntax import true_term, false_term
from syntax import foldr1

(mk_var, mk_plus, mk_uminus, mk_minus, mk_times, mk_modulus, mk_bwand, mk_eq,
mk_less_eq, mk_less, mk_implies, mk_and, mk_or, mk_not, mk_word32, mk_word8,
mk_word32_maybe, mk_cast, mk_memacc, mk_memupd, mk_arr_index, mk_arroffs,
mk_if, mk_meta_typ, mk_pvalid) = syntax.mks

from syntax import structs
from target_objects import trace, printout

def is_int (n):
	return hasattr (n, '__int__')

def mk_eq_with_cast (a, c):
	return mk_eq (a, mk_cast (c, a.typ))

def mk_rodata (m):
	assert m.typ == builtinTs['Mem']
	return Expr ('Op', boolT, name = 'ROData', vals = [m])

def cast_pair (((a, a_addr), (c, c_addr))):
	if a.typ != c.typ and c.typ == boolT:
		c = mk_if (c, mk_word32 (1), mk_word32 (0))
	return ((a, a_addr), (mk_cast (c, a.typ), c_addr))

ghost_assertion_type = syntax.Type ('WordArray', 64, 32)

def split_scalar_globals (vs):
	for i in range (len (vs)):
		if vs[i].typ.kind != 'Word' and vs[i].typ != boolT:
			break
	else:
		i = len (vs)
	scalars = vs[:i]
	global_vars = vs[i:]
	for v in global_vars:
		if v.typ not in [builtinTs['Mem'], builtinTs['Dom'],
				builtinTs['HTD'], builtinTs['PMS'],
				ghost_assertion_type]:
			assert not "scalar_global split expected", vs
	memT = builtinTs['Mem']
	mems = [v for v in global_vars if v.typ == memT]
	others = [v for v in global_vars if v.typ != memT]
	return (scalars, mems, others)

def mk_vars (tups):
	return [mk_var (nm, typ) for (nm, typ) in tups]

def split_scalar_pairs (var_pairs):
	return split_scalar_globals (mk_vars (var_pairs))

def azip (xs, ys):
	assert len (xs) == len (ys)
	return zip (xs, ys)

def mk_mem_eqs (a_imem, c_imem, a_omem, c_omem, tags):
	[a_imem] = a_imem
	a_tag, c_tag = tags
	if c_imem:
		[c_imem] = c_imem
		ieqs = [((a_imem, a_tag + '_IN'), (c_imem, c_tag + '_IN'))]
	else:
		ieqs = []
	if c_omem:
		[a_m] = a_omem
		[c_omem] = c_omem
		oeqs = [((a_m, a_tag + '_OUT'), (c_omem, c_tag + '_OUT'))]
	else:
		oeqs = [((a_m, a_tag + '_OUT'), (a_imem, a_tag + '_IN'))
			for a_m in a_omem]

	ieqs += [((mk_rodata (a_imem), a_tag + '_IN'), (true_term, a_tag + '_IN'))]
	oeqs += [((mk_rodata (a_m), a_tag + '_OUT'), (true_term, a_tag + '_OUT'))
		for a_m in a_omem]

	return (ieqs, oeqs)

def mk_fun_eqs (as_f, c_f, prunes = None):
	(var_a_args, a_imem, glob_a_args) = split_scalar_pairs (as_f.inputs)
	(var_c_args, c_imem, glob_c_args) = split_scalar_pairs (c_f.inputs)
	(var_a_rets, a_omem, glob_a_rets) = split_scalar_pairs (as_f.outputs)
	(var_c_rets, c_omem, glob_c_rets) = split_scalar_pairs (c_f.outputs)
	
	(mem_ieqs, mem_oeqs) = mk_mem_eqs (a_imem, c_imem, a_omem, c_omem,
		['ASM', 'C'])

	if not prunes:
		prunes = (var_a_args, var_a_args)
	assert len (prunes[0]) == len (var_c_args), (params, var_a_args,
		var_c_args, prunes)
	a_map = dict (azip (prunes[1], var_a_args))
	ivar_pairs = [((a_map[p], 'ASM_IN'), (c, 'C_IN')) for (p, c)
		in azip (prunes[0], var_c_args) if p in a_map]

	ovar_pairs = [((a_ret, 'ASM_OUT'), (c_ret, 'C_OUT')) for (a_ret, c_ret)
		in azip (var_a_rets, var_c_rets)]
	return (map (cast_pair, mem_ieqs + ivar_pairs),
		map (cast_pair, mem_oeqs + ovar_pairs))

def mk_var_list (vs, typ):
	return [syntax.mk_var (v, typ) for v in vs]

def mk_offs_sequence (init, offs, n, do_reverse = False):
	r = range (n)
	if do_reverse:
		r.reverse ()
	def mk_offs (n):
		return Expr ('Num', init.typ, val = offs * n)
	return [mk_plus (init, mk_offs (m)) for m in r]

def mk_stack_sequence (sp, offs, stack, typ, n, do_reverse = False):
	return [(mk_memacc (stack, addr, typ), addr)
		for addr in mk_offs_sequence (sp, offs, n, do_reverse)]

def mk_aligned (w, n):
	assert w.typ.kind == 'Word'
	mask = Expr ('Num', w.typ, val = ((1 << n) - 1))
	return mk_eq (mk_bwand (w, mask), Expr ('Num', w.typ, val = 0))

def mk_eqs_arm_none_eabi_gnu (var_c_args, var_c_rets, c_imem, c_omem,
		min_stack_size):
	arg_regs = mk_var_list (['r0', 'r1', 'r2', 'r3'], word32T)
	r0 = arg_regs[0]
	sp = mk_var ('r13', word32T)
	st = mk_var ('stack', builtinTs['Mem'])
	r0_input = mk_var ('r0_input', word32T)
	sregs = mk_stack_sequence (sp, 4, st, word32T, len (var_c_args) + 1)
	
	ret = mk_var ('ret', word32T)
	preconds = [mk_aligned (sp, 2), mk_eq (ret, mk_var ('r14', word32T)),
		mk_aligned (ret, 2), mk_eq (r0_input, r0),
		mk_less_eq (min_stack_size, sp)]
	post_eqs = [(x, x) for x in mk_var_list (['r4', 'r5', 'r6', 'r7', 'r8',
			'r9', 'r10', 'r11', 'r13'], word32T)]

	arg_seq = [(r, None) for r in arg_regs] + sregs
	if len (var_c_rets) > 1:
		# the 'return-too-much' issue.
		# instead r0 is a save-returns-here pointer
		arg_seq.pop (0)
		preconds += [mk_aligned (r0, 2), mk_less_eq (sp, r0)]
		save_seq = mk_stack_sequence (r0_input, 4, st, word32T,
			len (var_c_rets))
		save_addrs = [addr for (_, addr) in save_seq]
		post_eqs += [(r0_input, r0_input)]
		out_eqs = zip (var_c_rets, [x for (x, _) in save_seq])
		out_eqs = [(c, mk_cast (a, c.typ)) for (c, a) in out_eqs]
		init_save_seq = mk_stack_sequence (r0, 4, st, word32T,
			len (var_c_rets))
		(_, last_arg_addr) = arg_seq[len (var_c_args) - 1]
		preconds += [mk_less_eq (sp, addr)
			for (_, addr) in init_save_seq[-1:]]
		if last_arg_addr:
			preconds += [mk_less (last_arg_addr, addr)
				for (_, addr) in init_save_seq[:1]]
	else:
		out_eqs = zip (var_c_rets, [r0])
		save_addrs = []
	arg_seq_addrs = [addr for ((_, addr), _) in zip (arg_seq, var_c_args)
		if addr != None]
	swrap = mk_stack_wrapper (sp, st, arg_seq_addrs)
	swrap2 = mk_stack_wrapper (sp, st, save_addrs)
	post_eqs += [(swrap, swrap2)]

	mem = mk_var ('mem', builtinTs['Mem'])
	(mem_ieqs, mem_oeqs) = mk_mem_eqs ([mem], c_imem, [mem], c_omem,
		['ASM', 'C'])

	addr = None
	arg_eqs = [cast_pair (((a_x, 'ASM_IN'), (c_x, 'C_IN')))
		for (c_x, (a_x, addr)) in zip (var_c_args, arg_seq)]
	if addr:
		preconds += [mk_less_eq (sp, addr)]
	ret_eqs = [cast_pair (((a_x, 'ASM_OUT'), (c_x, 'C_OUT')))
		for (c_x, a_x) in out_eqs]
	preconds = [((a_x, 'ASM_IN'), (true_term, 'ASM_IN')) for a_x in preconds]
	asm_invs = [((vin, 'ASM_IN'), (vout, 'ASM_OUT')) for (vin, vout) in post_eqs]

	return (arg_eqs + mem_ieqs + preconds,
		ret_eqs + mem_oeqs + asm_invs)

known_CPUs = {
	'arm-none-eabi-gnu': mk_eqs_arm_none_eabi_gnu
}

def mk_fun_eqs_CPU (cpu_f, c_f, cpu_name, funcall_depth = 1):
	cpu = known_CPUs[cpu_name]
	(var_c_args, c_imem, glob_c_args) = split_scalar_pairs (c_f.inputs)
	(var_c_rets, c_omem, glob_c_rets) = split_scalar_pairs (c_f.outputs)

	return cpu (var_c_args, var_c_rets, c_imem, c_omem,
		(funcall_depth * 256) + 256)

class Pairing:
	def __init__ (self, tags, funs, eqs, notes = None):
		[l_tag, r_tag] = tags
		self.tags = tags
		assert set (funs) == set (tags)
		self.funs = funs
		self.eqs = eqs

		self.l_f = funs[l_tag]
		self.r_f = funs[r_tag]
		self.name = 'Pairing (%s (%s) <= %s (%s))' % (self.l_f,
			l_tag, self.r_f, r_tag)

		self.notes = {}
		if notes != None:
			self.notes.update (notes)

	def __str__ (self):
		return self.name

	def __hash__ (self):
		return hash (self.name)

	def __eq__ (self, other):
		return self.name == other.name and self.eqs == other.eqs

	def __ne__ (self, other):
		return not other or not self == other

def mk_pairing (functions, c_f, as_f, prunes = None, cpu = None):
	fs = (functions[as_f], functions[c_f])
	if cpu:
		eqs = mk_fun_eqs_CPU (fs[0], fs[1], cpu,
			funcall_depth = funcall_depth (functions, c_f)) 
	else:
		eqs = mk_fun_eqs (fs[0], fs[1], prunes = prunes)
	return Pairing (['ASM', 'C'], {'C': c_f, 'ASM': as_f}, eqs)

def inst_eqs_pattern (pattern, params):
	(pat_params, inp_eqs, out_eqs) = pattern
	substs = [((x.name, x.typ), y)
		for (pat_vs, vs) in azip (pat_params, params)
		for (x, y) in azip (pat_vs, vs)]
	substs = dict (substs)
	subst = lambda x: var_subst (x, substs)
	return ([(subst (x), subst (y)) for (x, y) in inp_eqs],
		[(subst (x), subst (y)) for (x, y) in out_eqs])

def inst_eqs_pattern_tuples (pattern, params):
	return inst_eqs_pattern (pattern, map (mk_vars, params))

def inst_eqs_pattern_exprs (pattern, params):
	(inp_eqs, out_eqs) = inst_eqs_pattern (pattern, params)
	return (foldr1 (mk_and, [mk_eq (a, c) for (a, c) in inp_eqs]),
		foldr1 (mk_and, [mk_eq (a, c) for (a, c) in out_eqs]))

def var_match (var_exp, conc_exp, assigns):
	if var_exp.typ != conc_exp.typ:
		return False
	if var_exp.kind == 'Var':
		key = (var_exp.name, var_exp.typ)
		if key in assigns:
			return conc_exp == assigns[key]
		else:
			assigns[key] = conc_exp
			return True
	elif var_exp.kind == 'Op':
		if conc_exp.kind != 'Op' or var_exp.name != conc_exp.name:
			return False
		return all ([var_match (a, b, assigns)
			for (a, b) in azip (var_exp.vals, conc_exp.vals)])
	else:
		return False

def var_subst (var_exp, assigns, must_subst = True):
	def substor (var_exp):
		if var_exp.kind == 'Var':
			k = (var_exp.name, var_exp.typ)
			if must_subst or k in assigns:
				return assigns[k]
			else:
				return None
		else:
			return None
	return syntax.do_subst (var_exp, substor)

def recursive_term_subst (eqs, expr):
	if expr in eqs:
		return eqs[expr]
	if expr.kind == 'Op':
		vals = [recursive_term_subst (eqs, x) for x in expr.vals]
		return Expr ('Op', expr.typ, name = expr.name, vals = vals)
	return expr

def mk_accum_rewrites ():
	x = mk_var ('x', word32T)
	y = mk_var ('y', word32T)
	z = mk_var ('z', word32T)
	i = mk_var ('i', word32T)
	def via_word8 (v):
		return mk_cast (mk_cast (v, word8T), word32T)
	return [(x, i, mk_plus (x, y), mk_plus (x, mk_times (i, y)),
			y),
		(x, i, mk_plus (y, x), mk_plus (x, mk_times (i, y)),
			y),
		(x, i, mk_minus (x, y), mk_minus (x, mk_times (i, y)),
			mk_uminus (y)),
		(x, i, via_word8 (mk_plus (x, y)),
			via_word8 (mk_plus (x, mk_times (i, y))),
			y),
		(x, i, via_word8 (mk_plus (y, x)),
			via_word8 (mk_plus (x, mk_times (i, y))),
			y),
		(x, i, via_word8 (mk_plus (via_word8 (mk_plus (x, z)), y)),
			via_word8 (mk_plus (x, mk_times (i, mk_plus (y, z)))),
			mk_plus (y, z)),
		(x, i, via_word8 (mk_plus (y, x)),
			via_word8 (mk_plus (x, mk_times (i, y))),
			y),
		(x, i, mk_plus (mk_plus (x, y), z),
			mk_plus (x, mk_times (i, mk_plus (y, z))),
			mk_plus (y, z)),
		(x, i, mk_plus (mk_plus (y, x), z),
			mk_plus (x, mk_times (i, mk_plus (y, z))),
			mk_plus (y, z)),
		(x, i, mk_plus (y, mk_plus (x, z)),
			mk_plus (x, mk_times (i, mk_plus (y, z))),
			mk_plus (y, z)),
		(x, i, mk_plus (y, mk_plus (z, x)),
			mk_plus (x, mk_times (i, mk_plus (y, z))),
			mk_plus (y, z)),
		(x, i, mk_minus (mk_minus (x, y), z),
			mk_minus (x, mk_times (i, mk_plus (y, z))),
			mk_plus (y, z)),
	]

accum_rewrites = mk_accum_rewrites ()

def default_val (typ):
	if typ.kind == 'Word':
		return Expr ('Num', typ, val = 0)
	elif typ == boolT:
		return false_term
	else:
		assert not 'default value for type %s created', typ

trace_accumulators = []

def accumulator_closed_form (expr, (nm, typ)):
	for (x, i, pattern, rewrite, offset) in accum_rewrites:
		var = mk_var (nm, typ)
		ass = {(x.name, x.typ): var}
		m = var_match (pattern, expr, ass)
		if m:
			x2_def = default_val (typ)
			i2_def = default_val (word32T)
			def do_rewrite (x2 = x2_def, i2 = i2_def):
				ass[(x.name, x.typ)] = x2
				ass[(i.name, i.typ)] = i2
				vs = var_subst (rewrite, ass)
				return vs
			offs = var_subst (offset, ass)
			return (do_rewrite, offs)
	if trace_accumulators:
		trace ('no accumulator %s' % ((expr, nm, typ), ))
	return (None, None)

def end_addr (p, typ):
	if typ[0] == 'Array':
		(_, typ, n) = typ
		sz = mk_times (mk_word32 (typ.size ()), n)
	else:
		assert typ[0] == 'Type', typ
		(_, typ) = typ
		sz = mk_word32 (typ.size ())
	return mk_plus (p, mk_minus (sz, mk_word32 (1)))

def pvalid_assertion1 ((typ, k, p, pv), (typ2, k2, p2, pv2)):
	"""first pointer validity assertion: incompatibility.
	pvalid1 & pvalid2 --> non-overlapping OR somehow-contained.
	typ/typ2 is ('Type', syntax.Type) or ('Array', Type, Expr) for
	dynamically sized arrays.
	"""
	offs1 = mk_minus (p, p2)
	cond1 = get_styp_condition (offs1, typ, typ2)
	offs2 = mk_minus (p2, p)
	cond2 = get_styp_condition (offs2, typ2, typ)
	
	out1 = mk_less (end_addr (p, typ), p2)
	out2 = mk_less (end_addr (p2, typ2), p)
	return mk_implies (mk_and (pv, pv2), foldr1 (mk_or,
		[cond1, cond2, out1, out2]))

def pvalid_assertion2 ((typ, k, p, pv), (typ2, k2, p2, pv2)):
	"""second pointer validity assertion: implication.
	pvalid1 & strictly-contained --> pvalid2
	"""
	if typ[0] == 'Array' and typ2[0] == 'Array':
		# this is such a vague notion it's not worth it
		return true_term
	offs1 = mk_minus (p, p2)
	cond1 = get_styp_condition (offs1, typ, typ2)
	imp1 = mk_implies (mk_and (cond1, pv2), pv)
	offs2 = mk_minus (p2, p)
	cond2 = get_styp_condition (offs2, typ2, typ)
	imp2 = mk_implies (mk_and (cond2, pv), pv2)
	return mk_and (imp1, imp2)

def sym_distinct_assertion ((typ, p, pv), (start, end)):
	out1 = mk_less (mk_plus (p, mk_word32 (typ.size () - 1)), mk_word32 (start))
	out2 = mk_less (mk_word32 (end), p)
	return mk_implies (pv, mk_or (out1, out2))

def norm_array_type (t):
	if t[0] == 'Type' and t[1].kind == 'Array':
		(_, atyp) = t
		return ('Array', atyp.el_typ_symb, mk_word32 (atyp.num), 'Strong')
	elif t[0] == 'Array' and len (t) == 3:
		(_, typ, l) = t
		# these derive from PArrayValid assertions. we know the array is
		# at least this long, but it might be longer.
		return ('Array', typ, l, 'Weak')
	else:
		return t

stored_styp_conditions = {}

def get_styp_condition (offs, inner_typ, outer_typ):
	r = get_styp_condition_inner1 (inner_typ, outer_typ)
	if not r:
		return false_term
	else:
		return r (offs)

def get_styp_condition_inner1 (inner_typ, outer_typ):
	inner_typ = norm_array_type (inner_typ)
	outer_typ = norm_array_type (outer_typ)
	k = (inner_typ, outer_typ)
	if k in stored_styp_conditions:
		return stored_styp_conditions[k]
	r = get_styp_condition_inner2 (inner_typ, outer_typ)
	stored_styp_conditions[k] = r
	return r

def array_typ_size ((kind, el_typ, num, _)):
	el_size = mk_word32 (el_typ.size ())
	return mk_times (num, el_size)

def get_styp_condition_inner2 (inner_typ, outer_typ):
	if inner_typ[0] == 'Array' and outer_typ[0] == 'Array':
		(_, ityp, inum, _) = inner_typ
		(_, otyp, onum, outer_bound) = outer_typ
		# array fits in another array if the starting element is
		# a sub-element, and if the size of the left array plus
		# the offset fits in the right array
		cond = get_styp_condition_inner1 (('Type', ityp), outer_typ)
		isize = array_typ_size (inner_typ)
		osize = array_typ_size (outer_typ)
		if outer_bound == 'Strong' and cond:
			return lambda offs: mk_and (cond (offs),
				mk_less_eq (mk_plus (isize, offs), osize))
		else:
			return cond
	elif inner_typ == outer_typ:
		return lambda offs: mk_eq (offs, mk_word32 (0))
	elif outer_typ[0] == 'Type' and outer_typ[1].kind == 'Struct':
		conds = [(get_styp_condition_inner1 (inner_typ,
				('Type', sf_typ)), mk_word32 (offs2))
			for (_, offs2, sf_typ)
			in structs[outer_typ[1].name].fields.itervalues()]
		conds = [cond for cond in conds if cond[0]]
		if conds:
			return lambda offs: foldr1 (mk_or,
				[c (mk_minus (offs, offs2))
					for (c, offs2) in conds])
		else:
			return None
	elif outer_typ[0] == 'Array':
		(_, el_typ, n, bound) = outer_typ
		cond = get_styp_condition_inner1 (inner_typ, ('Type', el_typ))
		el_size = mk_word32 (el_typ.size ())
		size = mk_times (n, el_size)
		if bound == 'Strong' and cond:
			return lambda offs: mk_and (mk_less (offs, size),
				cond (mk_modulus (offs, el_size)))
		elif cond:
			return lambda offs: cond (mk_modulus (offs, el_size))
		else:
			return None
	else:
		return None

def all_vars_have_prop (expr, prop):
	class Failed (Exception):
		pass
	def visit (expr):
		if expr.kind != 'Var':
			return
		v2 = (expr.name, expr.typ)
		if not prop (v2):
			raise Failed ()
	try:
		expr.visit (visit)
		return True
	except Failed:
		return False

def all_vars_in_set (expr, var_set):
	return all_vars_have_prop (expr, lambda v: v in var_set)

def var_not_in_expr (var, expr):
	v2 = (var.name, var.typ)
	return all_vars_have_prop (expr, lambda v: v != v2)

def mk_align_valid_ineq (typ, p):
	if typ[0] == 'Type':
		(_, typ) = typ
		align = typ.align ()
		size = mk_word32 (typ.size ())
	else:
		assert typ[0] == 'Array', typ
		(kind, typ, num) = typ
		align = typ.align ()
		size = mk_times (mk_word32 (typ.size ()), num)
	assert align in [1, 4, 8]
	w0 = mk_word32 (0)
	if align > 1:
		align_req = [mk_eq (mk_bwand (p, mk_word32 (align - 1)), w0)]
	else:
		align_req = []
	return foldr1 (mk_and, align_req + [mk_not (mk_eq (p, w0)),
		mk_implies (mk_less (w0, size),
			mk_less_eq (p, mk_uminus (size)))])

# generic operations on function/problem graphs
def dict_list (xys, keys = None):
	d = {}
	for (x, y) in xys:
		d.setdefault (x, [])
		d[x].append (y)
	if keys:
		for x in keys:
			d.setdefault (x, [])
	return d

def compute_preds (nodes):
	preds = dict_list ([(c, n) for n in nodes
			for c in nodes[n].get_conts ()],
		keys = nodes)
	for n in ['Ret', 'Err']:
		preds.setdefault (n, [])
	return preds

def simplify_node_elementary(node):
	if node.kind == 'Cond' and node.cond == true_term:
		return Node ('Basic', node.left, [])
	elif node.kind == 'Cond' and node.cond == false_term:
		return Node ('Basic', node.right, [])
	elif node.kind == 'Cond' and node.left == node.right:
		return Node ('Basic', node.left, [])
	else:
		return node

def compute_var_flows (nodes, outputs, preds, override_lvals_rvals = {}):
	# compute a graph of reverse var flows to pass to tarjan's algorithm
	graph = {}
	entries = ['Ret']
	for (n, node) in nodes.iteritems ():
		if node.kind == 'Basic':
			for (lv, rv) in node.upds:
				graph[(n, 'Post', lv)] = [(n, 'Pre', v)
					for v in syntax.get_expr_var_set (rv)]
		elif node.is_noop ():
			pass
		else:
			if n in override_lvals_rvals:
				(lvals, rvals) = override_lvals_rvals[n]
			else:
				rvals = syntax.get_node_rvals (node)
				rvals = set (rvals.iteritems ())
				lvals = set (node.get_lvals ())
			if node.kind != 'Basic':
				lvals = list (lvals) + ['PC']
				entries.append ((n, 'Post', 'PC'))
			for lv in lvals:
				graph[(n, 'Post', lv)] = [(n, 'Pre', rv)
					for rv in rvals]
	graph['Ret'] = [(n, 'Post', v)
		for n in preds['Ret'] for v in outputs (n)]
	vs = set ([v for k in graph for (_, _, v) in graph[k]])
	for v in vs:
		for n in nodes:
			graph.setdefault ((n, 'Post', v), [(n, 'Pre', v)]) 
			graph[(n, 'Pre', v)] = [(n2, 'Post', v)
				for n2 in preds[n]]

	comps = tarjan (graph, entries)
	return (graph, comps)

def mk_not_red (v):
	if v.is_op ('Not'):
		[v] = v.vals
		return v
	else:
		return syntax.mk_not (v)

def cont_with_conds (nodes, n, conds):
	while True:
		if n not in nodes or nodes[n].kind != 'Cond':
			return n
		cond = nodes[n].cond
		if cond in conds:
			n = nodes[n].left
		elif mk_not_red (cond) in conds:
			n = nodes[n].right
		else:
			return n

def contextual_conds (nodes, preds):
	"""computes a collection of conditions that can be assumed true
	at any point in the node graph."""
	pre_conds = {}
	arc_conds = {}
	visit = [n for n in nodes if not (preds[n])]
	while visit:
		n = visit.pop ()
		if n not in nodes:
			continue
		in_arc_conds = [arc_conds.get ((pre, n), set ())
			for pre in preds[n]]
		if not in_arc_conds:
			conds = set ()
		else:
			conds = set.intersection (* in_arc_conds)
		if pre_conds.get (n) == conds:	
			continue
		pre_conds[n] = conds
		if n not in nodes:
			continue
		if nodes[n].kind == 'Cond' and nodes[n].left == nodes[n].right:
			c_conds = [conds, conds]
		elif nodes[n].kind == 'Cond':
			c_conds = [nodes[n].cond, mk_not_red (nodes[n].cond)]
			c_conds = [set.union (set ([c]), conds)
				for c in c_conds]
		else:
			upds = set (nodes[n].get_lvals ())
			c_conds = [set ([c for c in conds if
				not set.intersection (upds, 
					syntax.get_expr_var_set (c))])]
		for (cont, conds) in zip (nodes[n].get_conts (), c_conds):
			arc_conds[(n, cont)] = conds
			visit.append (cont)
	return (arc_conds, pre_conds)

def contextual_cond_simps (nodes, preds):
	"""a common pattern in architectures with conditional operations is
	a sequence of instructions with the same condition.
	we can usually then reduce to a single contional block.
	  b   e    =>    b-e
	 / \ / \   =>   /   \ 
	a-c-d-f-g  =>  a-c-f-g
	this is sometimes important if b calculates a register that e uses
	since variable dependency analysis will see this register escape via
	the impossible path a-c-d-e
	"""
	(arc_conds, pre_conds) = contextual_conds (nodes, preds)
	nodes = dict (nodes)
	for n in nodes:
		if nodes[n].kind == 'Cond':
			continue
		cont = nodes[n].cont
		conds = arc_conds[(n, cont)]
		cont2 = cont_with_conds (nodes, cont, conds)
		if cont2 != cont:
			nodes[n] = syntax.copy_rename (nodes[n],
				({}, {cont: cont2}))
	return nodes

def minimal_loop_node_set (p):
	"""discover a minimal set of loop addresses, excluding some operations
	using conditional instructions which are syntactically within the
	loop but semantically must always be followed by an immediate loop
	exit.

	amounts to rerunning loop detection after contextual_cond_simps."""

	loop_ns = set (p.loop_data)
	really_in_loop = {}
	nodes = contextual_cond_simps (p.nodes, p.preds)
	def is_really_in_loop (n):
		if n in really_in_loop:
			return really_in_loop[n]
		ns = []
		r = None
		while r == None:
			ns.append (n)
			if n not in loop_ns:
				r = False
			elif p.loop_splittables[n]:
				r = True
			else:
				conts = [n2 for n2 in nodes[n].get_conts ()
					if n2 != 'Err']
				if len (conts) > 1:
					r = True
				else:
					[n] = conts
		for n in ns:
			really_in_loop[n] = r
		return r
	return set ([n for n in loop_ns if is_really_in_loop (n)])

def compute_var_deps (nodes, outputs, preds, override_lvals_rvals = {}):
	# outs = list of (outname, retvars)
	var_deps = {}
	visit = set ()
	visit.update (preds['Ret'])
	visit.update (preds['Err'])

	nodes = contextual_cond_simps (nodes, preds)

	while visit:
		n = visit.pop ()

		node = simplify_node_elementary (nodes[n])
		if n in override_lvals_rvals:
			(lvals, rvals) = override_lvals_rvals[n]
			lvals = set (lvals)
			rvals = set (rvals)
		elif node.is_noop ():
			lvals = set ([])
			rvals = set ([])
		else:
			rvals = syntax.get_node_rvals (node)
			rvals = set (rvals.iteritems ())
			lvals = set (node.get_lvals ())
		cont_vs = set ()

		for c in node.get_conts ():
			if c == 'Ret':
				cont_vs.update (outputs (n))
			elif c == 'Err':
				pass
			else:
				cont_vs.update (var_deps.get (c, []))
		vs = set.union(rvals, cont_vs - lvals)

		if n in var_deps and vs <= var_deps[n]:
			continue
		var_deps[n] = vs
		visit.update (preds[n])

	return var_deps

def compute_loop_var_analysis (nodes, var_deps, n, loop, preds):
	upd_vs = set ([v for n2 in loop
		if not nodes[n2].is_noop ()
		for v in nodes[n2].get_lvals ()])
	const_vs = set ([v for n2 in loop
		for v in var_deps[n2] if v not in upd_vs])

	vca = compute_var_cycle_analysis (nodes, n, loop, preds,
		const_vs, set (var_deps[n]))
	vca = [(syntax.mk_var (nm, typ), data)
		for ((nm, typ), data) in vca.items ()]
	return vca

cvca_trace = []
cvca_diag = [False]
no_accum_expressions = set ()

def compute_var_cycle_analysis (nodes, n, loop, preds, const_vars, vs,
		diag = None):

	if diag == None:
		diag = cvca_diag[0]

	cache = {}
	del cvca_trace[:]

	def warm_cache_before (n2, v):
		cvca_trace.append ((n2, v))
		cvca_trace.append ('(')
		arc = []
		for i in range (100000):
			opts = [n3 for n3 in preds[n2] if n3 in loop
				if v not in nodes[n3].get_lvals ()
				if n3 != n
				if (n3, v) not in cache]
			if not opts:
				break
			n2 = opts[0]
			arc.append (n2)
		if not (len (arc) < 100000):
			trace ('warmup overrun in compute_var_cycle_analysis')
			trace ('chasing %s in %s' % (v, set (arc)))
			assert False, (v, arc[-500:])
		for n2 in reversed (arc):
			var_eval_before (n2, v)
		cvca_trace.append (')')

	def var_eval_before (n2, v, do_cmp = True):
		if (n2, v) in cache and do_cmp:
			return cache[(n2, v)]
		if n2 == n and do_cmp:
			var_exp = mk_var (v[0], v[1])
			vs = set ([v for v in [v] if v not in const_vars])
			return (vs, var_exp)
		warm_cache_before (n2, v)
		ps = [n3 for n3 in preds[n2] if n3 in loop]
		vs = [var_eval_after (n3, v) for n3 in ps]
		if not all ([v3 == vs[0] for v3 in vs]):
			if diag:
				trace ('vs disagree @ %d: %s' % (n2, vs))
			r = None
		else:
			r = vs[0]
		if do_cmp:
			cache[(n2, v)] = r
		return r
	def var_eval_after (n2, v):
		node = nodes[n2]
		if node.kind == 'Call' and v in node.rets:
			if diag:
				trace ('fetched %s from call at %d' % (v, n2))
			return None
		elif node.kind == 'Basic':
			for (lv, val) in node.upds:
				if lv == v:
					return expr_eval_before (n2, val)
			return var_eval_before (n2, v)
		else:
			return var_eval_before (n2, v)
	def expr_eval_before (n2, expr):
		if expr.kind == 'Op':
			if expr.vals == []:
				return (set(), expr)
			vals = [expr_eval_before (n2, v)
				for v in expr.vals]
			if None in vals:
				return None
			s = set.union (* [s for (s, v) in vals])
			if len(s) > 1:
				if diag:
					trace ('too many vars for %s @ %d: %s' % (expr, n2, s))
				return None
			return (s, Expr ('Op', expr.typ,
				name = expr.name,
				vals = [v for (s, v) in vals]))
		elif expr.kind == 'Num':
			return (set(), expr)
		elif expr.kind == 'Var':
			return var_eval_before (n2,
				(expr.name, expr.typ))
		else:
			if diag:
				trace ('Unwalkable expr %s' % expr)
			return None

	vca = {}
	for v in vs:
		rv = var_eval_before (n, v, do_cmp = False)
		if rv == None:
			vca[v] = 'LoopVariable'
			continue
		(s, expr) = rv
		if expr == mk_var (v[0], v[1]):
			vca[v] = 'LoopConst'
			continue
		if var_not_in_expr (mk_var (v[0], v[1]), expr):
			# leaf calculations do not have data flow to
			# themselves. the search algorithm doesn't
			# have to worry about these.
			vca[v] = 'LoopLeaf'
			continue
		(form, offs) = accumulator_closed_form (expr, v)
		if form != None and all_vars_in_set (form (), const_vars):
			vca[v] = ('LoopLinearSeries', form, offs)
		else:
			if diag:
				trace ('No accumulator %s => %s'
					% (v, expr))
			no_accum_expressions.add ((v, expr))
			vca[v] = 'LoopVariable'
	return vca

def mk_var_renames (xs, ys):
	renames = {}
	for (x, y) in azip (xs, ys):
		assert x.kind == 'Var' and y.kind == 'Var'
		assert x.name not in renames
		renames[x.name] = y.name
	return renames

def first_aligned_address (nodes, radix):
	ks = [k for k in nodes
		if k % radix == 0]
	if ks:
		return min (ks)
	else:
		return None

def entry_aligned_address (fun, radix):
	n = fun.entry
	while n % radix != 0:
		ns = fun.nodes[n].get_conts ()
		assert len (ns) == 1, (fun.name, n)
		[n] = ns
	return n

def aligned_address_sanity (functions, symbols, radix):
	for (f, func) in functions.iteritems ():
		if f not in symbols:
			# happens for static or invented functions sometimes
			continue
		if func.entry:
			addr = first_aligned_address (func.nodes, radix)
			if addr == None:
				printout ('Warning: %s: no aligned instructions' % f)
				continue
			addr2 = symbols[f][0]
			if addr != addr2:
				printout ('target mismatch on func %s' % f)
				printout ('  (starts at 0x%x not 0x%x)' % (addr, addr2))
				return False
			addr3 = entry_aligned_address (func, radix)
			if addr3 != addr2:
				printout ('entry mismatch on func %s' % f)
				printout ('  (enters at 0x%x not 0x%x)' % (addr3, addr2))
				return False
	return True

# variant of tarjan's strongly connected component algorithm
def tarjan (graph, entries):
	"""tarjan (graph, entries)
	variant of tarjan's strongly connected component algorithm
	e.g. tarjan ({1: [2, 3], 3: [4, 5]}, [1])
	entries should not be reachable"""
	data = {}
	comps = []
	for v in entries:
		assert v not in data
		tarjan1 (graph, v, data, [], set ([]), comps)
	return comps

def tarjan1 (graph, v, data, stack, stack_set, comps):
	vs = []
	while True:
		# skip through nodes with single successors
		data[v] = [len(data), len(data)]
		stack.append(v)
		stack_set.add(v)
		cs = graph[v]
		if len (cs) != 1 or cs[0] in data:
			break
		vs.append ((v, cs[0]))
		[v] = cs

	for c in graph[v]:
		if c not in data:
			tarjan1 (graph, c, data, stack, stack_set, comps)
			data[v][1] = min (data[v][1], data[c][1])
		elif c in stack_set:
			data[v][1] = min (data[v][1], data[c][0])
	
	vs.reverse ()
	for (v2, c) in vs:
		data[v2][1] = min (data[v2][1], data[c][1])

	for (v2, _) in [(v, 0)] + vs:
		if data[v2][1] == data[v2][0]:
			comp = []
			while True:
				x = stack.pop ()
				stack_set.remove (x)
				if x == v2:
					break
				comp.append (x)
			comps.append ((v2, comp))

def get_one_loop_splittable (p, loop_set):
	"""discover a component of a strongly connected
	component which, when removed, disconnects the component.
	complex loops lack such a split point."""
	candidate_splittables = set (loop_set)
	graph = dict ([(x, [y for y in p.nodes[x].get_conts ()
		if y in loop_set]) for x in loop_set])
	while candidate_splittables:
		n = candidate_splittables.pop ()
		graph2 = dict ([(x, [y for y in graph[x] if y != n])
			for x in graph])
		comps = logic.tarjan (graph2, [n])
		if not [comp for comp in comps if comp[1]]:
			return n
		loop2 = find_loop_avoiding (graph, loop_set,
			candidate_splittables)
		candidate_splittables = set.intersection (loop2,
			candidate_splittables)
	return None

def find_loop_avoiding (graph, loop, avoid):
	n = (list (loop - avoid) + list (loop))[0]
	arc = [n]
	visited = set ([n])
	while True:
		cs = set (graph[n])
		acs = cs - avoid
		vcs = set.intersection (cs, visited)
		if vcs:
			n = vcs.pop ()
			break
		elif acs:
			n = acs.pop ()
		else:
			n = cs.pop ()
		visited.add (n)
		arc.append (n)
	[i] = [i for (i, n2) in enumerate (arc) if n2 == n]
	return set (arc[i:])
# non-equality relations in proof hypotheses are recorded as a pretend
# equality and reverted to their 'real' meaning here.
def mk_stack_wrapper (stack_ptr, stack, excepts):
	return syntax.mk_rel_wrapper ('StackWrapper',
		[stack_ptr, stack] + excepts)

def mk_mem_acc_wrapper (addr, v):
	return syntax.mk_rel_wrapper ('MemAccWrapper', [addr, v])

def mk_mem_wrapper (m):
	return syntax.mk_rel_wrapper ('MemWrapper', [m])

def tm_with_word32_list (xs):
	if xs:
		return foldr1 (mk_plus, map (mk_word32, xs))
	else:
		return mk_uminus (mk_word32 (0))

def word32_list_from_tm (t):
	xs = []
	while t.is_op ('Plus'):
		[x, t] = t.vals
		assert x.kind == 'Num' and x.typ == word32T
		xs.append (x.val)
	if t.kind == 'Num':
		xs.append (t.val)
	return xs

def mk_eq_selective_wrapper (v, (xs, ys)):
	# this is a huge hack, but we need to put these lists somewhere
	xs = tm_with_word32_list (xs)
	ys = tm_with_word32_list (ys)
	return syntax.mk_rel_wrapper ('EqSelectiveWrapper', [v, xs, ys])

def apply_rel_wrapper (lhs, rhs):
	assert lhs.typ == syntax.builtinTs['RelWrapper']
	assert rhs.typ == syntax.builtinTs['RelWrapper']
	assert lhs.kind == 'Op'
	assert rhs.kind == 'Op'
	ops = set ([lhs.name, rhs.name])
	if ops == set (['StackWrapper']):
		[sp1, st1] = lhs.vals[:2]
		[sp2, st2] = rhs.vals[:2]
		excepts = list (set (lhs.vals[2:] + rhs.vals[2:]))
		for p in excepts:
			st1 = syntax.mk_memupd (st1, p, syntax.mk_word32 (0))
			st2 = syntax.mk_memupd (st2, p, syntax.mk_word32 (0))
		return syntax.Expr ('Op', boolT, name = 'StackEquals',
			vals = [sp1, st1, sp2, st2])
	elif ops == set (['MemAccWrapper', 'MemWrapper']):
		[acc] = [v for v in [lhs, rhs] if v.is_op ('MemAccWrapper')]
		[addr, val] = acc.vals
		assert addr.typ == syntax.word32T
		[m] = [v for v in [lhs, rhs] if v.is_op ('MemWrapper')]
		[m] = m.vals
		assert m.typ == builtinTs['Mem']
		expr = mk_eq (mk_memacc (m, addr, val.typ), val)
		return expr
	elif ops == set (['EqSelectiveWrapper']):
		[lhs_v, _, _] = lhs.vals
		[rhs_v, _, _] = rhs.vals
		if lhs_v.typ == syntax.builtinTs['RelWrapper']:
			return apply_rel_wrapper (lhs_v, rhs_v)
		else:
			return mk_eq (lhs, rhs)
	else:
		assert not 'rel wrapper opname understood'

def inst_eq_at_visit (exp, vis):
	if not exp.is_op ('EqSelectiveWrapper'):
		return True
	[_, xs, ys] = exp.vals
	# hacks
	xs = word32_list_from_tm (xs)
	ys = word32_list_from_tm (ys)
	if vis.kind == 'Number':
		return vis.n in xs
	elif vis.kind == 'Offset':
		return vis.n in ys
	else:
		assert not 'visit kind useable', vis

def strengthen_hyp (expr, sign = 1):
	if not expr.kind == 'Op':
		return expr
	if expr.name in ['And', 'Or']:
		vals = [strengthen_hyp (v, sign) for v in expr.vals]
		return syntax.Expr ('Op', expr.typ, name = expr.name,
			vals = vals)
	elif expr.name == 'Implies':
		[l, r] = expr.vals
		l = strengthen_hyp (l, - sign)
		r = strengthen_hyp (r, sign)
		return syntax.mk_implies (l, r)
	elif expr.name == 'Not':
		[x] = expr.vals
		x = strengthen_hyp (x, - sign)
		return syntax.mk_not (x)
	elif expr.name == 'StackEquals':
		if sign == 1:
			return syntax.Expr ('Op', boolT,
				name = 'ImpliesStackEquals', vals = expr.vals)
		else:
			return syntax.Expr ('Op', boolT,
				name = 'StackEqualsImplies', vals = expr.vals)
	elif expr.name == 'ROData':
		if sign == 1:
			return syntax.Expr ('Op', boolT,
				name = 'ImpliesROData', vals = expr.vals)
		else:
			return expr
	elif expr.name == 'Equals' and expr.vals[0].typ == boolT:
		vals = expr.vals
		if vals[1] in [syntax.true_term, syntax.false_term]:
			vals = [vals[1], vals[0]]
		if vals[0] == syntax.true_term:
			return strengthen_hyp (vals[1], sign)
		elif vals[0] == syntax.false_term:
			return strengthen_hyp (syntax.mk_not (vals[1]), sign)
		else:
			return expr
	else:
		return expr

def weaken_assert (expr):
	return strengthen_hyp (expr, -1)

