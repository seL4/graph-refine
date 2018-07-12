# * Copyright 2015, NICTA
# *
# * This software may be distributed and modified according to the terms of
# * the BSD 2-Clause license. Note that NO WARRANTY is provided.
# * See "LICENSE_BSD2.txt" for details.
# *
# * @TAG(NICTA_BSD)

# pseudo-compiler for use of aggregate types in C-derived function code

import syntax
from syntax import structs, get_vars, get_expr_typ, get_node_vars, Expr, Node
import logic


(mk_var, mk_plus, mk_uminus, mk_minus, mk_times, mk_modulus, mk_bwand, mk_eq,
mk_less_eq, mk_less, mk_implies, mk_and, mk_or, mk_not, mk_word32, mk_word8,
mk_word32_maybe, mk_cast, mk_memacc, mk_memupd, mk_arr_index, mk_arroffs,
mk_if, mk_meta_typ, mk_pvalid) = syntax.mks

from syntax import word32T, word8T

from syntax import fresh_name, foldr1

from target_objects import symbols, trace

def compile_field_acc (name, expr, replaces):
	'''pseudo-compile access to field (named name) of expr'''
	if expr.kind == 'StructCons':
		return expr.vals[name]
	elif expr.kind == 'FieldUpd':
		if expr.field[0] == name:
			return expr.val
		else:
			return compile_field_acc (name, expr.struct, replaces)
	elif expr.kind == 'Var':
		assert expr.name in replaces
		[(v_nm, typ)] = [(v_nm, typ) for (f_nm, v_nm, typ)
			in replaces[expr.name] if f_nm == name]
		return mk_var (v_nm, typ)
	elif expr.is_op ('MemAcc'):
		assert expr.typ.kind == 'Struct'
		(typ, offs, _) = structs[expr.typ.name].fields[name]
		[m, p] = expr.vals
		return mk_memacc (m, mk_plus (p, mk_word32 (offs)), typ)
	elif expr.kind == 'Field':
		expr2 = compile_field_acc (expr.field[0], expr.struct, replaces)
		return compile_field_acc (name, expr2, replaces)
	elif expr.is_op ('ArrayIndex'):
		[arr, i] = expr.vals
		expr2 = compile_array_acc (i, arr, replaces, False)
		assert expr2, (arr, i)
		return compile_field_acc (name, expr2, replaces)
	else:
		print expr
		assert not 'field acc compilable'

def compile_array_acc (i, expr, replaces, must = True):
	'''pseudo-compile access to array element i of expr'''
	if not logic.is_int (i) and i.kind == 'Num':
		assert i.typ == word32T
		i = i.val
	if expr.kind == 'Array':
		if logic.is_int (i):
			return expr.vals[i]
		else:
			expr2 = expr.vals[-1]
			for (j, v) in enumerate (expr.vals[:-1]):
				expr2 = mk_if (mk_eq (i, mk_word32 (j)), v, expr2)
			return expr2
	elif expr.is_op ('ArrayUpdate'):
		[arr, j, v] = expr.vals
		if j.kind == 'Num' and logic.is_int (i):
			if i == j.val:
				return v
			else:
				return compile_array_acc (i, arr, replaces)
		else:
			return mk_if (mk_eq (j, mk_word32_maybe (i)), v,
				compile_array_acc (i, arr, replaces))
	elif expr.is_op ('MemAcc'):
		[m, p] = expr.vals
		return mk_memacc (m, mk_arroffs (p, expr.typ, i), expr.typ.el_typ)
	elif expr.is_op ('IfThenElse'):
		[cond, left, right] = expr.vals
		return mk_if (cond, compile_array_acc (i, left, replaces),
			compile_array_acc (i, right, replaces))
	elif expr.kind == 'Var':
		assert expr.name in replaces
		if logic.is_int (i):
			(_, v_nm, typ) = replaces[expr.name][i]
			return mk_var (v_nm, typ)
		else:
			vs = [(mk_word32 (j), mk_var (v_nm, typ))
				for (j, v_nm, typ)
				in replaces[expr.name]]
			expr2 = vs[0][1]
			for (j, v) in vs[1:]:
				expr2 = mk_if (mk_eq (i, j), v, expr2)
			return expr2
	else:
		if not must:
			return None
		return mk_arr_index (expr, mk_word32_maybe (i))

def num_fields (container, typ):
	if container == typ:
		return 1
	elif container.kind == 'Array':
		return container.num * num_fields (container.el_typ, typ)
	elif container.kind == 'Struct':
		struct = structs[container.name]
		return sum ([num_fields (typ2, typ)
			for (nm, typ2) in struct.field_list])
	else:
		return 0

def get_const_global_acc_offset (expr, offs, typ):
	if expr.kind == 'ConstGlobal':
		return (expr, offs)
	elif expr.is_op ('ArrayIndex'):
		[expr2, offs2] = expr.vals
		offs = mk_plus (offs, mk_times (offs2,
			mk_word32 (num_fields (expr.typ, typ))))
		return get_const_global_acc_offset (expr2, offs, typ)
	elif expr.kind == 'Field':
		struct = structs[expr.struct.typ.name]
		offs2 = 0
		for (nm, typ2) in struct.field_list:
			if (nm, typ2) == expr.field:
				offs = mk_plus (offs, mk_word32 (offs2))
				return get_const_global_acc_offset (
					expr.struct, offs, typ)
			else:
				offs2 += num_fields (typ2, typ)
	else:
		return None

def compile_const_global_acc (expr):
	if expr.kind == 'ConstGlobal' or (expr.is_op ('ArrayIndex')
			and expr.vals[0].kind == 'ConstGlobal'):
		return None
	if expr.typ.kind != 'Word':
		return None
	r = get_const_global_acc_offset (expr, mk_word32 (0), expr.typ)
	if r == None:
		return None
	(cg, offs) = r
	return mk_arr_index (cg, offs)

def compile_val_fields (expr, replaces):
	if expr.typ.kind == 'Array':
		res = []
		for i in range (expr.typ.num):
			acc = compile_array_acc (i, expr, replaces)
			res.extend (compile_val_fields (acc, replaces))
		return res
	elif expr.typ.kind == 'Struct':
		res = []
		for (nm, typ2) in structs[expr.typ.name].field_list:
			acc = compile_field_acc (nm, expr, replaces)
			res.extend (compile_val_fields (acc, replaces))
		return res
	else:
		return [compile_accs (replaces, expr)]

def compile_val_fields_of_typ (expr, replaces, typ):
	return [e for e in compile_val_fields (expr, replaces)
		if e.typ == typ]

# it helps in this compilation to know that the outermost expression we are
# trying to fetch is always of basic type, never struct or array.

# sort of fudged in the array indexing case here
def compile_accs (replaces, expr):
	r = compile_const_global_acc (expr)
	if r:
		return compile_accs (replaces, r)

	if expr.kind == 'Field':
		expr = compile_field_acc (expr.field[0], expr.struct, replaces)
		return compile_accs (replaces, expr)
	elif expr.is_op ('ArrayIndex'):
		[arr, n] = expr.vals
		expr2 = compile_array_acc (n, arr, replaces, False)
		if expr2:
			return compile_accs (replaces, expr2)
		arr = compile_accs (replaces, arr)
		n = compile_accs (replaces, n)
		expr2 = compile_array_acc (n, arr, replaces, False)
		if expr2:
			return compile_accs (replaces, expr2)
		else:
			return mk_arr_index (arr, n)
	elif (expr.is_op ('MemUpdate')
			and expr.vals[2].is_op ('MemAcc')
			and expr.vals[2].vals[0] == expr.vals[0]
			and expr.vals[2].vals[1] == expr.vals[1]):
		# null memory copy. probably created by ops below
		return compile_accs (replaces, expr.vals[0])
	elif (expr.is_op ('MemUpdate')
			and expr.vals[2].kind == 'FieldUpd'):
		[m, p, f_upd] = expr.vals
		assert f_upd.typ.kind == 'Struct'
		(typ, offs, _) = structs[f_upd.typ.name].fields[f_upd.field[0]]
		assert f_upd.val.typ == typ
		return compile_accs (replaces,
			mk_memupd (mk_memupd (m, p, f_upd.struct),
				mk_plus (p, mk_word32 (offs)), f_upd.val))
	elif (expr.is_op ('MemUpdate')
			and expr.vals[2].typ.kind == 'Struct'):
		[m, p, s_val] = expr.vals
		struct = structs[s_val.typ.name]
		for (nm, (typ, offs, _)) in struct.fields.iteritems ():
			f = compile_field_acc (nm, s_val, replaces)
			assert f.typ == typ
			m = mk_memupd (m, mk_plus (p, mk_word32 (offs)), f)
		return compile_accs (replaces, m)
	elif (expr.is_op ('MemUpdate')
			and expr.vals[2].is_op ('ArrayUpdate')):
		[m, p, arr_upd] = expr.vals
		[arr, i, v] = arr_upd.vals
		return compile_accs (replaces,
			mk_memupd (mk_memupd (m, p, arr),
				mk_arroffs (p, arr.typ, i), v))
	elif (expr.is_op ('MemUpdate')
				and expr.vals[2].typ.kind == 'Array'):
		[m, p, arr] = expr.vals
		n = arr.typ.num
		typ = arr.typ.el_typ
		for i in range (n):
			offs = i * typ.size ()
			assert offs == i or offs % 4 == 0
			e = compile_array_acc (i, arr, replaces)
			m = mk_memupd (m, mk_plus (p, mk_word32 (offs)), e)
		return compile_accs (replaces, m)
	elif expr.is_op ('Equals') \
			and expr.vals[0].typ.kind in ['Struct', 'Array']:
		[x, y] = expr.vals
		assert x.typ == y.typ
		xs = compile_val_fields (x, replaces)
		ys = compile_val_fields (y, replaces)
		eq = foldr1 (mk_and, map (mk_eq, xs, ys))
		return compile_accs (replaces, eq)
	elif expr.is_op ('PAlignValid'):
		[typ, p] = expr.vals
		p = compile_accs (replaces, p)
		assert typ.kind == 'Type'
		return logic.mk_align_valid_ineq (('Type', typ.val), p)
	elif expr.kind == 'Op':
		vals = [compile_accs (replaces, v) for v in expr.vals]
		return syntax.adjust_op_vals (expr, vals)
	elif expr.kind == 'Symbol':
		return mk_word32 (symbols[expr.name][0])
	else:
		if expr.kind not in {'Var':True, 'ConstGlobal':True,
				'Num':True, 'Invent':True, 'Type':True}:
			print expr
			assert not 'field acc compiled'
		return expr

def expand_arg_fields (replaces, args):
	xs = []
	for arg in args:
		if arg.typ.kind == 'Struct':
			ys = [compile_field_acc (nm, arg, replaces)
				for (nm, _) in structs[arg.typ.name].field_list]
			xs.extend (expand_arg_fields (replaces, ys))
		elif arg.typ.kind == 'Array':
			ys = [compile_array_acc (i, arg, replaces)
				for i in range (arg.typ.num)]
			xs.extend (expand_arg_fields (replaces, ys))
		else:
			xs.append (compile_accs (replaces, arg))
	return xs

def expand_lval_list (replaces, lvals):
	xs = []
	for (nm, typ) in lvals:
		if nm in replaces:
			xs.extend (expand_lval_list (replaces, [(v_nm, typ)
				for (f_nm, v_nm, typ) in replaces[nm]]))
		else:
			assert typ.kind not in ['Struct', 'Array']
			xs.append ((nm, typ))
	return xs

def mk_acc (idx, expr, replaces):
	if logic.is_int (idx):
		assert expr.typ.kind == 'Array'
		return compile_array_acc (idx, expr, replaces)
	else:
		assert expr.typ.kind == 'Struct'
		return compile_field_acc (idx, expr, replaces)

def compile_upds (replaces, upds):
	lvs = expand_lval_list (replaces, [lv for (lv, v) in upds])
	vs = expand_arg_fields (replaces, [v for (lv, v) in upds])

	assert [typ for (nm, typ) in lvs] == map (get_expr_typ, vs), (lvs, vs)

	return [(lv, v) for (lv, v) in zip (lvs, vs)
		if not v.is_var (lv)]

def compile_struct_use (function):
	trace ('Compiling in %s.' % function.name)
	vs = get_vars (function)
	max_node = max (function.nodes.keys () + [2])

	visit_vs = vs.keys ()
	replaces = {}
	while visit_vs:
		v = visit_vs.pop ()
		typ = vs[v]
		if typ.kind == 'Struct':
			fields = structs[typ.name].field_list
		elif typ.kind == 'Array':
			fields = [(i, typ.el_typ) for i in range (typ.num)]
		else:
			continue
		new_vs = [(nm, fresh_name ('%s.%s' % (v, nm), vs, f_typ), f_typ)
			for (nm, f_typ) in fields]
		replaces[v] = new_vs
		visit_vs.extend ([v_nm for (_, v_nm, _) in new_vs])

	for n in function.nodes:
		node = function.nodes[n]
		if node.kind == 'Basic':
			node.upds = compile_upds (replaces, node.upds)
		elif node.kind == 'Basic':
			assert not node.lval[1].kind in ['Struct', 'Array']
			node.val = compile_accs (replaces, node.val)
		elif node.kind == 'Call':
			node.args = expand_arg_fields (replaces, node.args)
			node.rets = expand_lval_list (replaces, node.rets)
		elif node.kind == 'Cond':
			node.cond = compile_accs (replaces, node.cond)
		else:
			assert not 'node kind understood'

	function.inputs = expand_lval_list (replaces, function.inputs)
	function.outputs = expand_lval_list (replaces, function.outputs)
	return len (replaces) == 0

def check_compile (func):
	for node in func.nodes.itervalues ():
		vs = {}
		get_node_vars (node, vs)
		for (v_nm, typ) in vs.iteritems ():
			if typ.kind == 'Struct':
				print 'Failed to compile struct %s in %s' % (v_nm, func)
				print node
				assert not 'compiled'
			if typ.kind == 'Array':
				print 'Failed to compile array %s in %s' % (v_nm, func)
				print node
				assert not 'compiled'

def subst_expr (expr):
	if expr.kind == 'Symbol':
		return mk_word32 (symbols[expr.name][0])
	elif expr.is_op ('PAlignValid'):
		[typ, p] = expr.vals
		assert typ.kind == 'Type'
		return logic.mk_align_valid_ineq (('Type', typ.val), p)
	elif expr.kind in ['Op', 'Var', 'Num', 'Type']:
		return None
	else:
		assert not 'expression simple-substitutable', expr

def substitute_simple (func):
	from syntax import Node
	for (n, node) in func.nodes.items ():
		func.nodes[n] = node.subst_exprs (subst_expr,
			ss = set (['Symbol', 'PAlignValid']))

def missing_symbols (functions):
	symbols_needed = set()
	def visitor (expr):
		if expr.kind == 'Symbol':
			symbols_needed.add(expr.name)
	for func in functions.itervalues ():
		for node in func.nodes.itervalues ():
			node.visit (lambda l: (), visitor)
	trouble = symbols_needed - set (symbols)
	if trouble:
		print ('Symbols missing for substitution: %r' % trouble)
	return trouble

def compile_funcs (functions):
	assert not missing_symbols (functions)
	for (f, func) in functions.iteritems ():
		substitute_simple (func)
		check_compile (func)

def combine_duplicate_nodes (nodes):
	orig_size = len (nodes)
	node_renames = {}
	progress = True
	while progress:
		progress = False
		node_names = {}
		for (n, node) in nodes.items ():
			if node in node_names:
				node_renames[n] = node_names[node]
				del nodes[n]
				progress = True
			else:
				node_names[node] = n

		if not progress:
			break

		for (n, node) in nodes.items ():
			nodes[n] = rename_node_conts (node, node_renames)

	if len (nodes) < orig_size:
		print 'Trimmed duplicates %d -> %d' % (orig_size, len (nodes))
	return node_renames

def rename_node_conts (node, renames):
	new_conts = [renames.get (c, c) for c in node.get_conts ()]
	return Node (node.kind, new_conts, node.get_args ())

def recommended_rename (s):
	bits = s.split ('.')
	if len (bits) != 2:
		return s
	if all ([x in '0123456789' for x in bits[1]]):
		return bits[0]
	else:
		return s

def rename_vars (function):
	preds = logic.compute_preds (function.nodes)
	var_deps = logic.compute_var_deps (function.nodes,
		lambda x: function.outputs, preds)

	vs = set ()
	dont_rename_vs = set ()
	for n in var_deps:
		rev_renames = {}
		for (v, t) in var_deps[n]:
			v2 = recommended_rename (v)
			rev_renames.setdefault (v2, [])
			rev_renames[v2].append ((v, t))
			vs.add ((v, t))
		for (v2, vlist) in rev_renames.iteritems ():
			if len (vlist) > 1:
				dont_rename_vs.update (vlist)

	renames = dict ([(v, recommended_rename (v)) for (v, t) in vs
		if (v, t) not in dont_rename_vs])

	f = function
	f.inputs = [(renames.get (v, v), t) for (v, t) in f.inputs]
	f.outputs = [(renames.get (v, v), t) for (v, t) in f.outputs]
	for n in f.nodes:
		f.nodes[n] = syntax.copy_rename (f.nodes[n], (renames, {}))

def rename_and_combine_function_duplicates (functions):
	for (f, fun) in functions.iteritems ():
		rename_vars (fun)
		renames = combine_duplicate_nodes (fun.nodes)
		fun.entry = renames.get (fun.entry, fun.entry)


