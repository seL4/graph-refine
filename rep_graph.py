# * Copyright 2015, NICTA
# *
# * This software may be distributed and modified according to the terms of
# * the BSD 2-Clause license. Note that NO WARRANTY is provided.
# * See "LICENSE_BSD2.txt" for details.
# *
# * @TAG(NICTA_BSD)

from solver import Solver, merge_envs_pcs, smt_expr, mk_smt_expr, to_smt_expr
from syntax import (true_term, false_term, boolT, mk_and, mk_not, mk_implies,
	builtinTs, word32T, word8T, foldr1, mk_eq, mk_plus, mk_word32, mk_var)
import syntax
import logic
import solver
from logic import azip

from target_objects import functions, pairings, sections, trace, printout
import target_objects

class VisitCount:
	"""Used to represent a target number of visits to a split point.
	Options include a number (0, 1, 2), a symbolic offset (i + 1, i + 2),
	or a list of options."""
	def __init__ (self, kind, value):
		self.kind = kind
		self.is_visit_count = True
		if kind == 'Number':
			self.n = value
		elif kind == 'Offset':
			self.n = value
		elif kind == 'Options':
			self.opts = tuple (value)
			for opt in self.opts:
				assert opt.kind in ['Number', 'Offset']
		else:
			assert not 'VisitCount type understood'

	def __hash__ (self):
		if self.kind == 'Options':
			return hash (self.opts)
		else:
			return hash (self.kind) + self.n

	def __eq__ (self, other):
		if not other:
			return False
		if self.kind == 'Options':
			return (other.kind == 'Options'
				and self.opts == other.opts)
		else:
			return self.kind == other.kind and self.n == other.n

	def __neq__ (self, other):
		if not other:
			return True
		return not (self == other)

	def __str__ (self):
		if self.kind == 'Number':
			return str (self.n)
		elif self.kind == 'Offset':
			return 'i+%s' % self.n
		elif self.kind == 'Options':
			return '_'.join (map (str, self.opts))

	def __repr__ (self):
		(ns, os) = self.get_opts ()
		return 'vc_options (%r, %r)' % (ns, os)

	def get_opts (self):
		if self.kind == 'Options':
			opts = self.opts
		else:
			opts = [self]
		ns = [vc.n for vc in opts if vc.kind == 'Number']
		os = [vc.n for vc in opts if vc.kind == 'Offset']
		return (ns, os)

	def serialise (self, ss):
		ss.append ('VC')
		(ns, os) = self.get_opts ()
		ss.append ('%d' % len (ns))
		ss.extend (['%d' % n for n in ns])
		ss.append ('%d' % len (os))
		ss.extend (['%d' % n for n in os])

	def incr (self, incr):
		if self.kind in ['Number', 'Offset']:
			n = self.n + incr
			if n < 0:
				return None
			return VisitCount (self.kind, n)
		elif self.kind == 'Options':
			opts = [vc.incr (incr) for vc in self.opts]
			opts = [opt for opt in opts if opt]
			if opts == []:
				return None
			return mk_vc_opts (opts)
		else:
			assert not 'VisitCount type understood'

	def has_zero (self):
		if self.kind == 'Options':
			return bool ([vc for vc in self.opts
				if vc.has_zero ()])
		else:
			return self.kind == 'Number' and self.n == 0

def mk_vc_opts (opts):
	if len (opts) == 1:
		return opts[0]
	else:
		return VisitCount ('Options', opts)

def vc_options (nums, offsets):
	return mk_vc_opts (map (vc_num, nums) + map (vc_offs, offsets))

def vc_num (n):
	return VisitCount ('Number', n)

def vc_upto (n):
	return mk_vc_opts (map (vc_num, range (n)))

def vc_offs (n):
	return VisitCount ('Offset', n)

def vc_offset_upto (n):
	return mk_vc_opts (map (vc_offs, range (n)))

def vc_double_range (n, m):
	return mk_vc_opts (map (vc_num, range (n)) + map (vc_offs, range (m)))

class InlineEvent(Exception):
	pass

class Hyp:
	"""Used to represent a proposition about path conditions or data at
	various points in execution."""
	
	def __init__ (self, kind, arg1, arg2, induct = None):
		self.kind = kind
		if kind == 'PCImp':
			self.pcs = [arg1, arg2]
		elif kind == 'Eq':
			self.vals = [arg1, arg2]
			self.induct = induct
		else:
			assert not 'hyp kind understood'

	def __repr__ (self):
		if self.kind == 'PCImp':
			vals = map (repr, self.pcs)
		elif self.kind == 'Eq':
			vals = map (repr, self.vals)
			if self.induct:
				vals += [repr (self.induct)]
		else:
			assert not 'hyp kind understood'
		return 'Hyp (%r, %s)' % (self.kind, ', '.join (vals))

	def hyp_tuple (self):
		if self.kind == 'PCImp':
			return ('PCImp', self.pcs[0], self.pcs[1])
		elif self.kind == 'Eq':
			return ('Eq', self.vals[0], self.vals[1], self.induct)
		else:
			assert not 'hyp kind understood'

	def __hash__ (self):
		return hash (self.hyp_tuple ())

	def __ne__ (self, other):
		return not other or not (self == other)

	def __cmp__ (self, other):
		return cmp (self.hyp_tuple (), other.hyp_tuple ())

	def visits (self):
		if self.kind == 'PCImp':
			return [vis for vis in self.pcs
				if vis[0] != 'Bool']
		elif self.kind == 'Eq':
			return [vis for (_, vis) in self.vals]
		else:
			assert not 'hyp kind understood'

	def serialise_visit (self, (n, restrs), ss):
		ss.append ('%s' % n)
		ss.append ('%d' % len (restrs))
		for (n2, vc) in restrs:
			ss.append ('%d' % n2)
			vc.serialise (ss)

	def serialise_pc (self, pc, ss):
		if pc[0] == 'Bool' and pc[1] == true_term:
			ss.append ('True')
		elif pc[0] == 'Bool' and pc[1] == false_term:
			ss.append ('False')
		else:
			ss.append ('PC')
			serialise_visit (pc[0], ss)
			ss.append (pc[1])

	def serialise_hyp (self, ss):
		if self.kind == 'PCImp':	
			(visit1, visit2) = self.pcs
			ss.append ('PCImp')
			self.serialise_pc (visit1, ss)
			self.serialise_pc (visit2, ss)
		elif self.kind == 'Eq':
			assert len (self.vals) == 2
			ss.extend ('Eq')
			for (exp, visit) in self.vals:
				exp.serialise (ss)
				self.serialise_visit (visit, ss)
			if induct:
				ss.append ('%d' % induct[0])
				ss.append ('%d' % induct[1])
			else:
				ss.extend (['None', 'None'])
		else:
			assert not 'hyp kind understood'

	def interpret (self, rep):
		if self.kind == 'PCImp':
			((visit1, tag1), (visit2, tag2)) = self.pcs
			if visit1 == 'Bool':
				pc1 = tag1
			else:
				pc1 = rep.get_pc (visit1, tag = tag1)
			if visit2 == 'Bool':
				pc2 = tag2
			else:
				pc2 = rep.get_pc (visit2, tag = tag2)
			return mk_implies (pc1, pc2)
		elif self.kind == 'Eq':
			[(x, xvis), (y, yvis)] = self.vals
			if self.induct:
				v = rep.get_induct_var (self.induct)
				x = subst_induct (x, v)
				y = subst_induct (y, v)
			x_pc_env = rep.get_node_pc_env (xvis[0], tag = xvis[1])
			y_pc_env = rep.get_node_pc_env (yvis[0], tag = yvis[1])
			if x_pc_env == None or y_pc_env == None:
				return syntax.false_term
			((_, xenv), (_, yenv)) = (x_pc_env, y_pc_env)
			return inst_eq_with_envs ((x, xenv), (y, yenv), rep.solv)
		else:
			assert not 'hypothesis type understood'

def check_vis_is_vis (((n, vc), tag)):
	assert vc[:0] == (), vc

def eq_hyp (lhs, rhs, induct = None):
	check_vis_is_vis (lhs[1])
	check_vis_is_vis (rhs[1])
	return Hyp ('Eq', lhs, rhs, induct = induct)

def pc_true_hyp (vis):
	check_vis_is_vis (vis)
	return Hyp ('PCImp', ('Bool', true_term), vis)

def pc_false_hyp (vis):
	check_vis_is_vis (vis)
	return Hyp ('PCImp', vis, ('Bool', false_term))

def pc_triv_hyp (vis):
	check_vis_is_vis (vis)
	return Hyp ('PCImp', vis, vis)

class GraphSlice:
	"""Used to represent a slice of potential execution in a graph where
	looping is limited to certain specific examples. For instance, we
	might say that execution through node n will be represented only
	by visits 0, 1, 2, 3, i, and i + 1 (for a symbolic value i). The
	variable state at visits 4 and i + 2 will be calculated but no
	further execution will be done."""

	def __init__ (self, p, solv, inliner = None, fast = False):
		self.p = p
		self.solv = solv
		self.inp_envs = {}
		self.mem_calls = {}
		self.add_input_envs ()

		self.node_pc_envs = {}
		self.node_pc_env_order = []
		self.arc_pc_envs = {}
		self.inliner = inliner
		self.funcs = {}
		self.pc_env_requests = set ()
		self.fast = fast
		self.induct_var_env = {}
		self.contractions = {}

		self.local_defs_unsat = False
		self.use_known_eqs = True

		self.avail_hyps = set ()
		self.used_hyps = set ()

	def add_input_envs (self):
		for (entry, _, _, args) in self.p.entries:
			self.inp_envs[entry] = mk_inp_env (entry, args, self)

	def get_reachable (self, split, n):
		return self.p.is_reachable_from (split, n)

	class TooGeneral (Exception):
		def __init__ (self, split):
			self.split = split

	def get_tag_vcount (self, (n, vcount), tag):
		if tag == None:
			tag = self.p.node_tags[n][0]
		vcount_r = [(split, count, self.get_reachable (split, n))
			for (split, count) in vcount
			if self.p.node_tags[split][0] == tag]
		for (split, count, r) in vcount_r:
			if not r and not count.has_zero ():
				return (tag, None)
			assert count.is_visit_count
		vcount = [(s, c) for (s, c, r) in vcount_r if r]
		vcount = tuple (sorted (vcount))

		loop_id = self.p.loop_id (n)
		if loop_id != None:
			for (split, visits) in vcount:
				if (self.p.loop_id (split) == loop_id
						and visits.kind == 'Options'):
					raise self.TooGeneral (split)

		return (tag, vcount)

	def get_node_pc_env (self, (n, vcount), tag = None, request = True):
		tag, vcount = self.get_tag_vcount ((n, vcount), tag)
		if vcount == None:
			return None

		if (tag, n, vcount) in self.node_pc_envs:
			return self.node_pc_envs[(tag, n, vcount)]

		if request:
			self.pc_env_requests.add (((n, vcount), tag))

		self.warm_pc_env_cache ((n, vcount), tag)

		pc_env = self.get_node_pc_env_raw ((n, vcount), tag)
		if pc_env:
			pc_env = self.apply_known_eqs_pc_env ((n, vcount),
				tag, pc_env)

		assert not (tag, n, vcount) in self.node_pc_envs
		self.node_pc_envs[(tag, n, vcount)] = pc_env
		if pc_env:
			self.node_pc_env_order.append ((tag, n, vcount))

		return pc_env

	def warm_pc_env_cache (self, n_vc, tag):
		'this is to avoid recursion limits and spot bugs'
		prev_chain = []
		for i in range (5000):
			prevs = self.prevs (n_vc)
			try:
				prevs = [p for p in prevs
					if (tag, p[0], p[1])
						not in self.node_pc_envs
					if self.get_tag_vcount (p, None)
						== (tag, n_vc[1])]
			except self.TooGeneral:
				break
			if not prevs:
				break
			n_vc = prevs[0]
			prev_chain.append(n_vc)
		if not (len (prev_chain) < 5000):
			printout ([n for (n, vc) in prev_chain])
			assert len (prev_chain) < 5000, (prev_chain[:10],
				prev_chain[-10:])
		
		prev_chain.reverse ()
		for n_vc in prev_chain:
			self.get_node_pc_env (n_vc, tag, request = False)

	def get_loop_pc_env (self, split, vcount):
		vcount2 = dict (vcount)
		vcount2[split] = vc_num (0)
		vcount2 = tuple (sorted (vcount2.items ()))
		prev_pc_env = self.get_node_pc_env ((split, vcount2))
		if prev_pc_env == None:
			return None
		(_, prev_env) = prev_pc_env
		mem_calls = self.scan_mem_calls (prev_env)
		mem_calls = self.add_loop_mem_calls (split, mem_calls)
		def av (nm, typ, mem_name = None):
			nm2 = '%s_loop_at_%s' % (nm, split)
			return self.add_var (nm2, typ,
				mem_name = mem_name, mem_calls = mem_calls)
		env = {}
		consts = set ()
		for (nm, typ) in prev_env:
			check_const = self.fast or (typ in
				[builtinTs['HTD'], builtinTs['Dom']])
			if check_const and self.is_synt_const (nm, typ, split):
				env[(nm, typ)] = prev_env[(nm, typ)]
				consts.add ((nm, typ))
			else:
				env[(nm, typ)] = av (nm + '_after', typ,
					('Loop', prev_env[(nm, typ)]))
		for (nm, typ) in prev_env:
			if (nm, typ) in consts:
				continue
			z = self.var_rep_request ((nm, typ), 'Loop',
				(split, vcount), env)
			if z:
				env[(nm, typ)] = z

		pc = mk_smt_expr (av ('pc_of', boolT), boolT)
		if self.fast:
			imp = syntax.mk_implies (pc, prev_pc_env[0])
			self.solv.assert_fact (imp, prev_env,
				unsat_tag = ('LoopPCImp', split))

		return (pc, env)

	def is_synt_const (self, nm, typ, split):
		"""check if a variable at a split point is a syntactic constant
		which is always unmodified by the loop.
		we allow cases where a variable is renamed and renamed back
		during the loop (this often happens because of inlining).
		the check is done by depth-first-search backward through the
		graph looking for a source of a variant value."""
		loop = self.p.loop_id (split)
		loop_set = set (self.p.loop_body (split))
		
		orig_nm = nm
		safe = set ([(orig_nm, split)])
		first_step = True
		visit = []
		count = 0
		while first_step or visit:
			if first_step:
				(nm, n) = (orig_nm, split)
				first_step = False
			else:
				(nm, n) = visit.pop ()
				if (nm, n) in safe:
					continue
				elif n == split:
					return False
			new_nm = nm
			node = self.p.nodes[n]
			if node.kind == 'Call':
				if (nm, typ) not in node.rets:
					pass
				elif self.fast_const_ret (n, nm, typ):
					pass
				else:
					return False
			elif node.kind == 'Basic':
				upds = [arg for (lv, arg) in node.upds
					if lv == (nm, typ)]
				if [v for v in upds if v.kind != 'Var']:
					return False
				if upds:
					new_nm = upds[0].name
			preds = [(new_nm, n2) for n2 in self.p.preds[n]
				if n2 in loop_set]
			unknowns = [p for p in preds if p not in safe]
			if unknowns:
				visit.extend ([(nm, n)] + unknowns)
			else:
				safe.add ((nm, n))
			count += 1
			if count % 100000 == 0:
				trace ('is_synt_const: %d iterations' % count)
				trace ('visit length %d' % len (visit))
				trace ('visit tail %s' % visit[-20:])
		return True

	def fast_const_ret (self, n, nm, typ):
		"""determine if we can heuristically consider this return
		value to be the same as an input. this is known for some
		function returns, e.g. memory.
		this is important for heuristic "fast" analysis."""
		if not self.fast:
			return False
		node = self.p.nodes[n]
		assert node.kind == 'Call'
		for hook in target_objects.hooks ('rep_unsafe_const_ret'):
			if hook (node, nm, typ):
				return True
		return False

	def get_node_pc_env_raw (self, (n, vcount), tag):
		if n in self.inp_envs:
			return (true_term, self.inp_envs[n])

		for (split, count) in vcount:
			if split == n and count == vc_offs (0):
				return self.get_loop_pc_env (split, vcount)

		pc_envs = [pc_env for n_prev in self.p.preds[n]
			if self.p.node_tags[n_prev][0] == tag
			for pc_env in self.get_arc_pc_envs (n_prev,
				(n, vcount))]

		pc_envs = [pc_env for pc_env in pc_envs if pc_env]
		if pc_envs == []:
			return None

		if n == 'Err':
			# we'll never care about variable values here
			# and there are sometimes a LOT of arcs to Err
			# so we save a lot of merge effort
			pc_envs = [(to_smt_expr (pc, env, self.solv), {})
				for (pc, env) in pc_envs]

		(pc, env, large) = merge_envs_pcs (pc_envs, self.solv)

		if large or len (smt_expr (pc, env, self.solv)) > 80:
			name = self.path_cond_name ((n, vcount), tag)
			name = self.solv.add_def (name, pc, env)
			pc = mk_smt_expr (name, boolT)
		
		for (nm, typ) in env:
			if len (env[(nm, typ)]) > 80:
				env[(nm, typ)] = self.contract (nm, (n, vcount),
					env[(nm, typ)], typ)

		return (pc, env)

	def contract (self, name, n_vc, val, typ):
		if val in self.contractions:
			return self.contractions[val]

		name = self.local_name_before (name, n_vc)
		name = self.solv.add_def (name, mk_smt_expr (val, typ), {})
		
		self.contractions[val] = name
		return name

	def get_arc_pc_envs (self, n, n_vc2):
		try:
			prevs = [n_vc for n_vc in self.prevs (n_vc2)
				if n_vc[0] == n]
			assert len (prevs) <= 1
			return [self.get_arc_pc_env (n_vc, n_vc2)
				for n_vc in prevs]
		except self.TooGeneral, e:
			# consider specialisations of the target
			specs = self.specialise (n_vc2, e.split)
			specs = [(n_vc2[0], spec) for spec in specs]
			return [pc_env for spec in specs
				for pc_env in self.get_arc_pc_envs (n, spec)]

	def get_arc_pc_env (self, (n, vcount), n2):
		tag, vcount = self.get_tag_vcount ((n, vcount), None)

		if vcount == None:
			return None

		assert self.is_cont ((n, vcount), n2), ((n, vcount),
			n2, self.p.nodes[n].get_conts ())

		if (n, vcount) in self.arc_pc_envs:
			return self.arc_pc_envs[(n, vcount)].get (n2[0])

		if self.get_node_pc_env ((n, vcount), request = False) == None:
			return None

		arcs = self.emit_node ((n, vcount))
		arcs = dict ([(cont, (pc, env)) for (cont, pc, env) in arcs])

		self.arc_pc_envs[(n, vcount)] = arcs
		return arcs.get (n2[0])

	def add_local_def (self, n, vname, name, val, env):
		if self.local_defs_unsat:
			smt_name = self.solv.add_var (name, val.typ)
			eq = mk_eq (mk_smt_expr (smt_name, val.typ), val)
			self.solv.assert_fact (eq, env, unsat_tag
				= ('Def', n, vname))
		else:
			smt_name = self.solv.add_def (name, val, env)
		return smt_name

	def add_var (self, name, typ, mem_name = None, mem_calls = None):
		r = self.solv.add_var_restr (name, typ, mem_name = mem_name)
		if typ == syntax.builtinTs['Mem']:
			r_x = solver.parse_s_expression (r)
			self.mem_calls[r_x] = mem_calls
		return r

	def var_rep_request (self, (nm, typ), kind, n_vc, env):
		assert type (n_vc[0]) != str
		for hook in target_objects.hooks ('problem_var_rep'):
			z = hook (self.p, (nm, typ), kind, n_vc[0])
			if z == None:
				continue
			if z[0] == 'SplitMem':
				assert typ == builtinTs['Mem']
				(_, addr) = z
				addr = smt_expr (addr, env, self.solv)
				name = '%s_for_%s' % (nm,
					self.node_count_name (n_vc))
				return self.solv.add_split_mem_var (addr, name,
					typ, mem_name = 'SplitMemNonsense')
			else:
				assert z == None

	def emit_node (self, n):
		(pc, env) = self.get_node_pc_env (n, request = False)
		tag = self.p.node_tags[n[0]][0]
		app_eqs = self.apply_known_eqs_tm (n, tag)
		# node = logic.simplify_node_elementary (self.p.nodes[n[0]])
		# whether to ignore unreachable Cond arcs seems to be a huge
		# dilemma. if we ignore them, some reachable sites become
		# unreachable and we can't interpret all hyps
		# if we don't ignore them, the variable set disagrees with
		# var_deps and so the abstracted loop pc/env may not be
		# sufficient and we get EnvMiss again. I don't really know
		# what to do about this corner case.
		node = self.p.nodes[n[0]]
		env = dict (env)

		if node.kind == 'Call':
			self.try_inline (n[0], pc, env)

		if pc == false_term:
			return [(c, false_term, {}) for c in node.get_conts()]
		elif node.kind == 'Cond' and node.left == node.right:
			return [(node.left, pc, env)]
		elif node.kind == 'Cond' and node.cond == true_term:
			return [(node.left, pc, env),
				(node.right, false_term, env)]
		elif node.kind == 'Basic':
			upds = []
			for (lv, v) in node.upds:
				if v.kind == 'Var':
					upds.append ((lv, env[(v.name, v.typ)]))
				else:
					name = self.local_name (lv[0], n)
					v = app_eqs (v)
					vname = self.add_local_def (n,
						('Var', lv), name, v, env)
					upds.append ((lv, vname))
			for (lv, v) in upds:
				env[lv] = v
			return [(node.cont, pc, env)]
		elif node.kind == 'Cond':
			name = self.cond_name (n)
			cond = self.p.fresh_var (name, boolT)
			env[(cond.name, boolT)] = self.add_local_def (n,
				'Cond', name, app_eqs (node.cond), env)
			lpc = mk_and (cond, pc)
			rpc = mk_and (mk_not (cond), pc)
			return [(node.left, lpc, env), (node.right, rpc, env)]
		elif node.kind == 'Call':
			nm = self.success_name (node.fname, n)
			success = self.solv.add_var (nm, boolT)
			success = mk_smt_expr (success, boolT)
			fun = functions[node.fname]
			ins = dict ([((x, typ), smt_expr (app_eqs (arg), env, self.solv))
				for ((x, typ), arg) in azip (fun.inputs, node.args)])
			mem_name = None
			for (x, typ) in reversed (fun.inputs):
				if typ == builtinTs['Mem']:
					inp_mem = ins[(x, typ)]
					mem_name = (node.fname, inp_mem)
			mem_calls = self.scan_mem_calls (ins)
			mem_calls = self.add_mem_call (node.fname, mem_calls)
			outs = {}
			for ((x, typ), (y, typ2)) in azip (node.rets, fun.outputs):
				assert typ2 == typ
				if self.fast_const_ret (n[0], x, typ):
					outs[(y, typ2)] = env [(x, typ)]
					continue
				name = self.local_name (x, n)
				env[(x, typ)] = self.add_var (name, typ,
					mem_name = mem_name,
					mem_calls = mem_calls)
				outs[(y, typ2)] = env[(x, typ)]
			for ((x, typ), (y, _)) in azip (node.rets, fun.outputs):
				z = self.var_rep_request ((x, typ),
					'Call', n, env)
				if z != None:
					env[(x, typ)] = z
					outs[(y, typ)] = z
			self.add_func (node.fname, ins, outs, success, n)
			return [(node.cont, pc, env)]
		else:
			assert not 'node kind understood'

	def fetch_known_eqs (self, n_vc, tag):
		if not self.use_known_eqs:
			return None
		eqs = self.p.known_eqs.get ((n_vc, tag))
		if eqs == None:
			return None
		avail = []
		for (x, n_vc_y, tag_y, y, hyps) in eqs:
			if hyps <= self.avail_hyps:
				(_, env) = self.get_node_pc_env (n_vc_y, tag_y)
				avail.append ((x, smt_expr (y, env, self.solv)))
				self.used_hyps.update (hyps)
		if avail:
			return avail
		return None

	def apply_known_eqs_pc_env (self, n_vc, tag, (pc, env)):
		eqs = self.fetch_known_eqs (n_vc, tag)
		if eqs == None:
			return (pc, env)
		env = dict (env)
		for (x, sx) in eqs:
			if x.kind == 'Var':
				cur_rhs = env[x.name]
				for y in env:
					if env[y] == cur_rhs:
						trace ('substituted %s at %s.' % (y, n_vc))
						env[y] = sx
		return (pc, env)

	def apply_known_eqs_tm (self, n_vc, tag):
		eqs = self.fetch_known_eqs (n_vc, tag)
		if eqs == None:
			return lambda x: x
		eqs = dict ([(x, mk_smt_expr (sexpr, x.typ))
			for (x, sexpr) in eqs])
		return lambda tm: logic.recursive_term_subst (eqs, tm)

	def rebuild (self, solv = None):
		requests = self.pc_env_requests

		self.node_pc_env_order = []
		self.node_pc_envs = {}
		self.arc_pc_envs = {}
		self.funcs = {}
		self.pc_env_requests = set ()
		self.induct_var_env = {}
		self.contractions = {}

		if not solv:
			solv = Solver (produce_unsat_cores
				= self.local_defs_unsat)
		self.solv = solv

		self.add_input_envs ()

		self.used_hyps = set ()
		run_requests (self, requests)

	def add_func (self, name, inputs, outputs, success, n_vc):
		assert n_vc not in self.funcs
		self.funcs[n_vc] = (inputs, outputs, success)
		for pair in pairings.get (name, []):
			self.funcs.setdefault (pair.name, [])
			group = self.funcs[pair.name]
			for n_vc2 in group:
				if self.get_func_pairing (n_vc, n_vc2):
					self.add_func_assert (n_vc, n_vc2)
			group.append (n_vc)

	def get_func (self, n_vc, tag = None):
		"""returns (input_env, output_env, success_var) for
		function call at given n_vc."""
		tag, vc = self.get_tag_vcount (n_vc, tag)
		n_vc = (n_vc[0], vc)
		assert self.p.nodes[n_vc[0]].kind == 'Call'

		if n_vc not in self.funcs:
			# try to ensure n_vc has been emitted
			cont = self.get_cont (n_vc)
			self.get_node_pc_env (cont, tag = tag)

		return self.funcs[n_vc]

	def get_func_pairing_nocheck (self, n_vc, n_vc2):
		fnames = [self.p.nodes[n_vc[0]].fname,
			self.p.nodes[n_vc2[0]].fname]
		pairs = [pair for pair in pairings[list (fnames)[0]]
			if set (pair.funs.values ()) == set (fnames)]
		if not pairs:
			return None
		[pair] = pairs
		if pair.funs[pair.tags[0]] == fnames[0]:
			return (pair, n_vc, n_vc2)
		else:
			return (pair, n_vc2, n_vc)

	def get_func_pairing (self, n_vc, n_vc2):
		res = self.get_func_pairing_nocheck (n_vc, n_vc2)
		if not res:
			return res
		(pair, l_n_vc, r_n_vc) = res
		(lin, _, _) = self.funcs[l_n_vc]
		(rin, _, _) = self.funcs[r_n_vc]
		l_mem_calls = self.scan_mem_calls (lin)
		r_mem_calls = self.scan_mem_calls (rin)
		tags = pair.tags
		(c, s) = mem_calls_compatible (tags, l_mem_calls, r_mem_calls)
		if not c:
			trace ('skipped emitting func pairing %s -> %s'
				% (l_n_vc, r_n_vc))
			trace ('  ' + s)
			return None
		return res

	def get_func_assert (self, n_vc, n_vc2):
		(pair, l_n_vc, r_n_vc) = self.get_func_pairing (n_vc, n_vc2)
		(ltag, rtag) = pair.tags
		(inp_eqs, out_eqs) = pair.eqs
		(lin, lout, lsucc) = self.funcs[l_n_vc]
		(rin, rout, rsucc) = self.funcs[r_n_vc]
		lpc = self.get_pc (l_n_vc)
		rpc = self.get_pc (r_n_vc)
		envs = {ltag + '_IN': lin, rtag + '_IN': rin,
			ltag + '_OUT': lout, rtag + '_OUT': rout}
		inp_eqs = inst_eqs (inp_eqs, envs, self.solv)
		out_eqs = inst_eqs (out_eqs, envs, self.solv)
		succ_imp = mk_implies (rsucc, lsucc)

		return mk_implies (foldr1 (mk_and, inp_eqs + [rpc]),
			foldr1 (mk_and, out_eqs + [succ_imp]))

	def add_func_assert (self, n_vc, n_vc2):
		imp = self.get_func_assert (n_vc, n_vc2)
		imp = logic.weaken_assert (imp)
		if self.local_defs_unsat:
			self.solv.assert_fact (imp, {}, unsat_tag = ('FunEq',
				ln, rn))
		else:
			self.solv.assert_fact (imp, {})

	def node_count_name (self, (n, vcount)):
		name = str (n)
		bits = [str (n)] + ['%s=%s' % (split, count)
			for (split, count) in vcount]
		return '_'.join (bits)

	def get_mem_calls (self, mem_sexpr):
		mem_sexpr = solver.parse_s_expression (mem_sexpr)
		return self.get_mem_calls_sexpr (mem_sexpr)

	def get_mem_calls_sexpr (self, mem_sexpr):
		stores = set (['store-word32', 'store-word8', 'store-word64'])
		if mem_sexpr in self.mem_calls:
			return self.mem_calls[mem_sexpr]
		elif len (mem_sexpr) == 4 and mem_sexpr[0] in stores:
			return self.get_mem_calls_sexpr (mem_sexpr[1])
		elif mem_sexpr[:1] == ('ite', ):
			(_, _, x, y) = mem_sexpr
			x_calls = self.get_mem_calls_sexpr (x)
			y_calls = self.get_mem_calls_sexpr (y)
			return merge_mem_calls (x_calls, y_calls)
		elif mem_sexpr in self.solv.defs:
			mem_sexpr = self.solv.defs[mem_sexpr]
			return self.get_mem_calls_sexpr (mem_sexpr)
		assert not "mem_calls fallthrough", mem_sexpr

	def scan_mem_calls (self, env):
		for (nm, typ) in env:
			if typ == syntax.builtinTs['Mem']:
				v = env[(nm, typ)]
				if v[0] == 'SplitMem':
					continue
				return self.get_mem_calls (v)
		return None

	def add_mem_call (self, fname, mem_calls):
		if mem_calls == None:
			return None
		mem_calls = dict (mem_calls)
		(min_calls, max_calls) = mem_calls.get (fname, (0, 0))
		if max_calls == None:
			mem_calls[fname] = (min_calls + 1, None)
		else:
			mem_calls[fname] = (min_calls + 1, max_calls + 1)
		return mem_calls

	def add_loop_mem_calls (self, split, mem_calls):
		if mem_calls == None:
			return None
		fnames = set ([self.p.nodes[n].fname
			for n in self.p.loop_body (split)
			if self.p.nodes[n].kind == 'Call'])
		if not fnames:
			return mem_calls
		mem_calls = dict (mem_calls)
		for fname in fnames:
			if fname not in mem_calls:
				mem_calls[fname] = (0, None)
			else:
				(min_calls, max_calls) = mem_calls[fname]
				mem_calls[fname] = (min_calls, None)
		return mem_calls

	# note these names are designed to be unique by suffix
	# (so that smt names are independent of order of requests)
	def local_name (self, s, n_vc):
		return '%s_after_%s' % (s, self.node_count_name (n_vc))

	def local_name_before (self, s, n_vc):
		return '%s_v_at_%s' % (s, self.node_count_name (n_vc))

	def cond_name (self, n_vc):
		return 'cond_at_%s' % self.node_count_name (n_vc)

	def path_cond_name (self, n_vc, tag):
		return 'path_cond_to_%s_%s' % (
			self.node_count_name (n_vc), tag)

	def success_name (self, fname, n_vc):
		bits = fname.split ('.')
		nms = ['_'.join (bits[i:]) for i in range (len (bits))
			if bits[i:][0].isalpha ()]
		if nms:
			nm = nms[-1]
		else:
			nm = 'fun'
		return '%s_success_at_%s' % (nm, self.node_count_name (n_vc))

	def try_inline (self, n, pc, env):
		if not self.inliner:
			return False

		inline = self.inliner ((self.p, n))
		if not inline:
			return False

		# make sure this node is reachable before inlining
		if self.solv.test_hyp (mk_not (pc), env):
			trace ('Skipped inlining at %d.' % n)
			return False

		trace ('Inlining at %d.' % n)
		inline ()
		raise InlineEvent ()

	def incr (self, vcount, n, incr):
		vcount2 = dict (vcount)
		vcount2[n] = vcount2[n].incr (incr)
		if vcount2[n] == None:
			return None
		return tuple (sorted (vcount2.items ()))

	def get_cont (self, (n, vcount)):
		[c] = self.p.nodes[n].get_conts ()
		vcount2 = dict (vcount)
		if n in vcount2:
			vcount = self.incr (vcount, n, 1)
		cont = (c, vcount)
		assert self.is_cont ((n, vcount), cont)
		return cont

	def is_cont (self, (n, vcount), (n2, vcount2)):
		if n2 not in self.p.nodes[n].get_conts ():
			trace ('Not a graph cont.')
			return False

		vcount_d = dict (vcount)
		vcount_d2 = dict (vcount2)
		if n in vcount_d2:
			if n in vcount_d:
				assert vcount_d[n].kind != 'Options'
			vcount_d2[n] = vcount_d2[n].incr (-1)

		if not vcount_d <= vcount_d2:
			trace ('Restrictions not subset.')
			return False

		for (split, count) in vcount_d2.iteritems ():
			if split in vcount_d:
				continue
			if self.get_reachable (split, n):
				return False
			if not count.has_zero ():
				return False

		return True

	def prevs (self, (n, vcount)):
		prevs = []
		vcount_d = dict (vcount)
		for p in self.p.preds[n]:
			if p in vcount_d:
				vcount2 = self.incr (vcount, p, -1)
				if vcount2 == None:
					continue
				prevs.append ((p, vcount2))
			else:
				prevs.append ((p, vcount))
		return prevs

	def specialise (self, (n, vcount), split):
		vcount = dict (vcount)
		assert vcount[split].kind == 'Options'
		specs = []
		for n in vcount[split].opts:
			v = dict (vcount)
			v[split] = n
			specs.append (tuple (sorted (v.items ())))
		return specs

	def get_pc (self, (n, vcount), tag = None):
		pc_env = self.get_node_pc_env ((n, vcount), tag = tag)
		if pc_env == None:
			trace ('Warning: unreachable n_vc, tag: %s, %s' % ((n, vcount), tag))
			return false_term
		(pc, env) = pc_env
		return to_smt_expr (pc, env, self.solv)

	def to_smt_expr (self, expr, (n, vcount), tag = None):
		pc_env = self.get_node_pc_env ((n, vcount), tag = tag)
		(pc, env) = pc_env
		return to_smt_expr (expr, env, self.solv)

	def get_induct_var (self, (n1, n2)):
		if (n1, n2) not in self.induct_var_env:
			vname = self.solv.add_var ('induct_i_%d_%d' % (n1, n2),
				word32T)
			self.induct_var_env[(n1, n2)] = vname
			self.pc_env_requests.add (((n1, n2), 'InductVar'))
		else:
			vname = self.induct_var_env[(n1, n2)]
		return mk_smt_expr (vname, word32T)

	def interpret_hyp (self, hyp):
		return hyp.interpret (self)

	def interpret_hyp_imps (self, hyps, concl):
		imp = concl
		for h in hyps:
			imp = mk_implies (self.interpret_hyp (h), imp)
		return logic.strengthen_hyp (imp)

	def test_hyp_whyps (self, hyp, hyps, cache = None, fast = False,
			model = None):
		self.avail_hyps = set (hyps)
		if not self.used_hyps <= self.avail_hyps:
			self.rebuild ()

		last_test[0] = (hyp, hyps, list (self.pc_env_requests))

		expr = self.interpret_hyp_imps (hyps, hyp)

		trace ('Testing hyp whyps', push = 1)
		trace ('requests = %s' % self.pc_env_requests)

		expr_s = smt_expr (expr, {}, self.solv)
		if cache and expr_s in cache:
			trace ('Cached: %s' % cache[expr_s])
			return cache[expr_s]
		if fast:
			trace ('(not in cache)')
			return None

		self.solv.add_pvalid_dom_assertions ()

		(result, _) = self.solv.parallel_test_hyps ([(None, expr)], {},
			model = model)
		trace ('Result: %s' % result, push = -1)
		if cache != None:
			cache[expr_s] = result
		if not result:
			last_failed_test[0] = last_test[0]
		return result

	def test_hyp_imp (self, hyps, hyp, model = None):
		return self.test_hyp_whyps (self.interpret_hyp (hyp), hyps,
			model = model)

	def test_hyp_imps (self, imps):
		last_hyp_imps[0] = imps
		if imps == []:
			return (True, None)
		interp_imps = list (enumerate ([self.interpret_hyp_imps (hyps,
				self.interpret_hyp (hyp))
			for (hyps, hyp) in imps]))
		reqs = list (self.pc_env_requests)
		last_test[0] = (self.interpret_hyp (hyp), hyps, reqs)
		self.solv.add_pvalid_dom_assertions ()
		result = self.solv.parallel_test_hyps (interp_imps, {})
		assert result[0] in [True, False], result
		if result[0] == False:
			(hyps, hyp) = imps[result[1]]
			last_test[0] = (self.interpret_hyp (hyp), hyps, reqs)
			last_failed_test[0] = last_test[0]
		return result

	def replay_requests (self, reqs):
		for ((n, vc), tag) in reqs:
			self.get_node_pc_env ((n, vc), tag = tag)

last_test = [0]
last_failed_test = [0]
last_hyp_imps = [0]

def to_smt_expr_under_op (expr, env, solv):
	if expr.kind == 'Op':
		vals = [to_smt_expr (v, env, solv) for v in expr.vals]
		return syntax.Expr ('Op', expr.typ, name = expr.name,
			vals = vals)
	else:
		return to_smt_expr (expr, env, solv)

def inst_eq_with_envs ((x, env1), (y, env2), solv):
	x = to_smt_expr_under_op (x, env1, solv)
	y = to_smt_expr_under_op (y, env2, solv)
	if x.typ == syntax.builtinTs['RelWrapper']:
		return logic.apply_rel_wrapper (x, y)
	else:
		return mk_eq (x, y)

def inst_eqs (eqs, envs, solv):
	return [inst_eq_with_envs ((x, envs[x_addr]), (y, envs[y_addr]), solv)
		for ((x, x_addr), (y, y_addr)) in eqs]

def subst_induct (expr, induct_var):
	substs = {('%n', word32T): induct_var}
	return logic.var_subst (expr, substs, must_subst = False)

printed_hyps = {}
def print_hyps (hyps):
	hyps = tuple (hyps)
	if hyps in printed_hyps:
		trace ('hyps = %s' % printed_hyps[hyps])
	else:
		hname = 'hyp_set_%d' % (len (printed_hyps) + 1)
		trace ('%s = %s' % (hname, list (hyps)))
		printed_hyps[hname] = hyps
		trace ('hyps = %s' % hname)

def merge_mem_calls (mem_calls_x, mem_calls_y):
	if mem_calls_x == mem_calls_y:
		return mem_calls_x
	mem_calls = {}
	for fname in set (mem_calls_x.keys () + mem_calls_y.keys ()):
		(min_x, max_x) = mem_calls_x.get (fname, (0, 0))
		(min_y, max_y) = mem_calls_y.get (fname, (0, 0))
		if None in [max_x, max_y]:
			max_v = None
		else:
			max_v = max (max_x, max_y)
		mem_calls[fname] = (min (min_x, min_y), max_v)
	return mem_calls

def mem_calls_compatible (tags, l_mem_calls, r_mem_calls):
	if l_mem_calls == None or r_mem_calls == None:
		return (True, None)
	r_cast_calls = {}
	for (fname, calls) in l_mem_calls.iteritems ():
		pairs = [pair for pair in pairings[fname]
			if pair.tags == tags]
		if not pairs:
			return (None, 'no pairing for %s' % fname)
		assert len (pairs) <= 1, pairs
		[pair] = pairs
		r_fun = pair.funs[tags[1]]
		if not [nm for (nm, typ) in functions[r_fun].outputs
				if typ == syntax.builtinTs['Mem']]:
			continue
		r_cast_calls[pair.funs[tags[1]]] = calls
	for fname in set (r_cast_calls.keys () + r_mem_calls.keys ()):
		r_cast = r_cast_calls.get (fname, (0, 0))
		r_actual = r_mem_calls.get (fname, (0, 0))
		s = 'mismatch in calls to %s and pairs, %s / %s' % (fname,
			r_cast, r_actual)
		if r_cast[1] != None and r_cast[1] < r_actual[0]:
			return (None, s)
		if r_actual[1] != None and r_actual[1] < r_cast[0]:
			return (None, s)
	return (True, None)

def mk_inp_env (n, args, rep):
	trace ('rep_graph setting up input env at %d' % n, push = 1)
	inp_env = {}

	for (v_nm, typ) in args:
		inp_env[(v_nm, typ)] = rep.add_var (v_nm + '_init', typ,
			mem_name = 'Init', mem_calls = {})
	for (v_nm, typ) in args:
		z = rep.var_rep_request ((v_nm, typ), 'Init', (n, ()), inp_env)
		if z:
			inp_env[(v_nm, typ)] = z

	trace ('done setting up input env at %d' % n, push = -1)
	return inp_env

def mk_graph_slice (p, inliner = None, fast = False, mk_solver = Solver):
	trace ('rep_graph setting up solver', push = 1)
	solv = mk_solver ()
	trace ('rep_graph setting up solver', push = -1)
	return GraphSlice (p, solv, inliner, fast = fast)

def run_requests (rep, requests):
	for (n_vc, tag) in requests:
		if tag == 'InductVar':
			rep.get_induct_var (n_vc)
		else:
			rep.get_pc (n_vc, tag = tag)
	rep.solv.add_pvalid_dom_assertions ()

import re
paren_w_re = re.compile (r"(\(|\)|\w+)")

def mk_function_link_hyps (p, call_vis, tag, adjust_eq_seq = None):
	(entry, _, args) = p.get_entry_details (tag)
	((call_site, restrs), call_tag) = call_vis
	assert p.nodes[call_site].kind == 'Call'
	entry_vis = ((entry, ()), p.node_tags[entry][0])

	args = [syntax.mk_var (nm, typ) for (nm, typ) in args]

	pc = pc_true_hyp (call_vis)
	eq_seq = logic.azip (p.nodes[call_site].args, args)
	if adjust_eq_seq:
		eq_seq = adjust_eq_seq (eq_seq)
	hyps = [pc] + [eq_hyp ((x, call_vis), (y, entry_vis))
		for (x, y) in eq_seq
		if x.typ.kind == 'Word' or x.typ == syntax.builtinTs['Mem']
			or x.typ.kind == 'WordArray']

	return hyps

