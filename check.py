# * Copyright 2015, NICTA
# *
# * This software may be distributed and modified according to the terms of
# * the BSD 2-Clause license. Note that NO WARRANTY is provided.
# * See "LICENSE_BSD2.txt" for details.
# *
# * @TAG(NICTA_BSD)

# proof scripts and check process

from rep_graph import mk_graph_slice, Hyp, eq_hyp, pc_true_hyp, pc_false_hyp
import rep_graph
from problem import Problem, consider_inline_c, inline_at_point

from solver import to_smt_expr
from target_objects import functions, pairings, trace, printout
import target_objects
from rep_graph import (vc_num, vc_offs, vc_double_range, vc_upto, mk_vc_opts,
	VisitCount)
import logic

from syntax import (true_term, false_term, boolT, mk_var, mk_word32, mk_word8,
	mk_plus, mk_minus, word32T, word8T, mk_and, mk_eq, mk_implies, mk_not,
	rename_expr)
import syntax

def build_problem (pairing, force_inline = None):
	p = Problem (pairing)

	for (tag, fname) in pairing.funs.items ():
		p.add_entry_function (functions[fname], tag)

	p.do_analysis ()

	# FIXME: the inlining is heuristic and belongs in 'search'
	inline_completely_unmatched (p)
	
	# now do any C inlining
	inline_reachable_unmatched_C (p, force_inline)

	trace ('Done inlining.')

	p.pad_merge_points ()
	p.do_analysis ()

	return p

def inline_completely_unmatched (p, ref_tags = None):
	if ref_tags == None:
		ref_tags = p.pairing.tags
	while True:
		ns = [n for n in p.nodes
			if p.nodes[n].kind == 'Call'
			if not [pair for pair
				in pairings.get (p.nodes[n].fname, [])
				if pair.tags == ref_tags]]
		for n in ns:
			inline_at_point (p, n)
		if not ns:
			return

def inline_reachable_unmatched_C (p, force_inline = None):
	if 'C' not in p.pairing.tags:
		return
	[compare_tag] = [tag for tag in p.pairing.tags if tag != 'C']
	inline_reachable_unmatched (p, 'C', compare_tag, force_inline)

def inline_reachable_unmatched (p, inline_tag, compare_tag,
		force_inline = None):
	funs = [pair.funs['C']
		for n in p.nodes
		if p.nodes[n].kind == 'Call'
		if p.node_tags[n][0] != 'C'
		for pair in pairings[p.nodes[n].fname]
		if 'C' in pair.tags]

	rep = mk_graph_slice (p,
		consider_inline_c (funs, force_inline))
	opts = vc_double_range (3, 3)
	while True:
		try:
			limits = [(n, opts) for n in p.loop_heads ()]

			for n in p.nodes.keys ():
				try:
					r = rep.get_node_pc_env ((n, limits))
				except rep.TooGeneral:
					pass

			rep.get_node_pc_env (('Ret', limits), 'C')
			rep.get_node_pc_env (('Err', limits), 'C')
			break
		except rep_graph.InlineEvent:
			continue

def inst_eqs (p, restrs, eqs, tag_map = {}):
	addr_map = {}
	if not tag_map:
		tag_map = dict ([(tag, tag) for tag in p.tags ()])
	for (pair_tag, p_tag) in tag_map.iteritems ():
		addr_map[pair_tag + '_IN'] = ((p.get_entry (p_tag), ()), p_tag)
		addr_map[pair_tag + '_OUT'] = (('Ret', restrs), p_tag)
	renames = p.entry_exit_renames (tag_map.values ())
	for (pair_tag, p_tag) in tag_map.iteritems ():
		renames[pair_tag + '_IN'] = renames[p_tag + '_IN']
		renames[pair_tag + '_OUT'] = renames[p_tag + '_OUT']
	hyps = []
	for (lhs, rhs) in eqs:
		vals = [(rename_expr (x, renames[x_addr]), addr_map[x_addr])
			for (x, x_addr) in (lhs, rhs)]
		hyps.append (eq_hyp (vals[0], vals[1]))
	return hyps

def init_point_hyps (p):
	(inp_eqs, _) = p.pairing.eqs
	return inst_eqs (p, (), inp_eqs)

class ProofNode:
	def __init__ (self, kind, args = None, subproofs = []):
		self.kind = kind
		self.args = args
		self.subproofs = tuple (subproofs)
		if self.kind == 'Leaf':
			assert args == None
			assert list (subproofs) == []
		elif self.kind == 'Restr':
			(self.point, self.restr_range) = args
			assert len (subproofs) == 1
		elif self.kind == 'Split':
			self.split = args
			(l_details, r_details, eqs, n, loop_r_max) = args
			assert len (subproofs) == 2
		elif self.kind == 'CaseSplit':
			(self.point, self.tag) = args
			assert len (subproofs) == 2
		else:
			assert not 'proof node kind understood'

	def __repr__ (self):
		return 'ProofNode (%r, %r, %r)' % (self.kind,
			self.args, self.subproofs)

	def serialise (self, p, ss):
		if self.kind == 'Leaf':
			ss.append ('Leaf')
		elif self.kind == 'Restr':
			(kind, (x, y)) = self.restr_range
			tag = p.node_tags[self.point][0]
			ss.extend (['Restr', '%d' % self.point,
				tag, kind, '%d' % x, '%d' % y])
		elif self.kind == 'Split':
			(l_details, r_details, eqs, n, loop_r_max) = self.args
			ss.extend (['Split', '%d' % n, '%d' % loop_r_max])
			serialise_details (l_details, ss)
			serialise_details (r_details, ss)
			ss.append ('%d' % len (eqs))
			for (x, y) in eqs:
				serialise_lambda (x, ss)
				serialise_lambda (y, ss)
		elif self.kind == 'CaseSplit':
			ss.extend (['CaseSplit', '%d' % self.point, self.tag])
		else:
			assert not 'proof node kind understood'
		for proof in self.subproofs:
			proof.serialise (p, ss)

	def save_serialise (self, p, fname):
		f = open (fname, 'w')
		ss = []
		self.serialise (p, ss)
		f.write (' '.join (ss) + '\n')
		f.close ()

	def __hash__ (self):
		return syntax.hash_tuplify (self.kind, self.args,
			self.subproofs)

def serialise_details (details, ss):
	(split, (seq_start, step), eqs) = details
	ss.extend (['%d' % split, '%d' % seq_start, '%d' % step])
	ss.append ('%d' % len (eqs))
	for eq in eqs:
		serialise_lambda (eq, ss)

def serialise_lambda (eq_term, ss):
	ss.extend (['Lambda', '%i'])
	word32T.serialise (ss)
	eq_term.serialise (ss)

def deserialise_details (ss, i):
	(split, seq_start, step) = [int (x) for x in ss[i : i + 3]]
	(i, eqs) = syntax.parse_list (deserialise_lambda, ss, i + 3)
	return (i, (split, (seq_start, step), eqs))

def deserialise_lambda (ss, i):
	assert ss[i : i + 2] == ['Lambda', '%i'], (ss, i)
	(i, typ) = syntax.parse_typ (ss, i + 2)
	assert typ == word32T, typ
	(i, eq_term) = syntax.parse_expr (ss, i)
	return (i, eq_term)

def deserialise_double_lambda (ss, i):
	(i, x) = deserialise_lambda (ss, i)
	(i, y) = deserialise_lambda (ss, i)
	return (i, (x, y))

def deserialise_inner (ss, i):
	if ss[i] == 'Leaf':
		return (i + 1, ProofNode ('Leaf'))
	elif ss[i] == 'Restr':
		point = int (ss[i + 1])
		tag = ss[i + 2]
		kind = ss[i + 3]
		assert kind in ['Number', 'Offset'], (kind, i)
		x = int (ss[i + 4])
		y = int (ss[i + 5])
		(i, p1) = deserialise_inner (ss, i + 6)
		return (i, ProofNode ('Restr', (point, (kind, (x, y))), [p1]))
	elif ss[i] == 'Split':
		n = int (ss[i + 1])
		loop_r_max = int (ss[i + 2])
		(i, l_details) = deserialise_details (ss, i + 3)
		(i, r_details) = deserialise_details (ss, i)
		(i, eqs) = syntax.parse_list (deserialise_double_lambda, ss, i)
		(i, p1) = deserialise_inner (ss, i)
		(i, p2) = deserialise_inner (ss, i)
		return (i, ProofNode ('Split', (l_details, r_details, eqs,
			n, loop_r_max), [p1, p2]))
	elif ss[i] == 'CaseSplit':
		n = int (ss[i + 1])
		tag = ss[i + 2]
		(i, p1) = deserialise_inner (ss, i + 3)
		(i, p2) = deserialise_inner (ss, i)
		return (i, ProofNode ('CaseSplit', (n, tag), [p1, p2]))
	else:
		assert not 'proof node type understood', (ss, i)

def deserialise (line):
	ss = line.split ()
	(i, proof) = deserialise_inner (ss, 0)
	assert i == len (ss), (ss, i)
	return proof

def proof_subproblems (p, kind, args, restrs, hyps, path):
	tags = p.pairing.tags
	if kind == 'Leaf':
		return []
	elif kind == 'Restr':
		restr = get_proof_restr (args[0], args[1])
		hyps = hyps + [restr_trivial_hyp (p, args[0], args[1], restrs)]
		return [((restr,) + restrs, hyps,
			'%s (%d limited)' % (path, args[0]))]
	elif kind == 'Split':
		split = args
		return [(restrs, hyps + split_no_loop_hyps (tags, split, restrs),
			'%d init case in %s' % (split[0][0], path)),
		(restrs, hyps + split_loop_hyps (tags, split, restrs, exit = True),
			'%d loop case in %s' % (split[0][0], path))]
	elif kind == 'CaseSplit':
		(point, tag) = args
		visit = ((point, restrs), tag)
		true_hyps = hyps + [pc_true_hyp (visit)]
		false_hyps = hyps + [pc_false_hyp (visit)]
		return [(restrs, true_hyps, 
			'true case (%d visited) in %s' % (point, path)),
		(restrs, false_hyps,
			'false case (%d not visited) in %s' % (point, path))]
	else:
		assert not 'proof node kind understood', proof.kind


def split_heads ((l_details, r_details, eqs, n, _)):
	(l_split, _, _) = l_details
	(r_split, _, _) = r_details
	return [l_split, r_split]

def split_no_loop_hyps (tags, split, restrs):
	((_, (l_seq_start, l_step), _), _, _, n, _) = split

	(l_visit, _) = split_visit_visits (tags, split, restrs, vc_num (n)) 

	return [pc_false_hyp (l_visit)]

def split_visit_one_visit (tag, details, restrs, visit):
	if details == None:
		return None
	(split, (seq_start, step), eqs) = details

	# the split point sequence at low numbers ('Number') is offset
	# by the point the sequence starts. At symbolic offsets we ignore
	# that, instead having the loop counter for the two sequences
	# be the same number of iterations after the sequence start.
	if visit.kind == 'Offset':
		visit = vc_offs (visit.n * step)
	else:
		visit = vc_num (seq_start + (visit.n * step))

	visit = ((split, ((split, visit), ) + restrs), tag)
	return visit

def split_visit_visits (tags, split, restrs, visit):
	(ltag, rtag) = tags
	(l_details, r_details, eqs, _, _) = split

	l_visit = split_visit_one_visit (ltag, l_details, restrs, visit)
	r_visit = split_visit_one_visit (rtag, r_details, restrs, visit)

	return (l_visit, r_visit)

def split_hyps_at_visit (tags, split, restrs, visit):
	(l_details, r_details, eqs, _, _) = split
	(l_split, (l_seq_start, l_step), l_eqs) = l_details
	(r_split, (r_seq_start, r_step), r_eqs) = r_details

	(l_visit, r_visit) = split_visit_visits (tags, split, restrs, visit)
	(l_start, r_start) = split_visit_visits (tags, split, restrs, vc_num (0))
	(l_tag, r_tag) = tags

	def mksub (v):
		return lambda exp: logic.var_subst (exp, {('%i', word32T) : v},
			must_subst = False)
	def inst (exp):
		return logic.inst_eq_at_visit (exp, visit)
	zsub = mksub (mk_word32 (0))
	if visit.kind == 'Number':
		lsub = mksub (mk_word32 (visit.n))
	else:
		lsub = mksub (mk_plus (mk_var ('%n', word32T),
			mk_word32 (visit.n)))

	hyps = [(Hyp ('PCImp', l_visit, r_visit), 'pc imp'),
		(Hyp ('PCImp', l_visit, l_start), '%s pc imp' % l_tag),
		(Hyp ('PCImp', r_visit, r_start), '%s pc imp' % r_tag)]
	hyps += [(eq_hyp ((zsub (l_exp), l_start), (lsub (l_exp), l_visit),
				(l_split, r_split)), '%s const' % l_tag)
			for l_exp in l_eqs if inst (l_exp)]
	hyps += [(eq_hyp ((zsub (r_exp), r_start), (lsub (r_exp), r_visit),
				(l_split, r_split)), '%s const' % r_tag)
			for r_exp in r_eqs if inst (r_exp)]
	hyps += [(eq_hyp ((lsub (l_exp), l_visit), (lsub (r_exp), r_visit),
				(l_split, r_split)), 'eq')
			for (l_exp, r_exp) in eqs
			if inst (l_exp) and inst (r_exp)]
	return hyps

def split_loop_hyps (tags, split, restrs, exit):
	((r_split, _, _), _, _, n, _) = split
	(l_visit, _) = split_visit_visits (tags, split, restrs, vc_offs (n - 1))
	(l_cont, _) = split_visit_visits (tags, split, restrs, vc_offs (n))
	(l_tag, r_tag) = tags

	l_enter = pc_true_hyp (l_visit)
	l_exit = pc_false_hyp (l_cont)
	if exit:
		hyps = [l_enter, l_exit]
	else:
		hyps = [l_enter]
	return hyps + [hyp for offs in map (vc_offs, range (n))
		for (hyp, _) in split_hyps_at_visit (tags, split, restrs, offs)]

def loops_to_split (p, restrs):
	loop_heads_with_split = set ([p.loop_id (n)
		for (n, visit_set) in restrs])
	return list (set (p.loop_heads ()) - loop_heads_with_split)

def restr_others (p, restrs, n):
	extras = [(sp, vc_upto (n)) for sp in loops_to_split (p, restrs)]
	return restrs + tuple (extras)

def non_r_err_pc_hyp (tags, restrs):
	return pc_false_hyp ((('Err', restrs), tags[1]))

def split_r_err_pc_hyp (p, split, restrs, tags = None):
	(_, r_details, _, n, loop_r_max) = split
	(r_split, (r_seq_start, r_step), r_eqs) = r_details

	nc = n * r_step
	vc = vc_double_range (r_seq_start + nc, loop_r_max + 2)

	restrs = restr_others (p, ((r_split, vc), ) + restrs, 2)

	if tags == None:
		tags = p.pairing.tags

	return non_r_err_pc_hyp (tags, restrs)

restr_bump = 0

def get_proof_restr (n, (kind, (x, y))):
	return (n, mk_vc_opts ([VisitCount (kind, i)
		for i in range (x, y + restr_bump)]))

def restr_trivial_hyp (p, n, (kind, (x, y)), restrs):
	restr = (n, VisitCount (kind, y - 1))
	return rep_graph.pc_triv_hyp (((n, (restr, ) + restrs),
		p.node_tags[n][0]))

def proof_restr_checks (n, (kind, (x, y)), p, restrs, hyps):
	restr = get_proof_restr (n, (kind, (x, y)))
	ncerr_hyp = non_r_err_pc_hyp (p.pairing.tags,
		restr_others (p, (restr, ) + restrs, 2))
	hyps = [ncerr_hyp] + hyps
	def visit (vc):
		return ((n, ((n, vc), ) + restrs), p.node_tags[n][0])

	# this cannot be more uniform because the representation of visit
	# at offset 0 is all a bit odd, with n being the only node so visited:
	if kind == 'Offset':
		min_vc = vc_offs (max (0, x - 1))
	elif x > 1:
		min_vc = vc_num (x - 1)
	else:
		min_vc = None
	if min_vc:
		init_check = [(hyps, pc_true_hyp (visit (min_vc)),
			'Check of restr min %d %s for %d' % (x, kind, n))]
	else:
		init_check = []

	# if we can reach node n with (y - 1) visits to n, then the next
	# node will have y visits to n, which we are disallowing
	# thus we show that this visit is impossible
	top_vc = VisitCount (kind, y - 1)
	top_check = (hyps, pc_false_hyp (visit (top_vc)),
		'Check of restr max %d %s for %d' % (y, kind, n))
	return init_check + [top_check]

def split_init_step_checks (p, restrs, hyps, split):
	(_, _, _, n, _) = split
	tags = p.pairing.tags

	err_hyp = split_r_err_pc_hyp (p, split, restrs)
	hyps = [err_hyp] + hyps
	checks = []
	for i in range (n):
		(l_visit, r_visit) = split_visit_visits (tags, split,
			restrs, vc_num (i))
		lpc_hyp = pc_true_hyp (l_visit)
		# this trivial 'hyp' ensures the rep is built to include
		# the matching rhs visits when checking lhs consts
		rpc_triv_hyp = rep_graph.pc_triv_hyp (r_visit)
		vis_hyps = split_hyps_at_visit (tags, split, restrs, vc_num (i))

		for (hyp, desc) in vis_hyps:
			checks.append ((hyps + [lpc_hyp, rpc_triv_hyp], hyp,
				'Induct check at visit %d: %s' % (i, desc)))
	return checks

def split_induct_step_checks (p, restrs, hyps, split, tags = None):
	((l_split, _, _), _, _, n, _) = split
	if tags == None:
		tags = p.pairing.tags

	err_hyp = split_r_err_pc_hyp (p, split, restrs, tags = tags)
	(cont, r_cont) = split_visit_visits (tags, split, restrs, vc_offs (n))
	# the 'trivial' hyp here ensures the representation includes a loop
	# of the rhs when proving const equations on the lhs
	hyps = ([err_hyp, pc_true_hyp (cont),
			rep_graph.pc_triv_hyp (r_cont)] + hyps
		+ split_loop_hyps (tags, split, restrs, exit = False))

	return [(hyps, hyp, 'Induct check (%s) at inductive step for %d'
			% (desc, l_split))
		for (hyp, desc) in split_hyps_at_visit (tags, split,
			restrs, vc_offs (n))]

def check_split_induct_step_group (rep, restrs, hyps, split, tags = None):
	checks = split_induct_step_checks (rep.p, restrs, hyps, split,
		tags = tags)
	groups = proof_check_groups (checks)
	for group in groups:
		if not test_hyp_group (rep, group):
			return False
	return True

def split_checks (p, restrs, hyps, split):
	return (split_init_step_checks (p, restrs, hyps, split)
		+ split_induct_step_checks (p, restrs, hyps, split))

def leaf_condition_checks (p, restrs, hyps):
	'''checks of the final refinement conditions'''
	nrerr_pc_hyp = non_r_err_pc_hyp (p.pairing.tags, restrs)
	hyps = [nrerr_pc_hyp] + hyps
	[l_tag, r_tag] = p.pairing.tags

	nlerr_pc = pc_false_hyp ((('Err', restrs), l_tag))
	# this 'hypothesis' ensures that the representation is built all
	# the way to Ret. in particular this ensures that function relations
	# are available to use in proving single-side equalities
	ret_eq = eq_hyp ((true_term, (('Ret', restrs), l_tag)),
		(true_term, (('Ret', restrs), r_tag)))

	### TODO: previously we considered the case where 'Ret' was unreachable
	### (as a result of unsatisfiable hyps) and proved a simpler property.
	### we might want to restore this
	(_, out_eqs) = p.pairing.eqs
	checks = [(hyps + [nlerr_pc, ret_eq], hyp, 'Leaf eq check') for hyp in
		inst_eqs (p, restrs, out_eqs)]
	return [(hyps + [ret_eq], nlerr_pc, 'Leaf path-cond imp')] + checks

def proof_checks (p, proof):
	return proof_checks_rec (p, (), init_point_hyps (p), proof, 'root')

def proof_checks_rec (p, restrs, hyps, proof, path):
	if proof.kind == 'Restr':
		checks = proof_restr_checks (proof.point, proof.restr_range,
			p, restrs, hyps)
	elif proof.kind == 'Split':
		checks = split_checks (p, restrs, hyps, proof.split)
	elif proof.kind == 'Leaf':
		checks = leaf_condition_checks (p, restrs, hyps)
	elif proof.kind == 'CaseSplit':
		checks = []

	checks = [(hs, hyp, '%s on %s' % (name, path))
		for (hs, hyp, name) in checks]

	subproblems = proof_subproblems (p, proof.kind,
		proof.args, restrs, hyps, path)
	for (subprob, subproof) in logic.azip (subproblems, proof.subproofs):
		(restrs, hyps, path) = subprob
		checks.extend (proof_checks_rec (p, restrs, hyps, subproof, path))
	return checks

last_failed_check = [None]

def proof_check_groups (checks):
	groups = {}
	for (hyps, hyp, name) in checks:
		n_vcs = set ([n_vc for hyp2 in [hyp] + hyps
			for n_vc in hyp2.visits ()])
		k = (tuple (sorted (list (n_vcs))))
		groups.setdefault (k, []).append ((hyps, hyp, name))
	return groups.values ()

def test_hyp_group (rep, group):
	imps = [(hyps, hyp) for (hyps, hyp, _) in group]
	names = set ([name for (_, _, name) in group])

	trace ('Testing group of hyps: %s' % list (names), push = 1)
	res = rep.test_hyp_imps (imps)
	trace ('Group result: %r' % res, push = -1)
	return res

def find_failed_test (rep, group):
	trace ('Finding failed test from hyp group.', push = 1)
	while len (group) > 1:
		split = len (group) / 2
		if test_hyp_group (rep, group[:split]):
			group = group[split:]
		else:
			group = group[:split]
	[(hyps, hyp, name)] = group
	if rep.test_hyp_imp (hyps, hyp):
		trace ('Group failure spurious! (%s)' % name, push = -1)
		return None
	else:
		trace ('Found failed test in group: %s' % name, push = -1)
		return (hyps, hyp, name)

def failed_test_sets (p, checks):
	failed = []
	sets = {}
	for (hyps, hyp, name) in checks:
		sets.setdefault (name, [])
		sets[name].append ((hyps, hyp))
	for name in sets:
		rep = rep_graph.mk_graph_slice (p)
		if not rep.test_hyp_imps (sets[name]):
			failed.append (name)
	return failed

save_checked_proofs = [None]

def check_proof (p, proof, use_rep = None):
	checks = proof_checks (p, proof)
	groups = proof_check_groups (checks)

	for group in groups:
		if use_rep == None:
			rep = rep_graph.mk_graph_slice (p)
		else:
			rep = use_rep

		res = test_hyp_group (rep, group)
		if res:
			continue
		failed = find_failed_test (rep, group)
		if failed:
			# hypothetically the checks might pass one at a time
			# having failed together for some performance reason
			last_failed_check[0] = failed
			(hyps, hyp, name) = failed
			trace ('%s: proof failed!' % name)
			return False
	if save_checked_proofs[0]:
		save = save_checked_proofs[0]
		save (p, proof)
	return True

def pretty_vseq ((split, (seq_start, seq_step), _)):
	if (seq_start, seq_step) == (0, 1):
		return 'visits to %d' % split
	else:
		i = seq_start + 1
		j = i + seq_step
		k = j + seq_step
		return 'visits [%d, %d, %d ...] to %d' % (i, j, k, split)

def next_induct_var (n):
	s = 'ijkabc'
	v = s[n % 6]
	if n >= 6:
		v += str ((n / 6) + 1)
	return v

def pretty_lambda (t):
	v = syntax.mk_var ('#seq-visits', word32T)
	t = logic.var_subst (t, {('%i', word32T) : v}, must_subst = False)
	return syntax.pretty_expr (t, print_type = True)

def check_proof_report_rec (p, restrs, hyps, proof, step_num, ctxt, inducts):
	import sys
	printout ('Step %d: %s' % (step_num, ctxt))
	if proof.kind == 'Restr':
		(kind, (x, y)) = proof.restr_range
		if kind == 'Offset':
			v = inducts[1][proof.point]
			rexpr = '{%s + %s ..< %s + %s}' % (v, x, v, y)
		else:
			rexpr = '{%s ..< %s}' % (x, y)
		printout ('  Prove the number of visits to %d is in %s'
			% (proof.point, rexpr))
		
		checks = proof_restr_checks (proof.point, proof.restr_range,
			p, restrs, hyps)
		cases = ['']
	elif proof.kind == 'Split':
		(l_dts, r_dts, eqs, n, lrmx) = proof.split
		v = next_induct_var (inducts[0])
		inducts = (inducts[0] + 1, dict (inducts[1]))
		inducts[1][l_dts[0]] = v
		inducts[1][r_dts[0]] = v
		printout ('  prove %s related to %s' % (pretty_vseq (l_dts),
			pretty_vseq (r_dts)))
		printout ('    with equalities')
		for (x, y) in eqs:
			printout ('      %s (@ addr %s)' % (pretty_lambda (x),
				l_dts[0]))
			printout ('      = %s (@ addr %s)' % (pretty_lambda (y),
				r_dts[0]))
		printout ('    and with invariants')
		for x in l_dts[2]:
			printout ('      %s (@ addr %s)'
				% (pretty_lambda (x), l_dts[0]))
		for x in r_dts[2]:
			printout ('      %s (@ addr %s)'
				% (pretty_lambda (x), r_dts[0]))
		checks = split_checks (p, restrs, hyps, proof.split)
		cases = ['case in (%d) where the length of the sequence < %d'
				% (step_num, n),
			'case in (%d) where the length of the sequence is %s + %s'
				% (step_num, v, n)]
	elif proof.kind == 'Leaf':
		printout ('  prove all verification conditions')
		checks = leaf_condition_checks (p, restrs, hyps)
		cases = []
	elif proof.kind == 'CaseSplit':
		printout ('  case split on whether %d is visited' % proof.point)
		checks = []
		cases = ['case in (%d) where %d is visited' % (step_num, proof.point),
			'case in (%d) where %d is not visited' % (step_num, proof.point)]

	if checks:
		groups = proof_check_groups (checks)
		for group in groups:
			rep = rep_graph.mk_graph_slice (p)
			res = test_hyp_group (rep, group)
			if not res:
				printout ('    .. failed to prove this.')
				sys.stdout.flush ()
				return

		printout ('    .. proven.')
		sys.stdout.flush ()

	subproblems = proof_subproblems (p, proof.kind,
		proof.args, restrs, hyps, '')
	xs = logic.azip (subproblems, proof.subproofs)
	xs = logic.azip (xs, cases)
	step_num += 1
	for ((subprob, subproof), case) in xs:
		(restrs, hyps, _) = subprob
		res = check_proof_report_rec (p, restrs, hyps, subproof,
			step_num, case, inducts)
		if not res:
			return
		(step_num, induct_var_num) = res
		inducts = (induct_var_num, inducts[1])
	return (step_num, inducts[0])

def check_proof_report (p, proof):
	res = check_proof_report_rec (p, (), init_point_hyps (p), proof,
		1, '', (0, {}))
	return bool (res)

def save_proofs_to_file (fname, mode = 'w'):
	assert mode in ['w', 'a']
	f = open (fname, mode)

	def save (p, proof):
		f.write ('ProblemProof (%s) {\n' % p.name)
		for s in p.serialise ():
			f.write (s + '\n')
		ss = []
		proof.serialise (p, ss)
		f.write (' '.join (ss))
		f.write ('\n}\n')
		f.flush ()
	return save

def load_proofs_from_file (fname):
	f = open (fname)

	proofs = {}
	lines = None
	for line in f:
		line = line.strip ()
		if line.startswith ('ProblemProof'):
			assert line.endswith ('{'), line
			name_bit = line[len ('ProblemProof') : -1].strip ()
			assert name_bit.startswith ('('), name_bit
			assert name_bit.endswith (')'), name_bit
			name = name_bit[1:-1]
			lines = []
		elif line == '}':
			assert lines[0] == 'Problem'
			assert lines[-2] == 'EndProblem'
			import problem
			trace ('loading proof from %d lines' % len (lines))
			p = problem.deserialise (name, lines[:-1])
			proof = deserialise (lines[-1])
			proofs.setdefault (name, [])
			proofs[name].append ((p, proof))
			trace ('loaded proof %s' % name)
			lines = None
		elif line.startswith ('#'):
			pass
		elif line:
			lines.append (line)
	assert not lines
	return proofs

