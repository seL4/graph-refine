# * Copyright 2015, NICTA
# *
# * This software may be distributed and modified according to the terms of
# * the BSD 2-Clause license. Note that NO WARRANTY is provided.
# * See "LICENSE_BSD2.txt" for details.
# *
# * @TAG(NICTA_BSD)


import search
from check import split_visit_one_visit
import check
from rep_graph import vc_num, vc_offs, pc_true_hyp, Hyp, eq_hyp
import logic
import rep_graph



def linear_eq_hyps_at_visit (tag, split, eqs, restrs, visit_num):
	details = (split, (0, 1), eqs)
	visit = split_visit_one_visit (tag, details, restrs, visit_num)
	start = split_visit_one_visit (tag, details, restrs, vc_num (0))
	from syntax import mk_word32, mk_plus, mk_var, word32T

	def mksub (v):
		return lambda exp: logic.var_subst (exp, {('%i', word32T) : v},
			must_subst = False)
	zsub = mksub (mk_word32 (0))
	if visit_num.kind == 'Number':
		isub = mksub (mk_word32 (visit_num.n))
	else:
		isub = mksub (mk_plus (mk_var ('%n', word32T),
			mk_word32 (visit_num.n)))

	hyps = [(Hyp ('PCImp', visit, start), '%s pc imp' % tag)]
	hyps += [(eq_hyp ((isub (exp), visit), (zsub (exp), start),
				(split, 0)), '%s const' % tag)
			for exp in eqs]

	return hyps

def linear_eq_induct_base_checks (p, restrs, hyps, tag, split, eqs):
	tests = []
	details = (split, (0, 1), eqs)
	for i in [0, 1]:
		reach = split_visit_one_visit (tag, details, restrs, vc_num (i))
		nhyps = [pc_true_hyp (reach)]
		tests.extend ([(hyps + nhyps, hyp,
			'Base check (%s, %d) at induct step for %d' % (desc,
				i, split)) for (hyp, desc) in
			linear_eq_hyps_at_visit (tag, split, eqs,
				restrs, vc_num (i))])
	return tests

def linear_eq_induct_step_checks (p, restrs, hyps, tag, split, eqs):
	details = (split, (0, 1), eqs)
	cont = split_visit_one_visit (tag, details, restrs, vc_offs (1))
	# the 'trivial' hyp here ensures the representation includes a loop
	# of the rhs when proving const equations on the lhs
	hyps = ([pc_true_hyp (cont)] + hyps
		+ [h for (h, _) in linear_eq_hyps_at_visit (tag, split,
			eqs, restrs, vc_offs (0))])

	return [(hyps, hyp, 'Induct check (%s) at inductive step for %d'
			% (desc, split))
		for (hyp, desc) in linear_eq_hyps_at_visit (tag, split, eqs,
			restrs, vc_offs (1))]

def get_linear_series_hyps (p, split):
	eqs = search.mk_seq_eqs (p, split, 1, with_rodata = False)
	(tag, _) = p.node_tags[split]
	
	checks = (linear_eq_induct_step_checks (p, (), [], tag, split, eqs)
		+ linear_eq_induct_base_checks (p, (), [], tag, split, eqs))

	rep = rep_graph.mk_graph_slice (p)
	groups = check.proof_check_groups (checks)
	for group in groups:
		if not check.test_hyp_group (rep, group):
			return False
	
	hyps = [h for (h, _) in linear_eq_hyps_at_visit (tag, split,
			eqs, (), vc_offs (0))]
	return hyps

def get_induct_eq_hyp (p, split, restrs, n):
	details = (split, (0, 1), [])
	(tag, _) = p.node_tags[split]
	visit = split_visit_one_visit (tag, details, restrs, vc_offs (0))
	from syntax import mk_var, word32T, mk_word32
	return eq_hyp ((mk_var ('%n', word32T), visit),
		(mk_word32 (n), visit), (split, 0))

def example ():
	"""works with new-gcc-O2 maybe"""
	from target_objects import functions
	import problem
	import syntax
	p = functions['Arch_createObject'].as_problem(problem.Problem)
	p.do_analysis ()
	split = 4026613876
	# prove linear series (r3 ~= i * 8) and get hyps
	# this is a series of visits to 'split' numbered by i
	hyps = get_linear_series_hyps (p, split)

	# assume i = 510
	hyp = get_induct_eq_hyp (p, split, (), 510)

	rep = rep_graph.mk_graph_slice (p)

	# consider pc of visit i + 2 (i.e. 512)
	continue_to_512 = rep.get_pc ((split, ((split, vc_offs (2)),)))
	# test whether this is impossible
	rep.test_hyp_whyps (syntax.mk_not (continue_to_512), [hyp] + hyps)


