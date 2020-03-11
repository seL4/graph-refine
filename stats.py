#
# Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

# various attempts at gathering statistics

from syntax import Expr, Type
from rep_graph import vc_options
from check import ProofNode

from target_objects import pairings
import check
import search
import logic
import rep_graph

def scan_proofs (res_f):
	nm = None
	proofs = {}
	pairings_set = set ([p for f in pairings for p in pairings[f]])
	pairings_names = dict ([(pair.name, pair) for pair in pairings_set])
	for line in res_f:
		if line.startswith ('Testing Function'):
			(_, nm) = line.split (' pair ', 1)
			nm = nm.strip ()
			pair = pairings_names[nm]
		if line.startswith ('ProofNode '):
			pn = eval (line)
			proofs[pair] = pn
	res_f.close ()
	return proofs

def all_problems (proofs, filt = None):
	problems = []
	for (pair, proof) in proofs.iteritems ():
		if filt != None:
			if not [pn for pn in proof.all_subproofs ()
					if filt (pn)]:
				continue
		p = check.build_problem (pair)
		probs = proof.all_subproblems (p, (),
			check.init_point_hyps (p), 'problem')
		problems.extend ([(p, pn, restrs, hyps)
			for (pn, restrs, hyps) in probs
			if filt == None or filt (pn)])
	return problems

def filter_split_problems (problems):
	return [(p, proofnode, restrs, hyps)
		for (p, proofnode, restrs, hyps) in problems
		if proofnode.kind == 'Split']

def scan_split_problems (fname):
	proofs = scan_proofs (open (fname))
	problems = all_problems (proofs, filt = lambda pn: pn.kind == 'Split')
	return problems

def split_metrics (proofnode):
	(l_start, l_step) = proofnode.split[0][1]
	(r_start, r_step) = proofnode.split[1][1]
	l_side = l_start + (l_step * 2) + 1
	r_side = r_start + (r_step * 2) + 1
	return (max (l_side, r_side), (l_start, l_step), (r_start, r_step))

def has_linear_split ((info, p, pn, restrs, hyps)):
	loop_head = pn.split[0][0]
	nec = search.get_necessary_split_opts (p, loop_head,
		restrs, hyps)
	return nec != None

def problems_with_linear_splits (split_problems):
	probs = sorted ([(split_metrics (pn), p, pn, restrs, hyps)
		for (p, pn, restrs, hyps) in split_problems])
	data = []
	for (i, (info, p, pn, restrs, hyps)) in enumerate (probs):
		print 'Handling loop %d in %s' % (i, p.name)
		h = has_linear_split ((info, p, pn, restrs, hyps))
		data.append ((info, pn, h))
	return data

def tabulate_problems_with_linear_splits (data):
	rows = {}
	for (_, pn, has_nec) in data:
		wsz = split_metrics (pn)[0]
		rows.setdefault (wsz, [])
		rows[wsz].append (has_nec)
	print 'Breakdown of presence of necessary splits:'
	for i in sorted (rows):
		print 'Window size %d:' % i
		tr = len ([v for v in rows[i] if v])
		ln = len (rows[i])
		print '  %d / %d (%0.1f%s)' % (tr, ln, (tr * 100.0) / ln, '%')

def problem_var_analysis_nonempty ((p, pn, restrs, hyps)):
	loop_head = pn.split[0][0]
	va = search.get_loop_var_analysis_at (p, loop_head)
	return bool ([v for (v, data) in va if data == 'LoopVariable'])

def example_problems (split_problems, num):
	probs = filter (problem_var_analysis_nonempty, split_problems)
	probs = sorted ([(split_metrics (pn), p, pn, restrs, hyps)
                for (p, pn, restrs, hyps) in probs])
	prob_idxs = sorted (set ([int ((i * (len (probs) - 1)) * 1.0 / num)
		for i in range (num)]))
	return [probs[i] for i in prob_idxs]

def big_example_problem (split_problems):
	probs = filter (problem_var_analysis_nonempty, split_problems)
	probs = sorted ([(split_metrics (pn), p, pn, restrs, hyps)
		for (p, pn, restrs, hyps) in split_problems])
	probs.reverse ()
	probs_with_lin = (prob for prob in probs
		if has_linear_split (prob))
	return probs_with_lin.next ()

def trace_split_loop_pairs_window (problem, window_size):
	(_, p, pn, restrs, hyps) = problem
	loop_head = pn.split[0][0]
	if ('v_eqs', loop_head) in p.cached_analysis:
		del p.cached_analysis[('v_eqs', loop_head)]

	rep = rep_graph.mk_graph_slice (p, fast = True)
	i_j_opts = search.mk_i_j_opts (unfold_limit = window_size)
	(i_opts, j_opts) = i_j_opts[-1]
	knowledge = search.setup_split_search (rep, loop_head, restrs, hyps,
                i_opts, j_opts, unfold_limit = window_size)

	res = search.split_search (loop_head, knowledge)
	trace = list (knowledge.live_pairs_trace)
	return (res, trace)

def tabulate_example_traces (split_problems, data):
	probs = example_problems (split_problems, 16)
	ex_traces = [(prob[0][0] + 1,
			trace_split_loop_pairs_window (prob, prob[0][0] + 1))
		for prob in probs]

	prob = big_example_problem (split_problems)
	big_traces = []
	for i in range (prob[0][0] + 2):
		if not search.mk_i_j_opts (unfold_limit = i):
			continue
		(_, trace) = trace_split_loop_pairs_window (prob, i)
		big_traces.append ((i, trace))

	print 'Search pair decay in random examples (idx, window size, trace):'
	for (i, (w, (_, trace))) in enumerate (ex_traces):
		print '  %d: %d: %s' % (i, w, trace)

	print 'Search pair decay in large problem, window sizes:'
	for (w, trace) in big_traces:
		print '  %d: %s' % (w, trace)

	print 'Example again in gnuplot-happy format:'
	for (w, (_, trace)) in ex_traces:
		print
		print
		for v in trace:
			print v

	print 'Large example again:'
	for (w, trace) in big_traces:
		print
		print
		for v in trace:
			print v

def scan_times (res_f):
	nm = None
	times = {}
	pairings_set = set ([p for f in pairings for p in pairings[f]])
	pairings_names = dict ([(pair.name, pair) for pair in pairings_set])
	for line in res_f:
		if line.startswith ('Testing Function'):
			(_, nm) = line.split (' pair ', 1)
			nm = nm.strip ()
			pair = pairings_names[nm]
		if line.startswith ('Result ') and 'time taken:' in line:
			(_, time) = line.split ('time taken:', 1)
			time = time.strip ()
			assert time[-1] == 's'
			time = float (time[:-1])
			times[pair] = time
	res_f.close ()
	return times

def problem_difficult_estimate (p):
	return (len (p.nodes), len (p.loop_heads ()),
		len ([n for n in p.nodes if p.loop_id (n)]))

def tabulate_timing_estimates (problems, proofs, times):
	pair_probs = {}
	for (p, _, _, _) in problems:
		pair_probs[p.pairing] = p
	print
	print 'Timing estimate info: (nodes, loops, loop nodes, proof nodes, time)'
	for pair in pair_probs:
		time = times[pair]
		p = pair_probs[pair]
		print '  %d %d %d %d %0.2f' % (problem_difficult_estimate (p)
			+ (len (proofs[pair].all_subproofs ()), )
			+ (time, ))

def print_total_time (times):
	time_vals = sorted (times.values ())
	import datetime
	def strs (seconds):
		return (seconds, str (datetime.timedelta (seconds = int (seconds))))
	print 'Slowest problem: %ss (%s)' % strs (time_vals[-1])
	print 'Total time: %ss (%s)' % strs (sum (time_vals))

def do_all (fname):
	proofs = scan_proofs (open (fname))
	problems = all_problems (proofs)
	times = scan_times (open (fname))

	split_problems = filter_split_problems (problems)
	data = problems_with_linear_splits (split_problems)

	tabulate_example_traces (split_problems, data)
	tabulate_problems_with_linear_splits (data)

	print_total_time (times)

	tabulate_timing_estimates (problems, proofs, times)


