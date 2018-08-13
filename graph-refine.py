# * Copyright 2015, NICTA
# *
# * This software may be distributed and modified according to the terms of
# * the BSD 2-Clause license. Note that NO WARRANTY is provided.
# * See "LICENSE_BSD2.txt" for details.
# *
# * @TAG(NICTA_BSD)

# toplevel graph-refine script
# usage: python graph-refine.py <target> <proofs>

import syntax
import pseudo_compile
import solver
import rep_graph
import problem
import check
import search
from target_objects import pairings, functions
from target_objects import trace, tracer, printout
import target_objects

import re
import random
import traceback
import time
#import diagnostic

import sys

if __name__ == '__main__':
	args = target_objects.load_target_args ()

def toplevel_check (pair, check_loops = True, report = False, count = None,
		only_build_problem = False):
	if not only_build_problem:
		printout ('Testing Function pair %s' % pair)
	if count and not only_build_problem:
		(i, n) = count
		printout ('  (function pairing %d of %d)' % (i + 1, n))
	
	for (tag, fname) in pair.funs.iteritems ():
		if not functions[fname].entry:
			printout ('Skipping %s, underspecified %s' % (pair, tag))
			return 'None'
	prev_tracer = tracer[0]
	if report:
		tracer[0] = lambda s, n: ()

	exception = None

	trace (time.asctime ())
	start_time = time.time()
	sys.stdout.flush ()
	try:
		p = check.build_problem (pair)
		if only_build_problem:
			tracer[0] = prev_tracer
			return 'True'
		if report:
			printout (' .. built problem, finding proof')
		if not check_loops and p.loop_data:
			printout ('Problem has loop!')
			tracer[0] = prev_tracer
			return 'Loop'
		if check_loops == 'only' and not p.loop_data:
			printout ('No loop in problem.')
			tracer[0] = prev_tracer
			return 'NoLoop'
		proof = search.build_proof (p)
		if report:
			printout (' .. proof found.')

		try:
			if report:
				result = check.check_proof_report (p, proof)
			else:
				result = check.check_proof (p, proof)
				if result:
					printout ('Refinement proven.')
				else:
					printout ('Refinement NOT proven.')
		except solver.SolverFailure, e:
			printout ('Solver timeout/failure in proof check.')
			result = 'CheckSolverFailure'
		except Exception, e:
			trace ('EXCEPTION in checking %s:' % p.name)
			exception = sys.exc_info ()
			result = 'CheckEXCEPT'

	except problem.Abort:
		result = 'ProofAbort'
	except search.NoSplit:
		result = 'ProofNoSplit'
	except solver.SolverFailure, e:
		printout ('Solver timeout/failure in proof search.')
		result = 'ProofSolverFailure'

	except Exception, e:
		trace ('EXCEPTION in handling %s:' % pair)
		exception = sys.exc_info ()
		result = 'ProofEXCEPT'

	end_time = time.time ()
	tracer[0] = prev_tracer
	if exception:
		(etype, evalue, tb) = exception
		traceback.print_exception (etype, evalue, tb,
			file = sys.stdout)

	if not only_build_problem:
		printout ('Result %s for pair %s, time taken: %.2fs'
			% (result, pair, end_time - start_time))
		sys.stdout.flush ()

	return str (result)

def toplevel_check_wname (pair, check_loops = True,
		report_mode = False, count = None,
		only_build_problem = False):
	r = toplevel_check (pair, count = count, report = report_mode,
		check_loops = check_loops,
		only_build_problem = only_build_problem)
	return (pair.name, r)

word_re = re.compile('\\w+')

def name_search (s, tags = None):
	pairs = list (set ([pair for f in pairings for pair in pairings[f]
		if s in pair.name
		if not tags or tags.issubset (set (pair.tags))]))
	if len (pairs) == 1:
		return pairs[0]
	word_pairs = [p for p in pairs if s in word_re.findall (str (p))]
	if len (word_pairs) == 1:
		return word_pairs[0]
	print 'Possibilities for %r: %s' % (s, [str (p) for p in pairs])
	return None

def check_search (s, tags = None, report_mode = False,
		check_loops = True):
	pair = name_search (s, tags = tags)
	if not pair:
		return 'None'
	else:
		return toplevel_check (pair, report = report_mode,
			check_loops = check_loops)

def problem_search (s):
	pair = name_search (s)
	print pair.name
	return check.build_problem (pair)

# somewhat arbitrary assignment of return codes to outcomes.
# larger numbers are (roughly) worse outcomes.
result_nums = {
	'True' : 0,
	'Loop' : 1,
	'NoLoop' : 2,
	'None' : 3,
	'False': 4,
	'ProofAbort' : 5,
	'ProofNoSplit' : 6,
	'ProofSolverFailure' : 7,
	'ProofEXCEPT' : 8,
	'CheckSolverFailure' : 9,
	'CheckEXCEPT' : 10,
}

def comb_results (r1, r2):
	(_, r) = max ([(result_nums[r], r) for r in [r1, r2]])
	return r

def check_pairs (pairs, loops = True, report_mode = False,
		only_build_problem = False):
	num_pairs = len (pairs)
	printout ('Checking %d function pair problems' % len (pairs))
	results = [toplevel_check_wname (pair, check_loops = loops,
			report_mode = report_mode, count = (i, num_pairs),
			only_build_problem = only_build_problem)
		for (i, pair) in enumerate (pairs)]
	if not only_build_problem:
		printout ('Results: %s' % results)
	printout ('Result summary:')
	count = len ([1 for (_, r) in results if r == 'True'])
	if only_build_problem:
		printout ('  - %d problems build' % count)
	else:
		printout ('  - %d proofs checked' % count)
	skipped = [nm for (nm, r) in results
		if r in ['ProofAbort', 'None']]
	printout ('  - %d proofs skipped' % len (skipped))
	fails = [(nm, r) for (nm, r) in results
		if r not in ['True', 'ProofAbort', 'None']]
	print_coverage_report (set (skipped))
	printout ('  - failures: %s' % fails)
	return syntax.foldr1 (comb_results, ['True']
		+ [r for (nm, r) in results])

def print_coverage_report (skipped_pairs):
	try:
		from trace_refute import addrs_covered, funs_sort_by_num_addrs
		covered = lambda f: all ([pair.name not in skipped_pairs
			for pair in pairings[f]])
		covered_fs = set (filter (covered, pairings))
		coverage = addrs_covered (covered_fs)
		printout ('  - %.2f%% instructions covered' % (coverage * 100))
		fs = funs_sort_by_num_addrs (set (pairings) - covered_fs)
		if not fs:
			return
		lrg_msgs = ['%s (%.2f%%)' % (f, addrs_covered ([f]) * 100)
			for f in reversed (fs[-3:])]
		printout ('  - largest skipped functions:')
		printout ('      %s' % ', '.join (lrg_msgs))
	except Exception, e:
		pass

def check_all (omit_set = set (), loops = True, tags = None,
		report_mode = False, only_build_problem = False):
	pairs = list (set ([pair for f in pairings for pair in pairings[f]
		if omit_set.isdisjoint (pair.funs.values ())
		if not tags or tags.issubset (set (pair.tags))]))
	omitted = list (set ([pair for f in pairings for pair in pairings[f]
		if not omit_set.isdisjoint (pair.funs.values())]))
	random.shuffle (pairs)
	r = check_pairs (pairs, loops = loops, report_mode = report_mode,
		only_build_problem = only_build_problem)
	if omitted:
		printout ('  - %d pairings omitted: %s'
			% (len (omitted), [pair.name for pair in omitted]))
	return r

def check_division_pairs (num, denom, loops = True, report_mode = False):
	pairs = list (set ([pair for f in pairings for pair in pairings[f]]))
	def pair_size (pair):
		return (len (functions[pair.l_f].nodes)
			+ len (functions[pair.r_f].nodes))
	pairs = sorted ([(pair_size (pair), pair) for pair in pairs])
	division = [pairs[i][1] for i in range (num, len (pairs), denom)]
	return check_pairs (division, loops = loops, report_mode = report_mode)

def check_deps (fname, report_mode = False):
	frontier = set ([fname])
	funs = set ()
	while frontier:
		fname = frontier.pop ()
		if fname in funs:
			continue
		funs.add (fname)
		frontier.update (functions[fname].function_calls ())
	funs = sorted (funs)
	funs = [fun for fun in funs if fun in pairings]
	printout ('Testing functions: %s' % funs)
	pairs = [pair for f in funs for pair in pairings[f]]
	return check_pairs (pairs, report_mode = report_mode)

def save_compiled_funcs (fname):
	out = open (fname, 'w')
	for (f, func) in functions.iteritems ():
		trace ('Saving %s' % f)
		for s in func.serialise ():
			out.write (s + '\n')
	out.close ()

def rerun_set (vs):
	def get_strs (vs):
		return [v for v in vs if type (v) == str] + [v2
			for v in vs if type (v) != str for v2 in get_strs (v)]
	vs = set (get_strs (vs))
	pairs = map (name_search, vs)
	strs = [pair.funs[pair.tags[0]] for pair in pairs if pair]
	return ' '.join (strs)

def main (args):
	excluding = False
	excludes = set ()
	loops = True
	tags = set ()
	report = True
	result = 'True'
	pairs_to_check = []
	for arg in args:
		r = 'True'
		try:
			if arg == 'verbose':
				report = False
			elif arg.startswith ('trace-to:'):
				(_, s) = arg.split (':', 1)
				f = open (s, 'w')
				target_objects.trace_files.append (f)
			elif arg == 'all':
				r = check_all (excludes, loops = loops,
					tags = tags, report_mode = report)
			elif arg == 'all_safe':
				ex = set.union (excludes,
					target_objects.danger_set)
				r = check_all (ex, loops = loops,
					tags = tags, report_mode = report)
			elif arg == 'coverage':
				r = check_all (excludes, loops = loops,
					tags = tags, report_mode = report,
					only_build_problem = True)
			elif arg.startswith ('div:'):
				[_, num, denom] = arg.split (':')
				num = int (num)
				denom = int (denom)
				r = check_division_pairs (num, denom,
					loops = loops, report_mode = report)
			elif arg == 'no_loops':
				loops = False
			elif arg == 'only_loops':
				loops = 'only'
			elif arg.startswith('save:'):
				save_compiled_funcs (arg[5:])
			elif arg.startswith('save-proofs:'):
				fname = arg[len ('save-proofs:') :]
				save = check.save_proofs_to_file (fname, 'a')
				check.save_checked_proofs[0] = save
			elif arg == '-exclude':
				excluding = True
			elif arg == '-end-exclude':
				excluding = False
			elif arg.startswith ('t:'):
				tags.add (arg[2:])
			elif arg.startswith ('target:'):
				pass
			elif arg.startswith ('skip-proofs-of:'):
				(_, fname) = arg.split(':', 1)
				import stats
				prev_proofs = stats.scan_proofs (open (fname))
				prev_fs = [f for pair in prev_proofs
					for f in pair.funs.values ()]
				excludes.update (prev_fs)
			elif excluding:
				excludes.add (arg)
			elif arg.startswith ('deps:'):
				r = check_deps (arg[5:],
					report_mode = report)
			else:
				r = name_search (arg, tags = tags)
				if r != None:
					pairs_to_check.append (r)
					r = 'True'
				else:
					r = 'None'
		except Exception, e:
			print 'EXCEPTION in syscall arg %s:' % arg
			print traceback.format_exc ()
			r = 'ProofEXCEPT'
		result = comb_results (r, result)
	if pairs_to_check:
		r = check_pairs (pairs_to_check, loops = loops,
			report_mode = report)
		result = comb_results (r, result)
	return result

if __name__ == '__main__':
	result = main (args)
	if result in ['True', 'Loop', 'NoLoop', 'None']:
		sys.exit (0)
	sys.exit (result_nums[result])

