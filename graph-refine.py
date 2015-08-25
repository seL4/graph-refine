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

if len(sys.argv) > 1:
	target = '%s/target.py' % sys.argv[1]
	target_objects.target_dir.set_dir(sys.argv[1])
	target_objects.target_args.extend([arg[7:] for arg in sys.argv
		if arg.startswith('target:')])
	execfile (target, {})
else:
	print 'Usage: python graph-refine <target> <instructions>'
	print 'Target should be a directory.'
	print 'See example target (named "example") for information on targets.'
	print "See graph-refine.py source for possible instructions."

def toplevel_check (pair, quiet, check_loops = True):
	printout ('Testing Function pair %s' % pair)
	
	for (tag, fname) in pair.funs.iteritems ():
		if not functions[fname].entry:
			printout ('Skipping %s, underspecified %s' % (pair, tag))
			return None
	if quiet:
		the_trace = []
		def new_tracer (s, v):
			the_trace.append (s)
		tracer[0] = new_tracer

	exception = None

	trace (time.asctime ())
	start_time = time.time()
	sys.stdout.flush ()
	try:
		p = check.build_problem (pair)
		if not check_loops and p.loop_data:
			trace ('Problem has loop!')
			return 'Loop'
		if check_loops == 'only' and not p.loop_data:
			return 'NoLoop'
		proof = search.build_proof (p)

		try:
			result = check.check_proof (p, proof)
		except Exception, e:
			trace ('EXCEPTION in checking %s:' % p.name)
			exception = sys.exc_info ()
			result = 'CheckEXCEPT'

	except problem.Abort:
		result = 'ProofAbort'
	except search.NoSplit:
		result = 'ProofNoSplit'

	except Exception, e:
		trace ('EXCEPTION in handling %s:' % pair)
		exception = sys.exc_info ()
		result = 'ProofEXCEPT'

	end_time = time.time ()
	if quiet:
		if result != True:
			printout ('Trace of failed toplevel check follows:')
			for s in the_trace:
				printout (s)
			tracer[0] = target_objects.default_tracer
	if exception:
		(etype, evalue, tb) = exception
		traceback.print_exception (etype, evalue, tb)

	printout ('Time taken to check %s for pair %s: %f' % (result, pair,
		end_time - start_time))
	sys.stdout.flush ()

	return str (result)

def toplevel_check_report (pair):
	arrer = '%s -> %s' % tuple ([pair.funs[t] for t in pair.tags])
	for (tag, fname) in pair.funs.iteritems ():
		if not functions[fname].entry:
			printout ('Skipping %s, underspecified %s' % (arrer, tag))
	tracer[0] = lambda x, y: ()

	try:
		printout ('Proofs for %s' % arrer)
		p = check.build_problem (pair)
		printout (' .. built problem, finding proof')
		proof = search.build_proof (p)
		printout (' .. proof found.')
		result = check.check_proof_report (p, proof)
		printout ('Refinement %s proven.' % arrer)

	except problem.Abort:
		printout ('Skipping %s, proof attempt aborted' % pair)
	except search.NoSplit:
		printout ('Could not find split for %s' % pair)

def toplevel_check_wname (pair, quiet = False, check_loops = True,
		report_mode = False):
	if report_mode:
		toplevel_check_report (pair)
	else:
		r = toplevel_check (pair, quiet, check_loops = check_loops)
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

def check_search (s, quiet = False, tags = None, report_mode = False,
		check_loops = True):
	pair = name_search (s, tags = tags)
	if pair:
		return toplevel_check_wname (pair, quiet,
			report_mode = report_mode,
			check_loops = check_loops)

def check_all (omit_set = set (), quiet = False, loops = True, tags = None,
		report_mode = False):
	pairs = list (set ([pair for f in pairings for pair in pairings[f]
		if omit_set.isdisjoint (pair.funs.values ())
		if not tags or tags.issubset (set (pair.tags))]))
	omitted = list (set ([pair for f in pairings for pair in pairings[f]
		if not omit_set.isdisjoint (pair.funs.values())]))
	random.shuffle (pairs)
	results = [toplevel_check_wname (pair, quiet, check_loops = loops,
			report_mode = report_mode)
		for pair in pairs]
	if not report_mode:
		printout ('Results: %s' % results)
		count = len ([1 for (_, r) in results if r == 'True'])
		printout ('%d proofs checked' % count)
		count = len ([1 for (_, r) in results
			if r in ['ProofAbort', None]])
		printout ('%d proofs skipped' % count)
		fails = [(nm, r) for (nm, r) in results
			if r not in ['True', 'ProofAbort', None]]
		printout ('Failures: %s' % fails)
		if omitted:
			printout ('%d pairings omitted: %s'
				% (len (omitted), omitted))

def save_compiled_funcs (fname):
	out = open (fname, 'w')
	for (f, func) in functions.iteritems ():
		trace ('Saving %s' % f)
		for s in func.serialise ():
			out.write (s + '\n')
	out.close ()

def main (args):
	quiet = False
	excluding = False
	excludes = set ()
	loops = True
	tags = set ()
	report = False
	for arg in args:
		try:
			if arg == 'quiet':
				quiet = True
			elif arg == 'report':
				report = True
			elif arg == 'report-to:':
				(_, s) = arg.split (':', 1)
				f = open (s, 'w')
				target_objects.trace_files.append (s)
				report = True
			elif arg == 'all':
				check_all (excludes, quiet,
					loops = loops, tags = tags,
					report_mode = report)
			elif arg == 'all_safe':
				check_all (set.union (target_objects.danger_set,
					excludes), quiet,
					loops = loops, tags = tags,
					report_mode = report)
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
			elif excluding:
				excludes.add (arg)
			else:
				if arg not in excludes:
					check_search (arg, quiet, tags = tags,
						report_mode = report,
						check_loops = loops)
		except Exception, e:
			print 'EXCEPTION in syscall arg %s:' % arg
			print traceback.format_exc ()

main (sys.argv[2:])

