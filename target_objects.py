#
# Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

# these objects are to be filled in by the target

import sys

class TargetDir:
	def __init__ (self):
		self.d = None
	def __str__ (self):
		return self.d
	def set_dir (self, d):
		self.d = d

target_dir = TargetDir ()
target_args = []

structs = {}
functions = {}
functions_by_tag = {}
const_globals = {}

symbols = {}
sections = {}

rodata = [None, None, None]

pairings = {}
# pre_pairings are optional
pre_pairings = {}

use_hooks = set ()
avail_hooks = {'problem_var_rep': {}, 'loop_var_analysis': {},
	'rep_unsafe_const_ret': {}, 'fun_calling_convention': {},
	'extra_wcet_assertions': {}, 'wcet_function_limits': {},
	'assume_sp_equal': {}, 'wcet_functions_to_avoid': {},
	'post_emit_node': {},
}

def add_hook (hook_key, module_key, hook):
	avail_hooks[hook_key][module_key] = hook
def hooks (hook_key):
	return [hook for (module_key, hook)
		in avail_hooks[hook_key].iteritems ()
		if module_key in use_hooks]

danger_set = set ([])

# this shared callback is used for tracing by everyone

trace_depth = [0, 1]
trace_files = []

def printout (s):
	print s
	sys.stdout.flush ()
	for f in trace_files:
		f.write (s + '\n')
		f.flush ()

def depth_tracer (s, push):
	if push != 0:
		trace_depth[0] += push
	if trace_depth[0] <= trace_depth[1]:
		printout (s)

def default_tracer (s, push):
	printout (s)

tracer = [default_tracer]

def trace (s, push = 0):
	tracer[0](str (s), push)

def load_target (target, target_args = None):
	target_dir.set_dir (target)
	if target_args != None:
		target_args.extend (target_args)
	package = '.'.join (__name__.split ('.')[:-1])
	if package:
		pck = sys.modules[package]
		pck.__path__.append (target)
	else:
		sys.path.append (target)
	import target

def load_target_args (args = None):
	if args == None:
		args = list (sys.argv)
	if len (args) <= 1:
		import os.path
		objname = os.path.basename (args[0])
		dirname = os.path.dirname (args[0])
		exname = os.path.join (dirname, 'example')
		print 'Usage: python %s <target> <instructions>' % objname
		print 'Target should be a directory.'
		if os.path.isdir (exname):
			print 'See example target (in %s)' % exname
		else:
			print 'See example target in graph-refine dir.'
		assert not 'Target specified'
	else:
		target = args[1]
		t_args = [arg[7:] for arg in args
			if arg.startswith ('target:')]
		args = [arg for arg in args[2:]
			if not arg.startswith ('target:')]
		load_target (target, t_args)
		return args

