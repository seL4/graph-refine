#
# Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

import subprocess
import elf_file
import elf_correlate
import elf_parser
import chronos.emitter
import re
from dot_utils import *
import call_graph_utils
import sys
import traceback
import graph_refine.problem as problem
import imm_utils
from graph_refine.target_objects import functions, functions_by_tag
import graph_refine.target_objects as target_objects
import cplex
import conflict

chronos_executable = "../../chronos4.2/est"

fast_path = [
'fastpath_restore',
'fastpath_call',
'fastpath_reply_wait',
'slowpath'
]

dummy_funs = [
'idle_thread', 'halt',
] + fast_path

#funs called by boot_funs only
boot_funs_called = [
'strncmp'
]

# Global arch variable

bench_arch = 'armv7'

def makeGraph(f_name,fs):
    p = fs[f_name].as_problem(problem.Problem)
    toGraph(p,f_name)

def runExtract(program_n_flags,cwd=None):
    if cwd:
        p = subprocess.Popen(program_n_flags,cwd=cwd,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
    else:
        p = subprocess.Popen(program_n_flags,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
    out,err = p.communicate()
    retval = p.returncode
    return retval, out, err

#given the imm, call chronos and cplex to return (wcet,chronos_out,chornos_err)
def getWcetFromImm(imm_file_name, generateILPOnly= False):
    print 'running chronos...'
    ret,out,err = runExtract([chronos_executable, imm_file_name])
    print 'chronos completed, ret: %s, err: %s\n' % (ret,err)
    if ret:
        print 'Chronos FAILED\n out: %s\n err: %s\n' % (out,err)
        print 'Chronos FAILED\n'
        return None
    else:
        pass
        print 'Chronos succeeded'
    if generateILPOnly:
        print "ILP file generated"
        return None
    return  float(cplex.cplexSolve(imm_file_name+'.ilp')),out,err


def toElfImmFun(f,dir_name,load_counts):
    ef = elfFile()
    elf_fun = ef.funcs[elfFile().gFunName(f)]
    imm_fun = elf_correlate.immFunc(elf_fun,load_counts=load_counts)
    return elf_fun, imm_fun, ef

def toImmFun(f,dir_name,load_counts=False):
    _, imm_fun, _ = toElfImmFun(f,dir_name,load_counts)
    return imm_fun

def analyseFunction(f,asm_fs,dir_name,gen_heads,load_counts,emit_graphs, stopAtILP=False):
    print '========analsying from entry point: %s===========' % f
    elf_fun,imm_fun, ef = toElfImmFun(f, dir_name,load_counts)
    #emit graphs with graph-refine
    if emit_graphs:
        makeGraph(f,asm_fs)

    imm_fun.process()
    if gen_heads:
      print 'generating loop heads'
      imm_utils.genLoopheads(imm_fun.bin_loops_by_fs,dir_name)
      print 'loop heads generated'
      if gen_heads:
        return None
      else:
        import elf_correlate
        #load the dummy loop counts
        elf_correlate.immFunc().loaded_loops_by_fs = elf_correlate.loadCounts(dir_name)

    #if emit_graphs:
        #toDot(imm_fun)
        #toDotBB(imm_fun)

    emitter = chronos.emitter.ChronosEmitter(dir_name, f, imm_fun, None, bench_arch)
    emitter.emitTopLevelFunction()

    imm_file_name = emitter.imm_file_name

    ret_g = getWcetFromImm(imm_file_name, stopAtILP)
    if not ret_g:
      return None
    wcet, out_chronos_gg,err_chronos_gg = ret_g
    if wcet:
      print 'G2G-Chronos extracted, wcet: %s\n' % wcet
      return wcet
    return None

def init(dir_name, arch='armv7'):
    global bench_arch
    bench_arch = arch
    '''setup the target and initialise the elfFile'''
    target_objects.load_target(dir_name)
    sys.setrecursionlimit(2000)
    import graph_refine.stack_logic as stack_logic
    stack_logic.add_hooks ()
    #silence graph-refine outputs that  we don't care about when doing wcet
    def silent_tracer (s,v):
        if s.startswith('Loop') or re.search(r'\s*\(=',s) or re.search(r'\s*\(',s):
          return
        if s.startswith('requests') or s.startswith('Result:') or s.startswith('Now'):
          return
        if s.startswith('testing') or s.startswith('done') or s.startswith('rep_graph'):
          return
        if s.startswith('Testing') or s.startswith('Group'):
          return
        print s

    target_objects.tracer[0] = silent_tracer
    elf_parser.parseElf(dir_name, arch)
    asm_fs = elfFile().asm_fs
    tran_call_graph = call_graph_utils.transitiveCallGraph(asm_fs,dir_name,dummy_funs)

    elfFile().tcg = tran_call_graph
    elfFile().asm_idents = None
    elfFile().immed = None
    return asm_fs

def bench(dir_name, entry_point_function, gen_heads,load_counts, interactive, parse_only=False, conflict_file=None, arch='armv7'):
    global bench_arch
    asm_fs = init(dir_name)
    bench_arch = arch
    functions = target_objects.functions
    if parse_only or interactive:
        t = entry_point_function
        i = toImmFun(t,dir_name,load_counts=load_counts)
        i.process()
        return
    dn = dir_name
    emit_graphs = False
    wcet = analyseFunction(entry_point_function,asm_fs, dir_name, gen_heads, load_counts, emit_graphs=emit_graphs)
    return wcet

