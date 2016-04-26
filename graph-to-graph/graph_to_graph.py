# * Copyright 2016, NICTA
# *
# * This software may be distributed and modified according to the terms
# of
# * the BSD 2-Clause license. Note that NO WARRANTY is provided.
# * See "LICENSE_BSD2.txt" for details.
# *
# * @TAG(NICTA_BSD)

import sys
import graph_refine.syntax as syntax
import graph_refine.problem as problem
import call_graph_utils
import bench
from bench import analyseFunction
import convert_loop_bounds
import conflict
from graph_refine.check import *
import graph_refine.target_objects as target_objects

from elf_correlate import *
import re
import cplex

def printHelp():
      print "args: <dir_name> <function_name> <flag> <phantom preemption point (only required when flag is --x)>"
      print 'e.g. ../graph-refine/gcc-O2 handleSyscall --L'
      print '''flags: --l generate loop heads at dir_name/loop_counts.py NOTE: this will override an existing file
      --L use loop counts at the file dir_name/loop_counts.py to generate ILP problem
      --i interactive mode (for debugging)
      --x automated WCET estimating, firstly generate the loop heads, then automatically deduce the loop bounds, and finally use the automatically determined loopbounds to estimate teh WCET. A conflict file specifying additional preemption points 
      '''

if __name__ == '__main__':
    if len(sys.argv) < 4:
        printHelp()
        sys.exit(-1)
    else:
        entry_point_function = sys.argv[2]
        gen_heads = False
        load_counts = False
        interactive = False
        automated = False
        conflict_file = None

        dir_name = sys.argv[1]
        print 'dir_name: %s' % dir_name
        flag = sys.argv[3]
        assert flag in ['--l','--L','--i', '--x']
        if flag == '--l':
            gen_heads = True
            bench.bench(dir_name, entry_point_function, gen_heads, load_counts,interactive)
            sys.exit(0)
        if flag == '--L':
          load_counts = True
        if flag == '--i':
          interactive = True
        if flag == '--x':
            if len(sys.argv) < 5:
                printHelp()
                sys.exit(-1)
            conflict_file = sys.argv[4]
            asm_fs = bench.init(dir_name)
            import convert_loop_bounds
            analyseFunction(entry_point_function,asm_fs, dir_name, True, False, False)
            print "loop heads generated"
            convert_loop_bounds.convert_loop_bounds(dir_name)
            print "loop bounds automatically determined via graph-refine and results stored in %s/loop_counts.py" % dir_name
            print "Using automatically determined loopbounds to generate ILP problem"
            analyseFunction(entry_point_function, asm_fs, dir_name, False, True, False, stopAtILP= True)
            print "Annotating ILP problem with preemption bounds"
            entry_point_function = entry_point_function.strip()
            prefix = dir_name + '/' + entry_point_function
            tcfg_map_file_name = prefix + ".imm.map"
            current_ilp = prefix + ".imm.ilp"
            print "current_ilp: %s" % current_ilp
            stripped_ilp = cplex.stripFooter(current_ilp)
            ilp_to_generate = prefix + "_annotated.imm.ilp"
            sol_to_generate = prefix + "_annotated.imm.sol"
            preemption_limit = 5
            print "Calling conflict to annotate and estimate WCET with conflict file %s, preemption limit: %d" % (conflict_file, preemption_limit)
            conflict.conflict(entry_point_function, tcfg_map_file_name, [conflict_file], stripped_ilp, ilp_to_generate, dir_name, sol_to_generate, emit_conflicts=True, do_cplex=True, preempt_limit= preemption_limit)
    bench_ret = bench.bench(dir_name, entry_point_function, gen_heads,load_counts,interactive)
    print 'bench returned: ' +  str(bench_ret)
