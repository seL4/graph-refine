# * Copyright 2016, NICTA
# *
# * This software may be distributed and modified according to the terms
# of
# * the BSD 2-Clause license. Note that NO WARRANTY is provided.
# * See "LICENSE_BSD2.txt" for details.
# *
# * @TAG(NICTA_BSD)

import os, sys, time
from subprocess import Popen, PIPE
import graph_refine.trace_refute as trace_refute
import conflict
import cplex

def silence():
    '''
    Silence all outputs to stdout and stderr
    '''
    #open 2 fds
    saved_fds = None
    null_fds = None
    null_fds = [os.open(os.devnull, os.O_RDWR) for x in xrange(2)]
    #save the current file descriptors to a tuple
    saved_fds = os.dup(1), os.dup(2)
    #put /dev/null fds on 1 and 2
    os.dup2(null_fds[0], 1)
    os.dup2(null_fds[1], 2)
    return (saved_fds, null_fds)

def unsilence(save_fds, null_fds):
    '''
    Un-silence outputs to stdout and stderr
    '''
    #restore stdin and stderr
    os.dup2(save_fds[0], 1)
    os.dup2(save_fds[1], 2)
    os.close(null_fds[0])
    os.close(null_fds[1])
    return (save_fds, null_fds)

def auto_infea(dir_name, entry_point_function, manual_conflicts_file, results_dir, initial_case_iteration, preemption_limit):
    kernel_elf_file = dir_name+'/kernel.elf'
    tcfg_map = dir_name + '/%s.imm.map' % entry_point_function
    kernel_elf_file = dir_name+'/kernel.elf'
    ilp_nofooter = cplex.stripFooter(dir_name + '/%s.imm.ilp' % entry_point_function)
    
    auto_refutes_file = results_dir+'/refutes.txt'

    p = Popen(['touch', auto_refutes_file])
    p.communicate()
    assert not p.returncode

    results_file = results_dir+ '/results.txt'
#we want to see results as we go, set bufsize to 0
    results_f = open(results_file,'w',0)

#setup trace_refute's environment
    from graph_refine.target_objects import target_dir, target_args
    target = '%s/target.py' % dir_name
    target_dir.set_dir(dir_name)

    case_i = initial_i
    while True:
        sol_file = results_dir+'/case_%d.sol' % case_i
        ilp_file = results_dir+'/case_%d.ilp' % case_i
        print 'case_i = %d' % case_i
        print 'calling conflict.conflict'
#silence()
#get the wcet with existing conflicts
        conflict.cleanGlobalStates()

        #FIXME: un-hardcode the entry function
        wcet = conflict.conflict(entry_point_function, tcfg_map, [manual_conflicts_file,auto_refutes_file],ilp_nofooter,ilp_file,dir_name, sol_file, emit_conflicts=True, do_cplex=True, silent_cplex=True, preempt_limit=preemption_limit)
#unsilence()

        print 'conflict.main returned'

        results_f.write('case %d\n' % case_i)
        results_f.write('   wcet: %s\n' % wcet)

#reconstruct the worst case
        refutables_fname = results_dir + '/refutables_%d' % case_i 
        f_refutables = open(refutables_fname,'w')
        print 'reconstructing the worst case for case %d' % case_i
        p = Popen(['python', 'reconstruct.py', '--refutable', dir_name, sol_file, tcfg_map, kernel_elf_file], stdout=f_refutables)
        p.communicate()
        ret = p.returncode
        print 'ret: %d'% ret
        assert ret == 0
        
        f_refutables.close()
        #now call trace_refute
        t = time.asctime()
        c1 = time.time()
        print 'calling trace_refute, time is: %s' % t
        results_f.write(' trace_refute called at: %s\n' % t)
        silence_all = False
        if silence_all:
            #but before we do, supress output.
            (saved_fds, null_fds) = silence()
        new_refutes,_ = trace_refute.refute(refutables_fname, auto_refutes_file, [auto_refutes_file])
        if silence_all:
            #restore stdin and stderr
            unsilence(saved_fds, null_fds)
        c2 = time.time()
        t = time.asctime()
        print 'trace_refute returned, time is: %s' % t
        results_f.write(' trace_refute returned at: %s\n' % t)

        results_f.write('   this took %f seconds\n' % (c2-c1))

        if not new_refutes:
            print 'At case %d, trace_refute cannot find any more refutations' % case_i
            results_f.write('terminated normally: trace_refute cannot find any more refutations\n')
            break

#cp the auto_refutes_file to keep a copy
        p = Popen(['cp', auto_refutes_file, results_dir+'/refutes_%d.txt'% case_i])
        p.communicate()
        assert not p.returncode
        case_i += 1

    results_f.close()

if __name__ == '__main__':    
    if len(sys.argv) != 5:
        print 'Usage: python auto_infea.py <dir_name> <entry point function> <results directory> <initial i>'
        print 'results direcotry should already exists and be empty'
        print 'initial i determine which iterations to start at, use 0 for fresh runs'
        print len(sys.argv)
        sys.exit(0)
    dir_name = sys.argv[1]
    entry_point_function = sys.argv[2]
    from convert_loop_bounds import phantomPreemptsAnnoFileName
    preempt_conflicts_file = phantomPreemptsAnnoFileName(dir_name)
    results_dir = sys.argv[3]
    initial_i = int(sys.argv[4])
    auto_infea(dir_name, entry_point_function,preempt_conflicts_file, results_dir, initial_i, preemption_limit = 5)

