# * Copyright 2016, NICTA
# *
# * This software may be distributed and modified according to the terms
# of
# * the BSD 2-Clause license. Note that NO WARRANTY is provided.
# * See "LICENSE_BSD2.txt" for details.
# *
# * @TAG(NICTA_BSD)
import graph_refine.loop_bounds as loop_bounds
import graph_refine.trace_refute as trace_refute
import graph_refine.target_objects as target_objects
from graph_refine.target_objects import functions
import graph_refine.problem as problem
import imm_utils
import sys

functionsBoundedByPreemptionOnly = set(['cancelAllIPC', 'cancelBadgedSends', 'cancelAllSignals'])

#extract all loop heads from loops_by_fs
def loopHeadsFromLBFS(lbfs):
    ret = []
    n_ignored = 0
    for f in lbfs:
        for head in lbfs[f]:
            if "ignore" not in lbfs[f][head][1]:
                ret += lbfs[f].keys()
            else:
                n_ignored +=1
    print 'ignored %d loops' % n_ignored 
    return ret

def convert_loop_bounds(target_dir_name):
    args = target_objects.load_target(target_dir_name)
    context = {}
    execfile('%s/loop_counts.py' % target_objects.target_dir,context)
    assert 'loops_by_fs' in context
    lbfs = context['loops_by_fs']
    bin_heads = loopHeadsFromLBFS(lbfs)
    functionsWithUnboundedLoop = set()
    #all_loop_heads = loop_bounds.get_all_loop_heads()
    print 'bin_heads: ' + str(bin_heads)
    for head in bin_heads:
        f = trace_refute.get_body_addrs_fun(head)
        if f not in lbfs:
            lbfs[f] = {}
        ret= None
        try:
            ret = loop_bounds.get_bound_super_ctxt(head,[])
        except problem.Abort, e:
            print 'failed to analyse %s, problem aborted' % f
        except:
            print "Unexpected error:", sys.exc_info()
            raise
        if ret == None or ret[1]== 'None':
            lbfs[f][head] = (2**30,'ignore: failed')
            functionsWithUnboundedLoop.add(f)
        else:
            lbfs[f][head] = ret
        imm_utils.genLoopheads(lbfs, target_objects.target_dir, incremental_head=(f,head))
    unexpectedUnboundedFuns = set([x for x in functionsWithUnboundedLoop if x not in functionsBoundedByPreemptionOnly])
    if unexpectedUnboundedFuns:
        print 'functions with unbounded loop and not bounded by preemption: %s' % str(unexpectedUnboundedFuns)
        return None
    return lbfs

if __name__== '__main__':
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("target_dir_name")
    args = parser.parse_args()
    target_dir_name = args.target_dir_name
    print "target_dir_name %s" % target_dir_name
    addr_to_bound = {}
    target_dir_name = sys.argv[1]
    lbfs = convert_loop_bounds(target_dir_name)
    if lbfs is None:
        sys.exit(-1)

