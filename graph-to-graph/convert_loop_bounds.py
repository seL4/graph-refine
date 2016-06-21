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
def loopHeadsToWorkOn(lbfs, worker):
    ret = []
    n_ignored = 0
    for f in lbfs:
        for head in lbfs[f]:
            if "ignore" in lbfs[f][head][1]:
                n_ignored +=1
            elif (worker == -1) or (lbfs[f][head][2] == worker):
                ret += lbfs[f].keys()
    print 'ignored %d loops' % n_ignored
    print 'working on %s' % str(map(hex,ret))
    return ret

def convert_loop_bounds(target_dir_name, worker_id=None, cached_only=False):
    if worker_id == None:
        worker_id = -1
    args = target_objects.load_target(target_dir_name)
    context = {}
    execfile('%s/loop_counts.py' % target_objects.target_dir,context)
    assert 'loops_by_fs' in context
    lbfs = context['loops_by_fs']
    bin_heads = loopHeadsToWorkOn(lbfs, worker_id)
    functionsWithUnboundedLoop = set()
    #all_loop_heads = loop_bounds.get_all_loop_heads()
    print 'bin_heads: ' + str(bin_heads)
    for head in bin_heads:
        f = trace_refute.get_body_addrs_fun(head)
        if f not in lbfs:
            lbfs[f] = {}
        ret= None
        try:
            ret = loop_bounds.get_bound_super_ctxt(head,[],cached_only)
        except problem.Abort, e:
            print 'failed to analyse %s, problem aborted' % f
        except:
            print "Unexpected error:", sys.exc_info()
            raise
        old_worker = lbfs[f][head][2]
        if ret == None or ret[1]== 'None':
            if cached_only:
                comment = 'did not find cached result'
            else:
                comment = 'ignore: failed'
            lbfs[f][head] = (2**30, comment, old_worker)
            functionsWithUnboundedLoop.add(f)
        else:
            lbfs[f][head] = (ret[0],ret[1], old_worker)
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
    parser.add_argument('worker_id', type=int, help="what bound marker is this instance responsible for, -1 means everything")
    parser.add_argument('--cached_only', type=bool, default=False, help="Only read what's cached in LoopBounds.txt")
    args = parser.parse_args()
    worker_id = args.worker_id
    target_dir_name = args.target_dir_name
    print "I am worker %d" % worker_id
    addr_to_bound = {}
    target_dir_name = sys.argv[1]
    lbfs = convert_loop_bounds(target_dir_name, worker_id, cached_only = args.cached_only)
    if lbfs is None:
        sys.exit(-1)

