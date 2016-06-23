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

#extract all loop heads from loops_by_fs
def loopHeadsToWorkOn(lbfs, funs_with_phantom_preempt, worker):
    ret = []
    n_ignored = 0
    for f in lbfs:
        for head in lbfs[f]:
            if (f not in funs_with_phantom_preempt) and ("ignore" in lbfs[f][head][1]):
                n_ignored +=1
            elif (worker == -1) or (lbfs[f][head][2] == worker):
                ret += lbfs[f].keys()
    print 'ignored %d loops' % n_ignored
    print 'working on %s' % str(map(hex,ret))
    return ret

def phantomPreemptsAnnoFileName(target_dir_name):
    return '%s/preempt_refutes.txt' % target_dir_name

def convert_loop_bounds(target_dir_name, worker_id=None, cached_only=False):
    if worker_id == None:
        worker_id = -1
    print 'target_dir_name: %s' % target_dir_name
    args = target_objects.load_target(target_dir_name)
    target_dir = target_objects.target_dir
    context = {}
    execfile('%s/loop_counts.py' % target_dir,context)
    assert 'loops_by_fs' in context
    lbfs = context['loops_by_fs']
    context = {}
    execfile('%s/phantom_preempt.py' % target_dir,context)
    funs_with_phantom_preempt = context['functions']
    if funs_with_phantom_preempt:
        preempt_annotations_file = open(phantomPreemptsAnnoFileName(target_dir), 'w')
    #print 'funs_with_phantom_preempt: %s' % str(funs_with_phantom_preempt)
    bin_heads = loopHeadsToWorkOn(lbfs, funs_with_phantom_preempt, worker_id)
    funs_with_unbounded_loop = set()
    #all_loop_heads = loop_bounds.get_all_loop_heads()
    print 'bin_heads: ' + str(bin_heads)
    for head in bin_heads:
        f = trace_refute.get_body_addrs_fun(head)
        if f not in lbfs:
            lbfs[f] = {}
        ret= None
        if f in funs_with_phantom_preempt:
             ret = (64, 'phantom_preempt')
             preempt_annotations_file.write("#" + f + "\n")
             preempt_annotations_file.write("[%s]:phantom_preemp_point\n\n" % hex(head))

             print '%s injected with phantom preemption point' % f
        else:
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
            funs_with_unbounded_loop.add(f)
        else:
            lbfs[f][head] = (ret[0],ret[1], old_worker)
        imm_utils.genLoopheads(lbfs, target_objects.target_dir, incremental_head=(f,head))
    preempt_annotations_file.close()
    unexpectedUnboundedFuns = set([x for x in funs_with_unbounded_loop if x not in funs_with_phantom_preempt])
    if unexpectedUnboundedFuns:
        print 'functions with unbounded loop and not bounded by preemption: %s' % str(unexpectedUnboundedFuns)
        return None
    return lbfs

if __name__== '__main__':
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("target_dir_name")
    parser.add_argument('--worker_id', type=int, help="what bound marker is this instance responsible for, -1 means everything", default= -1)
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

