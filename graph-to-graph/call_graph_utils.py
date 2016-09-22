# * Copyright 2016, NICTA
# *
# * This software may be distributed and modified according to the terms
# of
# * the BSD 2-Clause license. Note that NO WARRANTY is provided.
# * See "LICENSE_BSD2.txt" for details.
# *
# * @TAG(NICTA_BSD)

import pydot
import re
import graph_refine.problem as problem
from elf_file import elfFile, isSpecIns

#functions f called
def gFuncsCalled(f,fs,ignore_funs):
    g = fs[elfFile().gFunName(f)]
    call_node_indexes = [x for x in g.nodes if g.nodes[x].kind == 'Call']
    call_targs = [g.nodes[x].get_args()[0] for x in call_node_indexes]
    #rid clone subfixes
    call_targs = [x.split('.')[0] for x in call_targs]
    call_targs = [x for x in call_targs if x not in ignore_funs]

    return list(set(call_targs))

def funsCallGraph(funs,dir_name,ignore_funs):
    #dict to dicts of fun to funcs called
    cg = {}
    ignore_funs = ignore_funs + [f for f in funs if isSpecIns(f)]
    for f in funs:
        if isSpecIns(f):
            continue
        cg[f] = gFuncsCalled(f,funs,ignore_funs)
    return cg

def nFuncsFuncsCall(call_graph):
    ret = {}
    for f in call_graph:
        l = len(call_graph[f])
        if l not in ret:
            ret[l] = []
        ret[l].append(f)
    return ret

def dotCallGraph(fun,cg,dir_name):
    graph = pydot.Dot(graph_type='digraph')
    #graph.set_overlap('scale')
    nodes = {}
    
    callers = []
    vs = [fun]
    seen = []
    while vs:
        #print "vs: %s" % vs
        f = vs.pop()
        if f in seen:
            continue
        seen.append(f)
        callers += cg[f]
        callers.append(f)
        vs += cg[f]
    
    callers = set(callers)
    
    for f in callers:
      nodes[f] = pydot.Node(f)
      graph.add_node(nodes[f])
 
    n_edges = 0
    for f in callers:
        #now add edges
        for ff in cg[f]:
            if ff not in nodes:
                nodes[ff] = pydot.Node(ff,Nodestyle="dotted")
                graph.add_node(nodes[ff])
            assert nodes[f]
            assert nodes[ff]
            graph.add_edge(pydot.Edge(nodes[f],nodes[ff]))
            n_edges += 1

    print 'emitting call graph for %s' % fun
    print '%d nodes %d edges' % (len(nodes), n_edges)
    #graph.write_raw('%s/graphs/call_graph_%s.dot' % (dir_name,fun))
    #print '.raw generated'
    graph.write_svg('%s/graphs/call_graph_%s.svg' % (dir_name,fun))

def makeCallGraph(fun,functions,dir_name):
    cg = funsCallGraph(functions,dir_name,[])
    dotCallGraph(fun,cg,dir_name)

#return a list of all funcs transitively called by f
def transitivelyCalled(f,cg):
    ret = set()
    vs = list(cg[f]) # copy the list
    #print '     cg[%s] : %s' % (f, cg[f])
    while vs:
       ff = elfFile().gFunName(vs.pop())
       assert '.' not in ff
       if ff not in ret and not isSpecIns(ff):
          ret.add(ff)
          vs += cg[ff]
    return ret

#whether fun transtively calls one of fs_interested
def transitivelyCallsInterested(fun, cg, fs_interested):
    tc = transitivelyCalled(fun, cg)
    return (fun in fs_interested) or len([x for x in fs_interested if x in tc]) != 0
        
def drawFunCallGraph(f,funs,dn,ignore_funs,transitive=False, fs_interested=None):
    funs = {x: funs[x] for x in funs if not x.startswith("Kernel_C")}
    cg = funsCallGraph(funs,dn,ignore_funs)
    tc = transitivelyCalled(f,cg)
    if transitive:
        cg_tc = {x:transitivelyCalled(x,cg) for x in tc +[f]}
    else:
        #cg_tc = {x:cg[x] for x in tc + [f]}
        cg_tc = cg
    if fs_interested:
        cg_tc = {\
            caller: filter(lambda f: transitivelyCallsInterested(f, cg, fs_interested), cg_tc[caller]) \
        for caller in cg_tc if transitivelyCallsInterested(caller, cg, fs_interested)}
    
    dotCallGraph(f,cg_tc,dn)
    return cg_tc

#return a dict of dicts of fun to transitively called funcs
def transitiveCallGraph(funs,dn,ignore_funs):
    ret = {}
    cg = funsCallGraph(funs,dn,ignore_funs)
    for f in cg:
      ret[f] = transitivelyCalled(f,cg)
    return ret

#dict of number of transitively called functions to caller functions
def nFuncsFuncsTranCall(funs,dn,ignore_funs):
    tc = transitiveCallGraph(funs,dn,ignore_funs)
    return nFuncsFuncsCall(tc)

