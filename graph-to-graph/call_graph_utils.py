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
from elf_file import elfFile

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
    for f in funs:
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

def dotCallGraph(f,cg,dir_name):
    graph = pydot.Dot(graph_type='digraph')
    #graph.set_overlap('scale')
    nodes = {}
    fun = f
    #all funs are nodes
    for f in cg:
      nodes[f] = pydot.Node(f)
      graph.add_node(nodes[f])
    #now add edges
    for f in cg:
      for ff in cg[f]:
        if ff not in nodes:
            nodes[ff] = pydot.Node(ff,Nodestyle="dotted")
            graph.add_node(nodes[ff])
        assert nodes[f]
        assert nodes[ff]
        graph.add_edge(pydot.Edge(nodes[f],nodes[ff]))
    print 'emitting call graph for %s' % fun
    graph.write_svg('graphs/call_graph_%s.svg' % fun)

def makeCallGraph(functions,dir_name):
    cg = funsCallGraph(functions,dir_name)
    dotCallGraph(cg,dir_name)

#return a list of all funcs transitively called by f
def transitiveCall(f,cg):
    ret = []
    vs = []
    #print '     cg[%s] : %s' % (f, cg[f])
    for x in cg[f]:
      vs.append(x)
    while vs:
       ff = elfFile().gFunName(vs.pop())
       assert '.' not in ff
       if ff not in ret:
          ret.append(ff)
    #      print 'ret + f: %s: ' % ff
    #      print '[f]: %s' % cg[ff]
          vs += cg[ff]
    return list(set(ret))

def makeFunCallGraph(f,funs,dn,ignore_funs):
    cg = funsCallGraph(funs,dn,ignore_funs)
    tc = transitiveCall(f,cg)
    cg_tc = {x:cg[x] for x in tc}
    cg_tc[f] = cg[f]
    #print 'cg_tc: %s' % cg_tc
    dotCallGraph(f,cg_tc,dn) 

#return a dict of dicts of fun to transitively called funcs
def transitiveCallGraph(funs,dn,ignore_funs):
    ret = {}
    cg = funsCallGraph(funs,dn,ignore_funs)
    for f in cg:
      ret[f] = transitiveCall(f,cg)
    return ret

#dict of number of transitive call to functions
def nFuncsFuncsTranCall(funs,dn,ignore_funs):
    tc = transitiveCallGraph(funs,dn,ignore_funs)
    return nFuncsFuncsCall(tc)

