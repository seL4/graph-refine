#
# Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

import pydot
import subprocess
from elf_file import *


'''
All functions in this file will be updated to reflect changes made, they are currently outdated and produce misleading outputs if called.
This file was used for debugging the toolchains.
'''

def loopDot(head,p):
    from elf_correlate import immFunc
    graph = pydot.Dot(graph_type='digraph')
    nodes = {}
    ns = list(p.loop_data[head][1])
    print 'len: %d' % len(ns)
    for n in ns:
      phy_n = immFunc().phyAddrP(n,p)
      if isinstance(phy_n,int) and phy_n %4 == 0:
        text, _ = rawVals(phy_n)
      else:
        text = ''
      n_cap = '%s / %d \n %s' % (hex(phy_n),n, text)
      if [x for x in p.nodes[n].get_conts() if x not in ns and not x == 'Err']:
        print 'found exit node ! %d' % n
        nodes[n] = pydot.Node(n_cap,color="blue")
      else:
        nodes[n] = pydot.Node(n_cap)
    for n in nodes:
      graph.add_node(nodes[n])

    for n in ns:
        conts = p.nodes[n].get_conts()
        for c in conts:
          if c in ns:
            graph.add_edge(pydot.Edge(nodes[n],nodes[c]))

    graph.write_svg('graphs/loop.svg' )
    graph.write('graphs/loop.dot' )
    return


def toDot(imm_fun):
    #FIXME: add in return tracing
    graph = pydot.Dot(graph_type='digraph')
    nodes = {}
    #add all nodes
    for n in imm_fun.imm_nodes:
      text, _ = rawVals(n)
      nodes[n] = pydot.Node('addr_%s \n %s' % (hex(n), text))
      assert rawVals(n)

    #artificially insert the return node
    nodes['Ret'] = pydot.Node('Ret')

    #print 'nodes added to graph'
    for n in imm_fun.imm_nodes:
      imm_node = imm_fun.imm_nodes[n]
      for e in imm_node.edges:
          #print'%s -> %s' % (n,e.targ)
          graph.add_edge(pydot.Edge(nodes[n],nodes[e.targ]))
    #print 'edges added'
    graph.write_svg('graphs/ii_%s.svg' % imm_fun.g_f.name)
    #graph.write_png('/mnt/hgfs/imgs/ii_%s.png' % imm_fun.g_f.name)
    #print 'imm graph for %s generated' % self.g_f.name

def toDotBB(imm_fun):
    #FIXME as above
    graph = pydot.Dot(graph_type='digraph')
    nodes = {}
    #add all bbs
    print 'generating dot graph...'
    for bb_n in imm_fun.bbs:
      bb = imm_fun.bbs[bb_n]
      #print 'BB[%s]: %s' % (bb_n, bb)
      if len(bb) == 1:
        n_cap = '0x%x\n' % bb[0]
      else:
        n_cap = '0x%x - 0x%x\n' % (min(bb), max(bb))
      is_loophead = False
      for n in bb:
        i_node = imm_fun.imm_nodes[n]
        if n in imm_fun.imm_loopheads:
          is_loophead = True
        #only the entry can have >1 incoming edges
        assert n == bb[0] or i_node.n_edges_to <= 1
        #only the last node can have >1 outgoing edges
        if not (n == bb[-1] or i_node.nEdgesOut() == 1):
          print 'edges %s' % i_node
          print 'nEdgesOut %s' % i_node.nEdgesOut()
        assert (n == bb[-1] or i_node.nEdgesOut() == 1)
        assert rawVals(n)
        text,_ = rawVals(n)
        n_cap += '%s; %s\n' % (hex(n),text)

      if len(bb) > 2:
        is_jt = False
        #is_jt = imm_fun.isJumpTable(imm_fun.gToPAddr(bb[-2],no_match_expected = True, may_multi= True))
      else:
        is_jt = False
      if is_loophead:
        nodes[bb[0]] = pydot.Node(n_cap,Nodestyle="bold",color="hotpink")
      elif is_jt:
        nodes[bb[0]] = pydot.Node(n_cap,Nodestyle="bold",color="blue")
      else:
        nodes[bb[0]] = pydot.Node(n_cap)

    #artificially insert the return node
    nodes['Ret'] = pydot.Node('Ret')
    for n in nodes:
      graph.add_node(nodes[n])

    #print 'nodes added to graph'
    for bb in imm_fun.bbs:
      BB = imm_fun.bbs[bb]
      #for n in BB:
      n = BB[len(BB)-1]
      for e in imm_fun.imm_nodes[n].edges:
        #print'%s -> %s' % (n,e.targ)
        graph.add_edge(pydot.Edge(nodes[BB[0]],nodes[e.targ]))
    #print 'edges added'
    graph.write_svg('graphs/i_%s.svg' % imm_fun.g_f.name)
    #graph.write_png('/mnt/hgfs/imgs/i_%s.png' % imm_fun.g_f.name)
    print 'imm graph for %s generated' % imm_fun.g_f.name

def toGraph(p,f_name):
    p.save_graph('graphs/%s.dot' % f_name)
    p = subprocess.Popen(["dot","graphs/%s.dot"%f_name,"-Tsvg","-o","graphs/%s.svg" % f_name])
    p.communicate()
    ret = p.returncode
    assert not ret
    p = subprocess.Popen(["rm","graphs/%s.dot" % f_name])
    p.communicate()
    ret = p.returncode
    assert not ret
    #p = subprocess.Popen(["dot","graphs/%s.dot"%f_name,"-Tpng","-o","/mnt/hgfs/imgs/%s.png" % f_name])
