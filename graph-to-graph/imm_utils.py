# * Copyright 2016, NICTA
# *
# * This software may be distributed and modified according to the terms
# of
# * the BSD 2-Clause license. Note that NO WARRANTY is provided.
# * See "LICENSE_BSD2.txt" for details.
# *
# * @TAG(NICTA_BSD)
import sys
import re
from elf_file import elfFile
from addr_utils import phyAddrP

def genLoopheads(bin_loops_by_fs, dir_name, incremental_head=None ):
    '''
    write all loop heads with current bound (can be dummy) to dir_name/loop_counts.py
    If incremental_head is specified (as (function_name, head)), reload from loop_counts and update only that entry from bin_loops_by_fs. This allows us to manually edit loop_counts.py while the tool is running.
    '''
    if incremental_head is not None:
        loop_counts_file_name = '%s/loop_counts.py' % dir_name
        context = {}
        execfile(loop_counts_file_name, context)
        lbfs = context['loops_by_fs']
        f, head = incremental_head
        lbfs[f][head] = bin_loops_by_fs[f][head]
    else:
        lbfs = bin_loops_by_fs

    h_f = open(loop_counts_file_name,'w')
    h_f.write('loops_by_fs = {\n')
    imm_l_f = open ('%s/imm_counts' % dir_name,'w')
    for f in sorted(lbfs):
        loops = lbfs[f]
        h_f.write('\'%s\': {\n' % f)
        for head in sorted(loops):
            bound,desc = loops[head]
            if bound < 2046 or desc == 'dummy':
                #print large bounds in hex
                s_bound = str(bound)
            else:
                s_bound = hex(bound)
            h_f.write(' 0x%x : ( %s, \'%s\') ,\n' % (head, s_bound, desc))
            imm_l_f.write('l 0x%x %s\n' % (head, s_bound))
        h_f.write('},\n')

    h_f.write('}\n')
    h_f.close()
    imm_l_f.close()

class immEdge:
    def __init__ (self,targ,targ_valid=True,emit=True):
       if targ_valid:
        self.targ = targ
        assert targ != None
       else:
        self.targ = None
       self.emit = emit
    def __repr__(self):
       return 'targ %s' % (self.targ)

class immNode:
    def __init__(self,addr,inst):
        self.addr = addr
        #excludes returns
        self.edges = []
        #edges going to this node
        self.edges_to = []
        #a call_edge must always come with a call_ret_edge,unless it's a tailcall
        self.call_edge = None
        #where does the return go to ?
        self.call_ret_edge = None
        self.is_tail_call = False
        self.ret_edge = None
        #all immNodes are instructions
        self.text, self.raw_inst = inst
        #number of edges to this node
        self.n_edges_to = 0

    def __repr__(self):
        s = '%s:\n' % self.addr
        for e in self.edgesOut():
          s = s + '  -> %s\n' % e.targ
        for e in self.edges:
          s = s + '  e-> %s\n' % e.targ
        if self.call_edge:
          s += '   has call_edge %s' % self.call_edge.targ
        if self.is_tail_call:
          s += '   is tail call'
        if self.ret_edge:
          s += '   has ret_edge'
        return s

    #number of edges going out from this node
    def nEdgesOut(self):
        ret = len(self.edgesOut())
        #if self.return_edge:
        #  ret += 1
        if self.ret_edge:
            ret += 1
        return ret

    def edgesOut(self):
        ret = list(self.edges)
        if self.call_edge:
          ret.append(self.call_edge)
        return ret

    #add func call and func call return edges
    def addCallRetEdges(self,call_targ,call_ret_targ,is_tail_call):
        if self.call_edge:
          assert call_targ == self.call_edge.targ
          assert call_ret_targ == self.call_ret_edge.targ
          assert is_tail_call == self.is_tail_call
          return
        self.call_edge = immEdge(call_targ)
        self.call_ret_edge = immEdge(call_ret_targ,targ_valid= not is_tail_call)
        assert is_tail_call or call_ret_targ
        self.is_tail_call = is_tail_call

    def addRetEdge(self):
        self.ret_edge = immEdge(None,targ_valid=False)

    def addEdge(self,edge):
      #reject duplicate edges
      new = True
      for x in self.edges:
          if x.targ == edge.targ:
              new = False
              break
      if new:
          self.edges.append(edge)

#determine, for all imm nodes, the number of edges going into them
def findNEdgesTo (imm_fun):
    nodes = imm_fun.imm_nodes
    nodes[imm_fun.imm_entry].n_edges_to = 1
    for n in nodes:
      node = nodes[n]
      for e in node.edges:
        if e.targ == 'Ret':
          continue
        nodes[e.targ].n_edges_to += 1
        nodes[e.targ].edges_to.append(n)
      if node.call_edge:
        nodes[node.call_edge.targ].n_edges_to += 1
        nodes[node.call_edge.targ].edges_to.append(n)
        if not node.is_tail_call:
          if node.call_ret_edge.targ not in nodes:
            print 'call returning to: %x, from call site %x' % (node.call_ret_edge.targ, n)
          nodes[node.call_ret_edge.targ].n_edges_to += 1
          nodes[node.call_ret_edge.targ].edges_to.append(node.call_edge.targ)

#addr is imm_addr
def findBBs(addr,imm_fun,bbs=None,curr_bb = None,visited=None):
    if visited is None:
        findNEdgesTo(imm_fun)
        visited = []
        bbs = {}
    #bbs is a dict of lists, the lists are basic blocks, with elemetns being nodes in the bb
    node = imm_fun.imm_nodes[addr]
    #print 'findBBs(%s, curr_bb %s, n_edges_to %s)\n' %(addr,curr_bb,node.n_edges_to)
    if addr in visited:
      return
    visited.append(addr)
    n_out = node.nEdgesOut()
    n_in = node.n_edges_to
    #this is a new basic block
    if curr_bb == None:
      curr_bb = addr
      # the starting node is also a part of the bb
      bbs[addr] = []

    # 4 cases, 1 in >1 out, >1 in 1 out, or >1 in >1 out and 1 in 1 out

    if n_in == 1 and n_out == 1:
        #1 in 1 out, the current bb continues
        bbs[curr_bb].append(addr)
    elif n_in == 1 and n_out > 1:
      # 1 in >1 out
      #the current basic block has ended
      bbs[curr_bb].append(addr)
      assert bbs[curr_bb] != []
      curr_bb = None
    elif n_in > 1:
      # >1 in, 1 out and >1 out
      #the current bb ended at the previous node, this node itself is a startbb
      bbs[addr] = [addr]
      #if out edges > 1, this node is a 1 node basic block, all target nodes are startbb
      #else this node is the start of a basic block
      curr_bb = None if n_out >1 else addr
    else:
      print 'imm_n: %s' % addr
      print 'n_in %s n_out %s' % (n_in, n_out)
      assert False

    if n_out > 1:
        #all edges coming out from this node are startBBs
        for e in node.edges:
            if e.targ != 'Ret' and e.targ not in bbs:
                bbs[e.targ] = []
    edges = node.edgesOut()
    edges = [x for x in edges if x.targ != 'Ret']
    #do the same for all reachable nodes
    for e in edges:
        assert e.targ !=None
        findBBs(e.targ, imm_fun, bbs = bbs, curr_bb=curr_bb,visited=visited)
    if node.call_ret_edge:
        #being returned to makes u a start of a basic block for Chronos
        if node.call_ret_edge.targ:
            findBBs (node.call_ret_edge.targ, imm_fun, bbs = bbs, curr_bb=None,visited=visited)
    return bbs
