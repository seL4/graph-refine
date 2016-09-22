# * Copyright 2016, NICTA
# *
# * This software may be distributed and modified according to the terms
# of
# * the BSD 2-Clause license. Note that NO WARRANTY is provided.
# * See "LICENSE_BSD2.txt" for details.
# *
# * @TAG(NICTA_BSD)

import re
import graph_refine.syntax as syntax
import graph_refine.problem as problem
import graph_refine.stack_logic as stack_logic
from graph_refine.syntax import true_term, false_term, mk_not
from graph_refine.check import *
import graph_refine.search as search

import elf_parser
import graph_refine.target_objects as target_objects

from imm_utils import *
from elf_file import *
from addr_utils import *
from call_graph_utils import gFuncsCalled
from dot_utils import toDot,toGraph
from addr_utils import gToPAddrP,callNodes

def loadCounts(dir_name):
    #loop_counts.py must contain exactly 1 dict called man_loop_counts
    context = {}
    execfile('%s/loop_counts.py' % dir_name,context)

    #we should have a dict of addr -> bound
    assert 'loops_by_fs' in context
    lbfs = context['loops_by_fs']
    return lbfs

class immFunc (Borg):
    def __init__(self,elf_fun=None,load_counts=False):
        Borg.__init__(self)
        if not elf_fun:
            return
        self.elf_fun = elf_fun
        self.name = elf_fun.name
        self.addr = elf_fun.addr
        self.g_f = elf_fun.g_f
        self.asm_fs = elfFile().asm_fs
        self.imm_nodes = {}
        self.bbs = {}
        self.loaded_loop_counts = False
        self.parse_only = False
        self.loop_bounds = {}
        # dict of f-> loop_heads -> (bound, description)
        self.loops_by_fs = {}
        #f -> p_n
        self.p_entries = {}
        if load_counts:
           self.loaded_loops_by_fs = loadCounts(elfFile().dir_name)
           self.loaded_loop_counts = True

    def process(self):
        if self.bbs != {}:
            return
        self.makeBinGraph()
        self.loopheads = {}
        self.findLoopheads()
        lbfs = self.loops_by_fs
        if self.loaded_loop_counts:
            self.bin_loops_by_fs = self.loaded_loops_by_fs
            print 'loaded loop counts from file'
        else:
            #build bin_loops_by_fs from loops_by_fs
            self.bin_loops_by_fs = {}
            blbf = self.bin_loops_by_fs
            for f in lbfs:
                blbf[f] = {}
                p = self.f_problems[f]
                pA = lambda x: phyAddrP(x,p)
                loops = lbfs[f]
                for p_head in loops:
                    assert pA(p_head) not in blbf
                    blbf[f][pA(p_head)] = loops[p_head]

    def isBBHead(self,p_nf):
        if not self.isRealNode(p_nf):
          return False
        g_n = self.phyAddr(p_nf)
        if not type(g_n) == int:
          return False
        return g_n in self.bbs

    #bin addr to bb addr
    def bbAddr(self,addr):
        bbs = self.bbs
        for x in bbs:
          if addr in bbs[x]:
            return x
        print 'addr: %x' % addr
        assert False, 'BB not found !!'

    def toPhyAddrs(self, p_nis):
      return [self.phyAddr(x) for x in p_nis]

    #find all possible entries of the loop for Chronos
    def findLoopEntries(self, loop, f):
        p = self.f_problems[f]
        head = None
        lp = [x for x in list(loop) if self.isRealNode( (x,f) )]
        lpp = []
        lp_phys = self.toPhyAddrs([(x,f) for x in lp])
        for x in lp:
          #loop entry, must be
          #1. a basic block head and
          #2. has >=1 edge from outside the loop
          if (x, f ) in self.pf_deadends:
              ##gotta be halt / branch to halt
              continue
          phy_n = self.phyAddr((x,f))
          node = self.imm_nodes[phy_n]
          imm_ext_edges_to = [y for y in node.edges_to if (y not in lp_phys)]
          if ( len(imm_ext_edges_to) >= 1 and self.isBBHead((x,f)) ):
            lpp.append(x)
        return lpp

    def findLoopheads(self):
        self.imm_loopheads = {}
        #loopheads = {}
        loopheads = []
        #self.loopheads = loopheads
        loops_by_fs = self.loops_by_fs
        for (f,p) in [(f,self.f_problems[f]) for f in self.f_problems]:
            p.compute_preds()
            p.do_loop_analysis(skipInnerLoopCheck=True)
            l = p.loop_data
            if p.loop_heads():
                loops_by_fs[f] = {}
            for x in p.loop_heads():
              fun,_ = self.pNToFunGN((x,f))
              #dodge halt
              if fun in elfFile().deadend_funcs:
                continue
              loopheads.append((x, f))
              #the 0 worker_id will get ignored by genLoopHeads.
              #FIXME: do this properly..
              loops_by_fs[f][x] = (2**30,'dummy',0) 
        assert loopheads
        for p_nf in loopheads:
          p_n, f = p_nf
          p = self.f_problems[f]
          ll = p.loop_data[p_n][1]
          z = self.findLoopEntries(ll, f)
          #map from potential heads -> head, hack around chronos 'feature'
          for q in z:
            assert q not in self.imm_loopheads, 'one addr cannot have >1 loopcounts !'
            self.imm_loopheads[self.phyAddr((q,f))] = p_nf

        return 

    def firstRealNodes(self,p_nf,visited = None,may_multi=False,may_call=False,skip_ret=False):
        """
        Locate the first real node from, and including, p_addr, 
            or branch targets if it hits a branch before that. 
            Returns a list of p_nf
        """
        elf_fun = self.elf_fun
        p_n,f = p_nf
        next_p_nf = p_nf
        ret = []
        if visited == None:
            #print 'fRN on p_n %d, fun: %s' % (p_n,f)
            visited = []

        if p_nf in visited:
          return []
        visited.append(p_nf)

        assert self.pf_deadends != None
        while True:
          if self.isRealNode(next_p_nf):
             return [next_p_nf]
          next_p_n , next_f, next_p = self.unpackPNF(next_p_nf)
          if ( next_p_n == 'Ret' and f == self.name):
            return [('Ret',f)]
          elif next_p_n == 'Ret':
            if skip_ret:
              return []
            assert False,'firstRealNodes reached Ret when skip_ret is False'
          p_node, edges = self.pNodeConts(next_p_nf, may_call=may_call)
          if edges == []:
            return []
          assert (edges)
          if len(edges) > 1:
            assert may_multi
            for p_e in edges:
                for ee in self.firstRealNodes(p_e ,visited = list(visited),may_multi=may_multi,may_call=may_call,skip_ret=skip_ret):
                  ret.append(ee)

            return ret
          else:
              next_p_nf = edges[0]

    #function p_n belongs to, g_n
    def pNToFunGN(self,p_nf):
       p_n,f,p = self.unpackPNF(p_nf)
       tag = p.node_tags[p_n]
       _, x = tag
       f_name, g_n = x
       return f_name,g_n

    #given p_n is an imm call, return is_taillcall
    def isCallTailCall(self,p_nf):
        #    suc = p_n_cs[0]
        g_n = self.phyAddr(p_nf)
        return elf_parser.isDirectBranch(g_n)

    def isStraightToRetToRoot(self,p_nf):
        p_n,f,p = self.unpackPNF(p_nf)
        if p_n == 'Ret' and f == self.name:
          return True
        elif p_n == 'Ret':
          return False
        if self.isRealNode(p_nf):
          return False
        if self.phyAddr(p_nf)=='RetToCaller':
          return False
        elif type(p_n) == int:
          _,pf_conts = self.pNodeConts(p_nf)
          p_conts = [x[0] for x in pf_conts]
          if len(p_conts) == 1:
            return self.isStraightToRetToRoot((p_conts[0],f))
        return False


    #whether the corresponding imm has a return edge
    def isImmRootReturn(self,p_nf):
        p_n,f = p_nf
        if f != self.name :
          return False
        _, pf_conts = self.pNodeConts(p_nf)
        for x in pf_conts:
          if self.isStraightToRetToRoot(x):
            return True
        return False

    #whether p_n leads straightly to RetToCaller
    def isStraightToRetToCaller(self,p_nf):
        p_n,f = p_nf
        if p_n == 'Ret':
          if f != self.name:
            return True
          else:
            return False
        if self.isRealNode(p_nf):
          return False
        if self.phyAddr(p_nf)=="RetToCaller":
          return True
        elif type(p_n) == int:
          _,pf_conts = self.pNodeConts(p_nf)
          p_conts = [x[0] for x in pf_conts]
          if len(p_conts) == 1:
            return self.isStraightToRetToCaller((p_conts[0],f))
        return False
    
    #All return except the root one
    def isImmRetToCaller(self,p_nf):
        g_n = self.phyAddr(p_nf)
        p_n,f,p = self.unpackPNF(p_nf)
        if isCall(p.nodes[p_n]):
          return False
        p_node,pf_conts = self.pNodeConts(p_nf)
        p_conts = [x[0] for x in pf_conts]
        
        conts = [x for x in p_conts if type(p_n) == int]
        #print '     p_n %s p_conts %s' % (p_n,p_conts)
        n_rtc = 0
        assert self.phyAddr(p_nf) == g_n
        for pf_cont in pf_conts:
          cont_n,cont_f = pf_cont
          if not isCall(self.f_problems[cont_f].nodes[cont_n]):
            if self.isStraightToRetToCaller(pf_cont):
                ret = (pf_cont)
                n_rtc += 1
        if not ( n_rtc <= 1):
          #print 'p_n %s g_n %s: n_rtc %s' % (p_n, self.phyAddr(p_n), n_rtc)
          assert False
        if n_rtc > 0:
          return ret
        return False
     
    def funName(self,p_nf):
        p_n,f = p_nf
        fname = self.f_problems[f].nodes[p_n].fname
        if '.' in fname:
          #print 'f: %s' % fname
          s = []
          for c in fname:
            if c == '.':
              s.append('_')
            else:
              s.append(c)
          return ''.join(s)
        return fname

    def makeProblem(self,f):
        p = problem.Problem(None, 'Functions (%s)' % f)
        p.add_entry_function(self.asm_fs[f], 'ASM')
        p.do_analysis()
        return p
    
    def isSpecInsFunc(self,f):
        """
        Returns whether f is the name of  a special function 
        used to model special instruction
        """
        return f.startswith ("instruction'")
    
    def makeBinGraph(self):
        """
        Prepare problems for all functions transitively called by self,
        and turn this into a binary CFG
        """
        self.f_problems = {}
        if self.name not in elfFile().tcg:
            print elfFile().tcg.keys()
        tc_fs = list(elfFile().tcg[self.name])
        for f in tc_fs + [self.name]:
            assert '.' not in f
            if self.isSpecInsFunc(f):
                continue
            p = problem.Problem(None, 'Functions (%s)' % f)
            p.add_entry_function(self.asm_fs[f], 'ASM')
            self.f_problems[f] = p
            #print 'f %s, p.nodes: %d' % (f,len(p.nodes) )
            #get its entry
            assert len(p.entries) == 1
            self.p_entries[f] = p.entries[0][0]

        print 'all problems generated'
        self.findAllDeadends()
        print "all deadends found"
        #now generate the bin graph

        for f,p in self.f_problems.iteritems():
            for p_n in p.nodes:
                if type(p_n) != int:
                    continue
                p_nf = (p_n,f)
                if p_nf in self.pf_deadends:
                    continue
                if self.isRealNode(p_nf):
                    #print 'adding: %s' % str(p_nf)
                    self.addImmNode(p_nf)

        self.imm_entry = self.phyAddr(self.firstRealNodes((self.p_entries[self.name], self.name ))[0])
        #print 'self.imm_entry %x' % self.imm_entry
        self.bbs = findBBs(self.imm_entry,self)


    def findAllDeadends(self):
        self.pf_deadends = []
        pf_deadends = self.pf_deadends
        self.deadend_g_ns = set()
        #Halt is a deadend function, and should never be called, it's equivalent to Err for our purpose
        for dead_f in elfFile().deadend_funcs:
          print 'dead_f %s' % dead_f
          deadend_f_g_n = elfFile().funcs[dead_f].addr
          self.deadend_g_ns.add (deadend_f_g_n)
          print 'deadend_f_g_n 0x%x' % deadend_f_g_n

        for (f,p) in self.f_problems.iteritems():
            for p_n in p.nodes:
                if self.isDeadend((p_n,f)):
                    pf_deadends.append((p_n,f))

    def isDeadend(self,p_nf,visited=None):
        '''
        Determine if p_nf (p_n, function) is a deadend node
        '''
        if p_nf in self.pf_deadends:
          return True
        p_n, f, p = self.unpackPNF(p_nf)
        if visited == None:
          visited = []
        if p_n == 'Err':
          return True
        if p_n == 'Ret':
          return False
        if p_nf in visited:
          return True
        if isCall(p.nodes[p_n]):
            #walk into the callee problem
            f = self.funName(p_nf)
            #FIXME: dodge dummy functions
            if 'instruction' in f:
                return False
            if f in elfFile().deadend_funcs:
              return True
            p_callee = self.f_problems[f]
            assert len(p_callee.entries) == 1
            p_callee_n = p_callee.entries[0][0]
            return self.isDeadend((p_callee_n,f),visited=visited + [p_nf])

        if type(p_n) == int and self.phyAddr(p_nf) == 'RetToCaller':
          return False
        g_n = self.phyAddr(p_nf)
        
        if g_n in self.deadend_g_ns:
          return True
        
        #note: pNodeConts ensures we stay in the same problem
        node,fconts = self.pNodeConts(p_nf)
        conts = [ x[0] for x in fconts]
        for p_c in conts:
          assert p_c != p_n
          if not self.isDeadend( (p_c,f), visited = visited + [p_nf]):
            return False

        #all ends are dead, thus deadend
        return True

    def unpackPNF(self,p_nf):
        p_n,f = p_nf
        p = self.f_problems[f]
        return (p_n,f,p)

    def phyAddr (self,p_nf) :
        p_n, f , p = self.unpackPNF(p_nf)
        if not isinstance(p_n,int):
            return p_n
        _,x = p.node_tags[p_n]
        if x == 'LoopReturn':
            return 'LoopReturn'
        try:
            f_name,g_addr = x
        except:
            print f
            print 'tags: %s'%  str(p.node_tags[p_n])
            assert False
        return g_addr
    #must not reach Ret
    def pNodeConts(self, p_nf, no_deadends=False, may_call = False):
        p_n,f, p = self.unpackPNF(p_nf)
        p_node = p.nodes[p_n]
        if isCall(p_node):
          assert may_call
          fun_called = self.funName(p_nf)
          p = self.f_problems[fun_called]
          entry = self.p_entries[fun_called]
          pf_conts = [(entry,fun_called)]
          return p_node, pf_conts
        assert p_n != 'Ret'
        p_conts = filter(lambda x: x != 'Err', p_node.get_conts())
        if no_deadends:
            p_conts = filter(lambda x: (x, p_i) not in pi_deadends, p_conts)
        pf_conts = [(x , f) for x in p_conts]
        return p_node,pf_conts
    
    def isRealNode(self,p_nf):
        p_n,f = p_nf
        if p_n == 'Ret':
          return False
        g_n = self.phyAddr(p_nf)
        if g_n == 'RetToCaller':
            return False
        elif self.isLoopReturn(p_nf):
            return False
        elif type(g_n) != int:
            print 'g_n %s' % str(g_n)
            assert False, 'g_n expected of typ int'
        #elif g_n % 4 == 0 and not self.isLoopReturn(p_nf):
        elif g_n % 4 == 0:
            assert not self.isLoopReturn(p_nf)
            return True
        else:
            return False

    def isLoopReturn(self,p_nf):
        p_n,f = p_nf
        p = self.f_problems[f]
        tag = p.node_tags[p_n]
        return tag[1] == 'LoopReturn'

    def addImmNode(self,p_nf):
        imm_nodes = self.imm_nodes
        g_n = self.phyAddr(p_nf)
        p_node,pf_conts = self.pNodeConts(p_nf)
        p_conts = [x[0] for x in pf_conts]
        p_n,f,p = self.unpackPNF(p_nf)
        #print "adding imm_node p_n: %s f: %s" % (p_n,f)
        if g_n in imm_nodes:
          #we have been here before
          node = imm_nodes[g_n]
        else:
          node = immNode(g_n,rawVals(g_n))
          imm_nodes[g_n] = node

        dont_emit = []
        p_imm_return_to_caller_edge = self.isImmRetToCaller(p_nf)
        call_pn =  self.getCallTarg(p_nf)
        if call_pn:
            fun_called = self.funName((call_pn, f))
            if self.isSpecInsFunc(fun_called):
                #Hack: go straight to the return node, do nothing else
                next_addrs = p.nodes[call_pn].get_conts()
                assert len(next_addrs) == 1
                next_addr = next_addrs[0]
                assert next_addr not in ['Ret','Err']
                phy_next_addr = self.phyAddr((next_addr,f))
                i_e = immEdge(phy_next_addr, emit = True)
                node.addEdge(i_e)
                return
            imm_call = self.parseImmCall(p_nf)
            assert not p_imm_return_to_caller_edge
            g_call_targ,g_ret_addr,is_tail_call = imm_call
            dont_emit.append(g_call_targ)
            node.addCallRetEdges(g_call_targ, g_ret_addr,is_tail_call)

        elif p_imm_return_to_caller_edge or self.isImmRootReturn(p_nf):
            node.addRetEdge()

        #add edges to the imm node,ingore Err and halt
        for p_targ in p_conts:
          if type(p_targ) == int and (p_targ, f) not in self.pf_deadends:
            if p_targ == 'Ret':
              continue
            edges = self.firstRealNodes((p_targ,f),may_multi=True,may_call=True,skip_ret=True)
            for p_e in edges :
              #dodge halt
              if (p_e) in self.pf_deadends:
                continue
              g_e = self.phyAddr(p_e)
              assert g_e != None
              if g_e == 'Ret':
                continue
              assert g_e != 'Ret'
              i_e = immEdge(g_e,emit = g_e not in dont_emit)
              node.addEdge(i_e)

    def retPF(self,call_p_nf):
        p_n,f,p = self.unpackPNF(call_p_nf)
        assert len(p.nodes[p_n].get_conts()) == 1
        return ( (p.nodes[p_n].get_conts())[0] , f)
    
    def getCallTarg(self, p_nf):
        p_n,f,p = self.unpackPNF(p_nf)
        _, pf_conts = self.pNodeConts(p_nf)
        p_conts = map(lambda x: x[0],pf_conts)
        #is Imm call iff there is a successor of kind Call in the g graph
        p_n_cs = filter(lambda p_n_c:
                        type(p_n_c) == int
                        and not self.isLoopReturn(( p_n_c, f))
                        and isCall(self.gNode((p_n_c,f)))
                        , p_conts)
        if not p_n_cs:
          return None
        assert len(p_n_cs) == 1
        #return the p_n of the call node
        return p_n_cs[0]

    def parseImmCall(self,p_nf):
        """
        Returns (entry point to the called function, return addr, is_tailcall)
        """
        call_pn = self.getCallTarg(p_nf) 
        assert call_pn != None

        p_n,f,p = self.unpackPNF(p_nf)
        #print "p_n: %s, f: %s" % (p_n,f)
        p_nodes = p.nodes
        #find the return addr
        #print "call_pn = %d" % call_pn

        suc = self.firstRealNodes( (call_pn, f) ,may_multi=False,may_call=True)
        pf_call_targ = suc[0]
        g_call_targ = self.phyAddr(pf_call_targ)
        #locate the call return address
        f_caller, _ = self.pNToFunGN(p_nf)
        is_tailcall = self.isCallTailCall(p_nf)
        if not is_tailcall:
            #return the return addr
            phy_ret_addr = self.phyAddr(self.retPF((call_pn,f)))
        else:
            phy_ret_addr = None

        assert type(phy_ret_addr) == int or is_tailcall, "g_call_targ %s phy_ret_addr %s" % (g_call_targ, phy_ret_addr)
          #print 'call detected: phy_ret_addr %x' % phy_ret_addr
        return (g_call_targ, phy_ret_addr,is_tailcall)

    def gNode(self,p_nf):
        p_n,f,p = self.unpackPNF(p_nf)
        tag = p.node_tags[p_n]
        f = tag[1][0]
        g_n = tag[1][1]
        return self.asm_fs[f].nodes[g_n]
