# * Copyright 2016, NICTA
# *
# * This software may be distributed and modified according to the terms
# of
# * the BSD 2-Clause license. Note that NO WARRANTY is provided.
# * See "LICENSE_BSD2.txt" for details.
# *
# * @TAG(NICTA_BSD)

#!/usr/bin/env python

import os, re, sys, copy
from subprocess import Popen, PIPE
from elf_correlate import immFunc
from elf_file import elfFile
from addr_utils import callNodes,phyAddrP
import bench
import cplex
import graph_refine.trace_refute as trace_refute
import convert_loop_bounds
from graph_refine.trace_refute import parse_num_arrow_list

global bb_addr_to_ids
global id_to_bb_addr
global id_to_context
global bb_count
global edge_count
global bb_addrs_in_loops
global tcfg_paths
bb_addr_to_ids = {}
id_to_context = {}
bb_count = {}
edge_count = {}
bb_addrs_in_loops = []
tcfg_paths = {}
id_to_bb_addr = {}

def cleanGlobalStates():
    global bb_addr_to_ids
    global id_to_bb_addr
    global id_to_context
    global bb_count
    global edge_count
    global bb_addrs_in_loops
    global tcfg_paths

#we assume the ilp problem stays the same modulo extra refutes
    bb_addr_to_ids = {}
    id_to_context = {}
    bb_count = {}
    edge_count = {}
    bb_addrs_in_loops = []
    tcfg_paths = {}
    id_to_bb_addr = {}
    print 'conflict.py: global states cleaned'

def read_variables(input_filename):
        var_re = re.compile(r'^d(\d+|Sta)_(\d+)\s+([\d.]+)$')

        f = open(input_filename)
        global path_counts
        global total_edges
        while True:
                s = f.readline()
                if s == '':
                        break
                g = var_re.match(s.strip())
                if not g:
                        continue

                from_id, to_id, count = g.groups()
                if from_id not in path_counts:
                        path_counts[from_id] = {}

                if to_id in path_counts[from_id]:
                        raise Exception("Variable from %s to %s mentioned more than once." % (from_id, to_id))

                count = int(round(float(count)))
                if count == 0:
                        continue

                path_counts[from_id][to_id] = count
                total_edges += count

        f.close()
        if not path_counts:
                raise Exception("No variables found in solution.")



def read_tcfg_map(input_filename):
        tcfg_re = re.compile(
                r'''^
                        (\d+)
                        \( \d+ \. \d+ \)
                        \(
                                (0x[0-9a-f]+)
                                \+
                                (0x[0-9a-f]+)
                        \):
                        \s
                        \[\s
                                ([\d\s]*)
                        \]([0-9a-f\s]+)$''',
                        re.VERBOSE)

        f = open(input_filename)

        global bb_addr_to_ids
        global bb_count
        global edge_count
        global id_to_bb_addr
        id_to_bb_addr = {}
        while True:
                s = f.readline()
                if s == '':
                        break
                g = tcfg_re.match(s.strip())
                if not g:
                        continue

                bb_id, bb_addr, bb_size, bb_dests, ctx_str= g.groups()
                bb_id = int(bb_id)
                #print ctx_str

                bb_addr = int(bb_addr, 16)
                #our context matching assumes that all bb addr has the same n_digits...
                assert bb_addr >= 0xe0000000, 'Go fix context matching :( bb_addr: %x' % bb_addr
                bb_size = int(bb_size, 16)
                bb_dests = [int(x.strip()) for x in bb_dests.split() if x.strip()]
                ctx_str_list = ctx_str.split(' ')
                ctx_list = [int(x, 16) for x in ctx_str_list if x <> '']

                if not bb_addr in bb_addr_to_ids:
                        bb_addr_to_ids[bb_addr] = [bb_id]
                else:
                        bb_addr_to_ids[bb_addr].append(bb_id)

                #if ctx_list[0] == 0:
                #        ctx_list.pop(0)
                loop_head = ctx_list[0]
                if loop_head == 0:
                  pass
                else:
                  if not bb_addr in bb_addrs_in_loops:
                    bb_addrs_in_loops.append(bb_addr)
                  pass
                ctx_list=ctx_list[1:]

                id_to_context[bb_id] = ctx_list
                tcfg_paths[bb_id] = bb_dests
                assert bb_id not in id_to_bb_addr
                id_to_bb_addr[bb_id] = bb_addr
                bb_count[bb_id] = 0
                for dest in bb_dests:
                        edge_count[(bb_id, dest)] = 0

        f.close()

def callSitePA(pn,p):
        return phyAddrP(p.preds[pn][0],p)

def callstring_bbs(fs,cs_so_far = None):
          bbAddr= immFunc().bbAddr
          #print 'fs: %s' % str(fs)
          #print 'cs_so_far: %s' % str(cs_so_far)
          if not cs_so_far:
                cs_so_far = [ ]
          ret = []
          top_f = fs[0]
          next_f = fs[1]
          #print 'top_f #%s# next_f #%s#' % (top_f,next_f)
          p = immFunc().f_problems[top_f]
          cns = callNodes(p,fs=[next_f])
          #print 'cns:%s'% cns
          pA = lambda x: phyAddrP(x,p)
          #phy_rets =[phyAddrP(x,p) for x in cns]
          phy_rets =[callSitePA(x,p) for x in cns]
          #print ' phy_rets: %s' % str(phy_rets) 
          if len(fs) == 2:
                return  [(cs_so_far +[bbAddr(x)]) for x in phy_rets]

          assert len(fs) >2
          for x in phy_rets:
                ret += callstring_bbs(fs[1:],cs_so_far = cs_so_far + [bbAddr(x)])
          return ret

#does context match the list of bb_heads s ?
def bbs_context_match(context_targ, context_to_match):
        bbAddr = immFunc().bbAddr
        #print 'context: %s' % str(context)
        #print 's: %s' % str(s) 
        #all of s must be in context to begin with, strip the 0 subfix
        bb_ctx = [bbAddr(x) for x in context_targ[:-1]]
        if len(bb_ctx) < len(context_to_match):
           return False
        for i in range(len(context_to_match)):
           if context_to_match[i] != bb_ctx[len(context_to_match) -i - 1]:
                 return False
        return True

def inALoop(addr):
    '''
    Is the addr part of a loop ?
    '''
    return bbAddr(addr) in bb_addrs_in_loops

def inFunLoop(addr):
  from addr_utils import gToPAddrP
  f = elfFile().addrs_to_f[addr]
  p = immFunc().f_problems[f]
  p_addr = gToPAddrP(addr,p)
  return p_addr in p.loop_data

#ids for bb_addr with context
def idsMatchingContext(full_bb_context):
  ret = []
  for i,addr in enumerate(full_bb_context):
    ids = bb_addr_to_ids[addr]
    #we know there can only be 1 matching id
    match_id = None
    for d in ids:
      if bbs_context_match(id_to_context[d],full_bb_context[:i]):
        match_id = d
        break
    assert match_id != None
    ret.append(match_id)
  return ret 

#translate context in bin to a list of ids corresponding to the context
#note: no tcfg_ids can have the exact same context
def contextsBbAddrToIds(context,bb_addr):
  bb_context = [bbAddr(x[0]) for x in context]
  ret = idsMatchingContext(context, bb_addr)
  return ret

def bbAddrs(l):
  bbAddr = immFunc().bbAddr
  return [bbAddr(x) for x in l if x]

#get the unique tid corresponding to addr that matches context[: -truncate], 
#given that context is in the from of contexts from id_to_context
def addr_context_truncate_get_tid(addr, context, truncate):
  #note: r
  if truncate:
    #context = context[: - truncate]
    context = context[truncate : ]
  tids = [tid for tid in bb_addr_to_ids[addr]
    if id_to_context[tid] == context]
  if len(tids) > 1:
    ctx = id_to_context[tids[0]]
    print 'tids: %r' % tids
    assert all ([id_to_context[x]==ctx for x in tids ])
    #FIXME: some pairs of tids seem to share the exact same bb_addr, full ctx.
    # seems to be related to tailcalls
    print '!! WARNING !! Figure out wht\'s going on !! Seems to be a chronos feature...'
    print 'tids[0]: %d' % tids[0]
    return tids[0]
  assert len(tids) == 1, (tids, addr, context, truncate)
  [tid] = tids
  return tid

#emit a particular trace. full_context comes unmodified from id_to_context
def emitInconsistentTrace(fout, full_context,visits,line=None):
  if line==None:
    line = ''
  #fout.write('\ === impossible/inconsistent:' +line+' === \n')
  print ' full_context: %r' % full_context
  id_points = []
  for x in visits:
    addr,stack_i = x
    print ' visit: %s, stack_i %d' % (addr,stack_i)
    #addr = bbAddr(addr)
    if stack_i == 0 and bbAddr(addr) == bbAddr(full_context[0]):
      #special case for addr == tip_context, since id_to_context will be effectively one context short, as (addr / tip_context) itself will be missing.
      id_points.append(addr_context_truncate_get_tid(addr, full_context, 1))
    else:
      id_points.append(addr_context_truncate_get_tid(addr, full_context, stack_i))

  max_stack_i =max(visits, key = lambda x: x[1])[1]
  print 'max_stack_i: %d' % max_stack_i
  assert (max_stack_i < len(full_context))

  limiting_node_bb = bbAddr(full_context[max_stack_i])
  limiting_tid = addr_context_truncate_get_tid(limiting_node_bb, full_context,max_stack_i + 1)

  #now emit the ilp constraint
  print 'id_points: %r' % id_points
  s = ' + '.join(['b{0}'.format(p) for p in id_points])
  s += ' - {0} b{1} <= 0\n'.format( (len(id_points) -1  ), limiting_tid )
  print 'emitting \n%s\n' % s
  fout.write(s)

'''
def isHalt(addr):
  text = elfFile().lines[addr]
  if 'halt' in text:
    return True
  return False
'''
#context is infeasible
def emitImpossible(fout,context):
  #get the matching ids
  tids = bb_addr_to_ids[bbAddr(context[-1])]
  len_a = len(tids)
  tids = [x for x in tids if bbs_context_match(id_to_context[x], bbAddrs(context[:-1])) ]
  s=''
  assert tids
  for tid in tids:
    s += 'b{0} = 0\n'.format(tid)
  fout.write(s)
  return 

#context addrs are bbAddrs
#one_context is true iff all visits lie in context 0
def emitInconsistent(fout, context,visits):
  if visits == []:
    #this is just an impossible trace
    emitImpossible(fout,context)
    return
  #FIXME:
  #bug : [4026621540, 4026621472] : [4026621428 <- 1] would become
  #      [4026621540] : [4026621428<-0], which isn't the same thing...
  '''
  if all ([l > 0 for (_, l) in visits]):
    m = min ([l for (_, l) in visits])
    visits = [(baddr, l - m) for (baddr, l) in visits]
    context = context[: -m]
  '''
  #padding visits with (context[-1],0) should work.
  #can't think of a better way atm
  if all ([l > 0 for (_, l) in visits]):
    visits.append( (bbAddr(context[-1]),0) )

  print 'context: %r' % context
  print 'visits: %r' % visits 

  base_addr = [baddr for (baddr, l) in visits if l == 0][0]
  tids = bb_addr_to_ids[bbAddr(base_addr)]

  r_context = list(context)
  r_context.reverse()

  if bbAddr(base_addr) == bbAddr(context[-1]):
    #special case...
    for tid in tids:
      tid_ctxt = id_to_context[tid]
      if r_context and tid_ctxt[ : len(context) - 1] == r_context[1:]:
        emitInconsistentTrace(fout,[context[-1]]+tid_ctxt,visits)
  else:
    for tid in tids:
      tid_ctxt = id_to_context[tid]
      if r_context and tid_ctxt[ :len(context) ] == r_context:
        emitInconsistentTrace(fout,tid_ctxt,visits)

  return

def emit_f_conflicts (fout, line):
  '''
  '''
  bbAddr = immFunc().bbAddr
  match = re.search(r'\s*\[(?P<infeas>.*)\]\s*:\s*(?P<kind>.*$)', line)
  print 'infeas: %s' % match.group('infeas')
  infeasible_fs = match.group('infeas').split(',')
  print 'infeasible_fs: %s' % infeasible_fs
  #find all bb_addrs where f[-1] can be called by f[-2]
  bbCallStrings = callstring_bbs(infeasible_fs)
  print 'bbcs: %s' % str(bbCallStrings)
  for s in bbCallStrings:
   for x in s:
      assert bbAddr(x) == x
      final_callee_bb = s[-1]
      #print 'final_callee_bb: %s'% str(final_callee_bb)
      assert final_callee_bb in bb_addr_to_ids
      ids = bb_addr_to_ids[final_callee_bb]
      ids_ctx = [x for x in ids if bbs_context_match(id_to_context[x],s[:-1])] 
      print 'ids: %d, ids_ctx: %d' % (len(ids),len(ids_ctx))
      #ok, now all of these are just unreachable.
      for tcfg_id in ids_ctx:
        fout.write("b{0} = 0\n".format(tcfg_id))

def process_conflict(fout, conflict_files):
    fake_preemption_points = []
    for conflict_file in conflict_files:
            f = open(conflict_file,'r')
            global bb_addr_to_id
            fout.write('\ === conflict constraints from %s === \n\n' % conflict_file)
            last_bb_id = 0
            bbAddr = immFunc().bbAddr
            while True:
                line = f.readline()
                if line == '':
                        break
                #get rid of all white spaces
                line = line.replace(' ', '')
                line = line.rstrip()
                if line.startswith('#') or line=='':
                        #comment line
                        continue
                if line.rstrip() == '':
                        continue
                match = re.search(r'.*:\s*(?P<kind>.*$)', line)
                kind = match.group('kind')
                #print 'kind: %s' % kind
                if kind == 'possible':
                        continue
                elif kind == 'f_conflicts':
                        emit_f_conflicts (fout, line)
                elif kind == 'phantom_preemp_point':
                        match = re.search(r'\[(?P<addr>.*)\]:(?P<kind>.*$)', line)
                        fake_preemption_points.append(int(match.group('addr'),16))
                elif kind == 'times':
                        match = re.search(r'\s*\[(?P<addr>.*)\]\s*:\s*\[(?P<times>.*)\]\s*:\s*(?P<kind>.*$)', line)
                        addr = int(match.group('addr'),16)
                        times = int(match.group('times'))
                        print 'addr: %x' % addr
                        print 'times: %d' % times  
                        times_limit(fout,[addr],times)
                else:
                    bits = line.split(':')
                    [stack,visits,verdict] = bits
                    assert 'impossible' in verdict
                    stack = trace_refute.parse_num_list(stack)
                    visits = trace_refute.parse_num_arrow_list(visits)
                    bb_visits = [(bbAddr(x[0]),x[1]) for x in visits]
                    in_loops = [x for x in (stack[1:] + [x[0] for x in visits]) if inFunLoop(x)]
                    if in_loops:
                        print '!!! loops in inconsistent !!!'
                        print '%r' % in_loops
                        print 'rejected line: %s\n\n' % line
                        continue
                    print 'line: %s' % line
                    emitInconsistent(fout, stack,bb_visits)
            f.close()
    fout.write("\n");
    return fake_preemption_points 

def add_impossible_contexts(fout):
    fout.write('\ === excluded function constraints === \n\n')
    for (tid, ctxt) in id_to_context.iteritems ():
        if len (ctxt) <= 2:
            continue
        if not trace_refute.ctxt_within_function_limits (ctxt[:-2]):
            fout.write ('b%s = 0\n' % tid)

def print_constraints(conflict_files, old_cons_file, new_cons_file,sol_file_name, preempt_limit):
        global bb_count
        global edge_count
        #copy the file
        p = Popen(['cp', old_cons_file, new_cons_file])
        p.communicate()
        ret = p.returncode
        assert not ret
        #fin = open(old_cons_file)
        #append the new constraints at the end
        fout = open(new_cons_file,'a+')
        #copy everything until we hit the General label
        #cplex.endProblem(fout,log_file_name='./new-gcc-O2.imm.sol')
        cplex.endProblem(fout,sol_file_name)
        fout.write('add\n')
        add_impossible_contexts(fout)
        fake_preemption_points = process_conflict(fout,conflict_files)
        print '%r' % fake_preemption_points
        preemption_limit(fout,fake_preemption_points,preempt_limit)
        fout.write('end\n')
        cplex.solveProblem(fout,presolve_off=False)
        fout.close()

def id_print_context(id1,ctx=None):
        if ctx==None:
                ctx = id_to_context[id1][:-1]
        for bb in ctx:
          print '%s'% elfFile().addrs_to_f[bb]
        return

def preemption_limit(fout,fake_preemption_points,preempt_limit):
        #hardcoded preemption point limit
        fout.write('\ === preemption constraints === \n\n')
        preemp_addr = elfFile().funcs['preemptionPoint'].addr
        times_limit(fout,fake_preemption_points+[preemp_addr],preempt_limit)

def times_limit(fout, addrs,limit):
        ids = []
        for addr in addrs:
          ids += bb_addr_to_ids[addr]
        fout.write('b{0} '.format(ids[0]))
        for x in ids[1:]:
          fout.write(' + b{0}'.format(x))
        fout.write(' <= {0}\n'.format(limit))

def conflict(entry_point_function, tcfg_map, conflict_files, old_ilp, new_ilp, dir_name, sol_file, emit_conflicts=False, do_cplex=False, interactive=False, silent_cplex=False, preempt_limit= None, default_phantom_preempt=False):
        if preempt_limit == None:
            preempt_limit = 5
        if default_phantom_preempt:
            conflict_files.append(convert_loop_bounds.phantomPreemptsAnnoFileName(dir_name))
        #initialise graph_to_graph so we get immFunc
        #load the loop_counts
        print 'conflict.conflict: sol_file %s' % sol_file
        bench.bench(dir_name, entry_point_function,False,True,False,parse_only=True )
        #we need the loop data
        immFunc().process()
        global bbAddr
        bbAddr = immFunc().bbAddr
        read_tcfg_map(tcfg_map)
        if interactive:
          assert False, 'Halt'
        if emit_conflicts:
          print 'new_ilp:%s' % new_ilp
          print_constraints(conflict_files, old_ilp, new_ilp, sol_file, preempt_limit)
          if do_cplex:
            cplex_ret = cplex.cplexSolve(new_ilp,silent=silent_cplex,sol_file=sol_file)
            print 'cplex_ret: %s' % cplex_ret
            return cplex_ret
        #print_constraints(sys.argv[3], sys.argv[4], sys.argv[5])

if __name__ == '__main__':
        if len(sys.argv) != 9:
                print '''Usage: python conflict.py [tcfg map] [conflict file] [ilp file with footer stripped] [new ilp file] [target_dir] [flag] [preemption limit] [sol file to be generated]
                conflict file 1 and/or 2 can be empty
                flag is one of:
                        --c
                                generate a new conflict file
                        --i
                                interactive mode, for debugging only
                        --cx
                                generate a new conflict file and call cplex directly'''
                sys.exit(1)
        
        tcfg_map = sys.argv[1]
        old_ilp = sys.argv[3]
        new_ilp = sys.argv[4]
        dir_name = sys.argv[5]
        flag = sys.argv[6]
        preempt_limit = int(sys.argv[7])
        print 'preempt_limit: %d' % preempt_limit
        sol_file = sys.argv[8]
        assert 'sol' in sol_file
        conflict_files = [sys.argv[2]]
        print 'sol_file: %s' % sol_file
        print 'old_ilp %s' % old_ilp
        print 'conflict_files: %r' % conflict_files
        emit_conflicts = False
        interactive = False
        do_cplex=False
        if flag == '--c':
          emit_conflicts = True
        if flag == '--cx':
          emit_conflicts = True
          do_cplex = True
        elif flag == '--i':
          interactive = True
        #FIXME: un-hardcode the entry point function's name
        ret = conflict('handleSyscall', tcfg_map,conflict_files,old_ilp,new_ilp,dir_name,sol_file,emit_conflicts=emit_conflicts,do_cplex=do_cplex,interactive=interactive,preempt_limit = preempt_limit, default_phantom_preempt=True)
        print 'conflict terminated'
        print 'ret: %s' % str(ret)

