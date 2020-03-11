#
# Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

import re
from graph_refine.target_objects import functions, functions_by_tag
import graph_refine.problem as problem
from borg import Borg

#hardcoded list of function(s) that should never be called given correctness
deadend_funcs = ['halt']

class elfFunc:
    def __init__ (self,f_name,f_addr,g_f):
        self.name = f_name
        self.addr = int(f_addr,16)
        # a mapping from addr to line text
        self.lines = {}
        self.g_f = g_f
    def __repr__ (self):
        return ("%s start addr %d %s %d instructions" % (self.name, self.addr,hex(self.addr),len(self.lines) ))
    def append (self,addr, line):
        self.lines[int(addr,16)] = line


class elfSym:
    def __init__ (self,addr,flags,section,ali_size):
        self.addr = addr
        self.ali_size = ali_size
        self.flags = flags
        self.section = section


class elfFile (Borg):
    def __init__ (self,dir_name=None,ignore_funs=None,elf_only=False):
        Borg.__init__(self)
        if not (dir_name):
           return
        try:
            self.f_text = open('%s/kernel.elf.txt' %dir_name)
            self.f_symtab = open('%s/kernel.elf.symtab' %dir_name)
        except :
            print "kernel.elf.* can't be opened at directory %s" %dir_name
            assert 0
        self.elf_only = elf_only
        if not elf_only:
            self.asm_fs = dict ([(x,functions[x]) for x in functions_by_tag['ASM']])
            asm_fs = self.asm_fs
            self.tcg = None
            #from original name to the cloned name
            self.to_clone_name = {}
            self.un_clone_name = {}
            for f in asm_fs:
               if 'clone' in f:
                  match = re.search('(.*)(_clone).*',f)
                  f_name = match.groups()[0]
                  self.to_clone_name[f_name] = f
                  self.un_clone_name[f] = f_name
                #print 'to_clone_name: %s' % self.to_clone_name
        #print 'un_clone_name: %s' % self.un_clone_name

        #self.insts = {}
        #funcs is a dict of func names to elfFunc objs
        self.funcs = {}
        #dict of sym names to sym objects
        self.syms = {}
        #dict of addresses to data
        self.literals = {}
        #addr -> line text
        self.lines = {}
        self.deadend_funcs = deadend_funcs
        self.dir_name = dir_name
        #maps addrs to fun name containing it
        self.addrs_to_f = {}
    #handle the clone subfixes
    def gFunName(self, f):
        asm_fs = self.asm_fs
        if f in asm_fs:
          return f
        elif f in self.to_clone_name:
          return self.to_clone_name[f]
        else:
          return f
    def gUnCloneName(self,f):
        if f in self.un_clone_name:
          return self.un_clone_name[f]
        return f

    def addSymbol(self,name,addr,flags,section,ali_size):
        self.syms[name] = elfSym(addr,flags,section,ali_size)

#for instructions, return (text, rawValue)
#for literals, return (size, rawValue)
def rawVals(addr,inst_only=False):
    #return text,rawValue
    assert addr % 4 == 0
    ef = elfFile()
    if addr in ef.lines:
       inst = ef.lines[addr]
    else:
      if inst_only:
          return None
      if addr in ef.literals:
        #print 'addr %s is a literal' % addr
        return ef.literals[addr]
      return None
    #we take everything after the addr and the raw instruction
    match = re.search(r'^.*:\s+(?P<raw>[a-f0-9]+)\s*(?P<text>.*)$',inst)
    return  ( match.group('text'), int(match.group('raw'),16))

def isSpecIns(fun_name):
    return fun_name.startswith("instruction'") or \
           fun_name.startswith("asm_instruction'") or \
           fun_name.startswith("impl'")

