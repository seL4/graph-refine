# * Copyright 2016, NICTA
# *
# * This software may be distributed and modified according to the terms
# of
# * the BSD 2-Clause license. Note that NO WARRANTY is provided.
# * See "LICENSE_BSD2.txt" for details.
# *
# * @TAG(NICTA_BSD)
from elf_file import *
import re

def parseSymTab():
    ef = elfFile()
    #parse the symbol table
    ef.syms = {}
    #skip the header
    while True:
      line = ef.f_symtab.readline()
      if line.startswith('SYMBOL TABLE'):
        break
    #the rest should be symbols
    #should look like <address> <flags> <section> <alignment/size> <name>
    #for "common" symbol it's alignment and for other it is size, seems like we don't need to distinguish the two 
    objdump_symbol_re = re.compile(
     r'^([a-f0-9]+) (.*) +([a-zA-Z0-9_*.]+)\t([a-f0-9]+)\s+([a-zA-Z0-9_. -]+)$')
    while True:
        line = ef.f_symtab.readline()
        g = objdump_symbol_re.match(line)
        if g is not None:
          addr, flags, section, ali_size, name = g.groups()
          if ' ' in name:
            print name
            assert(0)
          ef.addSymbol(name,addr, flags, section, ali_size)
          #print '%s \n' % flags
          #print 'addr %s flags %s section %s ali_size %s' % (addr,flags,section,ali_size)
        else :
          break

def parseTxt ():
    ef = elfFile()
    curr_func_name = None
    skip_next_line = False
    for line in ef.f_text:
      #hack used to skip the ndks_boot struct, which looks like a function
      if skip_next_line == True:
        skip_next_line = False
        continue
      #ingore empty lines and the header
      if line in ['\n','\r\n']:
        continue
      header = re.search('kernel\.elf:\s*file\s*format\s*elf32-littlearm',line)
      header2 = re.search('Disassembly of section \..*:',line)
      if header != None or header2 != None:
        continue
      #ndsk_boot is a strange function only used in bootstrapping, ask tom about it
      ndks = re.search('.*ndks_boot.*',line)
      if ndks != None:
         skip_next_line = True
         continue

      #a function looks like f0000088 <create_it_frame_cap>: 
      r = re.search('(?P<f_addr>.*) <(?P<f_name>.*)>:$',line)
      if r != None:
        #we are creating a new function
          #print '%s: %s' % (r.group('f_name'),r.group('f_addr'))
        curr_func_name = r.group('f_name')
        if (not ef.elf_only) and curr_func_name in ef.asm_fs:
          g_f = ef.asm_fs[curr_func_name]
        else:
          g_f = None
          #print '%s not found in asm_fs' % curr_func_name
        ef.funcs[curr_func_name] = elfFunc(curr_func_name, r.group('f_addr'),g_f)
        elf_fun = ef.funcs[curr_func_name]
        elf_fun.entry_addr = int(r.group('f_addr'),16);
        elf_fun.lines = {}

      else:
        #check if this is a literal line
        literal = re.search('(?P<addr>.*):\s*[a-f0-9]+\s*(?P<size>(\.word)|(\.short)|(\.byte))\s*(?P<value>0x[a-f0-9]+)$',line)
        if literal != None:
           if literal.group('size') == '.word': 
                size = 4
           else:
                assert False, '%s size undefined' % literal.group('size')
           line_addr = int(literal.group('addr'),16)
           ef.literals[line_addr] = (size,int(literal.group('value'),16))
           ef.addrs_to_f[line_addr] = curr_func_name
        else:
           #This is an instruction, 
            #extract the address, a line looks like f00000ac:>--e5801000 >--str>r1, [r0]
           match = re.search('(?P<line_addr>.*):.*',line)
           assert match !=None
           line_addr = int(match.group('line_addr'),16)
           elf_fun.lines[line_addr] = line
           #remove everything after ;
           
           line = line.split(';')[0]
           line = line.rstrip(' \t\n\r')
           ef.lines[line_addr] = line
           ef.addrs_to_f[line_addr] = curr_func_name

#is the mnemonic b ? bl, bx etc don't count
#used to detech tail call
def isDirectBranch(addr):
  inst = elfFile().lines[addr]
  match = re.search(r'[a-f0-9]+:\s*[a-f0-9]+\s+(b|bx)\s+.*',inst)
  return match is not None 

def parseElf(dir_name):
    ef = elfFile(dir_name)
    parseTxt()
    parseSymTab()
    return ef
    

