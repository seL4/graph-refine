#
# Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

import re
import parser
import riscv_parser
import subprocess
from addr_utils import phyAddrP

verbose = False
from elf_file import elfFile, rawVals

'''
By default, the emitter handles armv7 instructions.
As we add RISC-V support in Chronos, we add "rv64", 64-bit RISC-V,
as another supported arch.
'''

valid_arch = ['armv7', 'rv64']


class ChronosEmitter:
    def __init__(self, dir_name, function_name, imm_fun, emit_as_dummy=None, arch='armv7'):
        self.function_name = function_name
        self.imm_fun = imm_fun
        self.imm_file_name = '%s/%s.imm' % (dir_name, function_name)
        self.imm_f = open(self.imm_file_name, 'w')
        self.debug_f = open('%s/d_%s.imm' % (dir_name, function_name), 'w')
        self.emitted_loop_counts_file = open('%s/%s_emittedLoopCounts' % (dir_name, function_name), 'w')
        self.emit_as_dummy = emit_as_dummy

        if arch in valid_arch:
            self.arch = arch
        else:
            self.arch = 'armv7'

        if self.arch == 'armv7':
            #			self.elf_fun_to_skip = elfFile().funcs['clean_D_PoU']
            # hack for running test code
            self.elf_fun_to_skip = []
        else:
            self.elf_fun_to_skip = []

        self.skip_fun = False

    def emitTopLevelFunction(self):
        imm_fun = self.imm_fun
        imm_f = self.imm_f
        debug_f = self.debug_f

        self.emitEntry()
        self.emitSyms()
        self.emitFunction()
        self.emitLiterals()

        self.imm_f.close()
        self.debug_f.close()
        self.emitted_loop_counts_file.close()

    def emitSyms(self):
        ef = elfFile()
        for name in sorted(ef.syms.keys(), key=lambda x: ef.syms[x].addr):
            flag_str = ''
            sym = ef.syms[name]
            # objects(O) in objdump is data
            if 'O' in sym.flags:
                flag_str += 'd'
                # functions are text
            if 'F' in sym.flags:
                flag_str += 't'
                self.imm_f.write('s %s 0x%s %s %s\n' % (name, sym.addr, sym.ali_size, flag_str))

    def emitEntry(self):
        entry_addr = self.imm_fun.addr
        s = 'e %#08x\n' % entry_addr
        self.emitString(s)

    def emitFunction(self):
        # def emitFunction(imm_fun,imm_f,debug_f=None):
        imm_fun = self.imm_fun
        imm_f = self.imm_f
        debug_f = self.debug_f

        emitted_loop_counts = {}

        i_nodes = imm_fun.imm_nodes
        imm_loopheads = imm_fun.imm_loopheads
        # locate the first and last addresses
        first_addr, last_addr = self.firstAndLastAddr()
        print 'first - last addrs : %x-%x' % (first_addr, last_addr)
        size = 4
        to_emit = {}

        # dict of complex loop "head"s to ( addrs in the loop, its bound)
        complex_loops = {}
        # we need to emit instructions in the order of addresses
        # firstly, put all the lines in a dict
        for bb_start_addr in imm_fun.bbs:
            if self.skip_fun and bb_start_addr in self.elf_fun_to_skip.lines:
                continue
            for addr in imm_fun.bbs[bb_start_addr]:
                if addr in imm_loopheads:
                    p_head, f = imm_loopheads[addr]
                    bin_head = phyAddrP(p_head, imm_fun.f_problems[f])
                    import graph_refine.loop_bounds
                    if imm_fun.loaded_loop_counts and bin_head in imm_fun.bin_loops_by_fs[f]:
                        # The user specified a manual loop-count override
                        loop_count, desc, _ = imm_fun.bin_loops_by_fs[f][bin_head]
                    else:

                        print "imm_fun.loaded_loop_counts: %s, bin_loops_by_fs[f].keys: %s, function: %s" % (
                            imm_fun.loaded_loop_counts, str(imm_fun.loops_by_fs[f]), f)
                        assert False
                        loop_count, desc = graph_refine.loop_bounds.get_bound_super_ctxt(bin_head, [])
                    if graph_refine.loop_bounds.is_complex_loop(addr):
                        body_addrs = graph_refine.loop_bounds.get_loop_addrs(addr)
                        complex_loops[addr] = (body_addrs, loop_count)
                    emitted_loop_counts[bin_head] = (loop_count, desc)
                    print '%x: bound %d/0x%x, %s' % (addr, loop_count, loop_count, desc)
                else:
                    loop_count = None
                to_emit[addr] = (addr, addr == bb_start_addr, loop_count)

        for loop_addr in complex_loops.keys():
            print "complex loop at 0x%x" % (addr)
            print "body: %s" % str(map(hex, body_addrs))
            # apply the loopcounts to all the instructions in this complex loop
            body_addrs, loop_bound = complex_loops[loop_addr]
            for addr in body_addrs:
                if addr not in to_emit:
                    # dodge the halt case
                    continue
                addr, is_start_bb, _ = to_emit[addr]
                to_emit[addr] = (addr, is_start_bb, loop_bound)
                emitted_loop_counts[addr] = (loop_bound, "complex_body")

        # then emit them in order
        for addr in xrange(first_addr, last_addr + size, size):
            if addr in to_emit:
                addr, is_start_bb, loop_count = to_emit[addr]
                self.emitImm(addr, i_nodes, is_start_bb, loop_count)
            else:
                # pad with nop
                self.emitNop(addr, size)

        for bin_head in emitted_loop_counts:
            count, desc = emitted_loop_counts[bin_head]
            self.emitted_loop_counts_file.write("0x%x : count %d, desc: %s\n" % (bin_head, count, desc))

    def firstAndLastAddr(self):
        i_addrs = []
        bbs = self.imm_fun.bbs
        for bb_n in bbs:
            i_addrs += bbs[bb_n]
        # print 'chronos_emit i_addrs %s' % i_addrs
        return min(i_addrs, key=int), max(i_addrs, key=int)

    def emitLiterals(self):
        ef = elfFile()
        for addr in sorted(ef.literals, key=int):
            (size, value) = ef.literals[addr]
            self.imm_f.write('v %s %s %d\n' % (hex(addr), value, size))

    def emitLoopcount(self, addr, loop_count):
        self.imm_f.write('l 0x%x %s\n' % (addr, loop_count))
        print 'l 0x%x %s\n' % (addr, loop_count)
        if self.debug_f:
            self.debug_f.write('l 0x%x %s\n' % (addr, loop_count))

    def emitString(self, s):
        self.imm_f.write(s)
        if self.debug_f:
            self.debug_f.write(s)

    def emitNop(self, addr, size):
        s = 'i %s %d startbb edges end nop _ _' % (hex(addr), size)
        if rawVals(addr):
            _, value = rawVals(addr)
            s += ' %s' % hexSansX(value)
        s += '\n'
        self.emitString(s)


    def emitArmImm(self, s, inst, value, txt):
        i = inst
        s += ' ' + i.mnemonic + ' '

        if i.condition:
            s += i.condition + ' '
        else:
            s += '_ '

        if i.setcc:
            s += 's '
        else:
            s += '_ '

        for reg in i.input_registers:
            s += 'input ' + reg + ' '
        for reg in i.output_registers:
            s += 'output ' + reg + ' '
        if hasattr(i, 'shift_val'):
            s += 'shift #' + i.shift_val + ' ' + i.shift_mode + ' '
        if hasattr(i, 'shift_reg'):
            s += 'shift ' + i.shift_reg + ' ' + i.shift_mode + ' '
        # finally the raw inst and the text

        s += '%s ' % hexSansX(value)
        s += '"%s"' % txt
        s += '\n'

        self.emitString(s)


    def emitRVImm(self, s, inst, value, txt):
        s += ' ' + inst.mnemonic + ' '
        for r in inst.input_registers:
            s += 'input ' + r + ' '
        if inst.has_imm:
            s += 'input #' + inst.imm + ' '
        for r in inst.output_registers:
            s += 'output ' + r + ' '

        s += '%s ' % hexSansX(value)
        s += '"%s"' % txt
        s += '\n'
        self.emitString(s)

    def emitImm(self, addr, nodes, is_startbb, loop_count):
        '''
        Emit a single line of imm instruction
        '''

        s = ''
        node = nodes[addr]
        # if this is a loop head, emit its loop count
        if loop_count != None:
            self.emitLoopcount(addr, loop_count)
        if verbose:
            print 'emitting %s: %s' % (addr, node.text)

        # is this the start of a basic block ?
        if is_startbb:
            bb = 'startbb'
        else:
            bb = 'contbb'

        # all insts are of size 4
        s += ('i %s 4 %s' % (hex(addr), bb))

        # output edges
        s += ' edges'
        # types of edges : next, call, callret,tailcall,return
        # call: function call, callret : where to go when call returns ?
        # return: this edge returns
        # tailcall: namesake

        for e in sorted(node.edges, key=lambda x: x.targ):
            if type(e.targ) != int:
                print 'e.targ %s' % e.targ
            if e.emit:
                s += ' next ' + hex(e.targ)
        dummy_call = False
        if node.call_edge:
            assert node.call_ret_edge != None
            if self.skip_fun and node.call_edge.targ in self.elf_fun_to_skip.lines:
                assert not node.is_tail_call
                # skip the function call and go directly to the return site
                s += ' next ' + hex(node.call_ret_edge.targ)
                dummy_call = True
            elif node.is_tail_call:
                s += ' tailcall ' + hex(node.call_edge.targ)
            else:
                s += ' call ' + hex(node.call_edge.targ)
                # print 'call_ret_edge %s ' % node.call_ret_edge.targ
                s += ' callret ' + hex(node.call_ret_edge.targ)
        if node.ret_edge:
            s += ' return'
            assert not node.call_edge
            assert not node.call_ret_edge
            if verbose and node.edges != []:
                print '     node.edges : '
                for x in node.edges:
                    print '       %s ' % x.targ

        s += (' end')
        txt = node.text
        # mnenomic condition setcc, input output etc
        # print '%s: %s' % (addr,txt)
        value = node.raw_inst
        if dummy_call:
            s += ' nop _ _ %s\n' % hexSansX(value)
            self.emitString(s)
            return

        if self.arch == 'armv7':
            i = parser.decode_instruction(addr, value, txt)
            self.emitArmImm(s, i, value, txt)
        elif self.arch == 'rv64':
            i = riscv_parser.decode_instruction(addr, value, txt)
            self.emitRVImm(s, i, value, txt)
        else:
            print 'unsupported arch %s ' % self.arch
            return


def hexSansX(n):
    '''translate the input to a hex without the 0x prefix'''
    s = hex(n)
    return s[2:]
