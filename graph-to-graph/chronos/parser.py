#
# Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

import re

'''
Regular expression based single instruction parsing utility.
Appopriated from previous work for interfacing with Chronos
Ideally, fix me by using a proper parser and/or the arm model.
The regexes are directly copied from Bernard's quoll, particularly machine_arm.py
This file used to be a part of a static execution engine used by Qoull.
'''

'''
The following constants culminate to valid_instruction_re, a regex search pattern, which is used to decipher an instruction mnemonic into the base instruction and all the
possible modifiers that can apply to it.
'''
# These instructions can have the s suffix to set condition codes.
# They are separated to avoid ambiguity from things like "bls".

valid_arith_instructions = (
    # 2 operands:
    'mov', 'mvn',
    'movw',
    'movt',
    'clz',
    'rrx',
    # 3 operands:
    'add', 'adc', 'sub', 'sbc', 'rsb', 'rsc',
    'and', 'orr', 'bic', 'eor',
    'lsl', 'lsr', 'asr', 'ror',
    'mul',
    'smulbb', 'smultb',
    # 4 operands:
    'mla', 'umull', 'umlal', 'smlabb', 'smull', 'smlal',
    'ubfx', 'sbfx', 'bfi', 'bfc',
)

# These instructions cannot have the s suffix.
valid_other_instructions = (
    'push', 'pop',
    'cmp', 'cmn', 'tst', 'teq', 'uxtb', 'uxtab', 'sxtb', 'uxth', 'sxth',
    'str', 'strb', 'strh', 'strd', 'ldr', 'ldrb', 'ldrh', 'ldrd',
    'ldrsh', 'ldrsb',
    'ldrex', 'strex',
    'strt', 'strbt', 'ldrt', 'ldrbt',
    '(?:ldm|stm|srs|rfe|dmb)(?P<dirflags>[di][ba])?',
    'b', 'bl', 'blx', 'bx',
    'mcr', 'mrc', 'mcrr',
    'msr', 'mrs',
    'cps(?P<cpsflags>i[de])?',
    'nop',
    'isb',
    'dsb',
    'swp',
    'vmrs', 'vmsr', 'vstmia', 'vldmia',
    'svc',
)

valid_conditions = (
    '', 'ne', 'eq',
    'cs', 'hs',
    'cc', 'lo',
    'mi', 'pl', 'vs', 'vc', 'hi', 'ls', 'ge', 'lt', 'gt', 'le',
)

valid_instruction_re = re.compile(
    r'''^(?:
            (?P<instruction1>%(arith_instructions)s)
            (?P<setcc>s?)
            (?P<cond1>%(conditions)s) |
            (?P<instruction2>%(other_instructions)s)
            (?P<cond2>%(conditions)s)
        )$''' % {
            'arith_instructions': '|'.join(valid_arith_instructions),
            'other_instructions': '|'.join(valid_other_instructions),
            'conditions': '|'.join(valid_conditions)
        }, re.X)

#
# The following regexes take the arguments of a specific instruction (whose
# form we already know), and extract all the relevant arguments and operands
# from the instruction.

all_registers = (
    'r0', 'r1',  'r2',  'r3',  'r4',  'r5',  'r6',  'r7',
    'r8', 'r9', 'r10', 'r11', 'r12',  'sp',  'lr', 'pc',
    'cc',
    #'mode',
)
aliases = {
    'sl': 'r10',
    'fp': 'r11',
    'ip': 'r12',
    'r13':'sp',
    'r14':'lr',
    'r15':'pc',
}

any_register = r'%s' % ('|'.join(list(all_registers) + aliases.keys()))
ldrstr_args_re = re.compile(
    r'''(?:(?:%(any_register)s),\s*)?
        (?P<target_reg>%(any_register)s),\s*
        \[
        (?P<base_addr_reg>%(any_register)s)\s*
        (?:,\s*
            (?:
                \#(?P<incr_val>-?[0-9]+) |
                (?P<incr_reg>%(any_register)s)\s*
                (?:,\s*
                    (?P<shift_method>lsl|lsr|asr|ror|rrx)\s+
                    \#(?P<shift_amount>[0-9]+)
                )?
            )
        )?
    \]
    (?:
        (?P<writeback> !) |
        ,\s* (?P<writeback_incr_reg>%(any_register)s) |
        ,\s* \#(?P<writeback_incr_amount>-?[0-9]+)
    )?\s*(;.*)?
    $''' % {'any_register' : any_register},
    re.X)

operand2 = r'''(?:
            \#(?P<op2_val>-?[0-9]+) |
            (?:
                (?P<op2_reg>%(any_register)s
                )
                (?:,\s*
                    (?P<shift_method>lsl|lsr|asr|ror|rrx)\s+
                    (?:
                        \#(?P<shift_amount>[0-9]+) |
                        (?P<shift_by_reg>%(any_register)s)
                    )
                )?
            )
        )'''

onereg_and_operand2_re = re.compile(
    (r'''(?P<target_reg>%(any_register)s),\s*''' + operand2 + '(\s*;.*)?$') % {
            'any_register' : any_register},
    re.X)

tworegs_and_operand2_re = re.compile(
    (r'''(?P<target_reg>%(any_register)s),\s*
        (?P<source_reg>%(any_register)s),\s*''' + operand2 + '(\s*;.*)?$') % {
            'any_register' : any_register},
    re.X)



#just used for decoding for us
class ARMInstruction:
    def __init__(self, addr, value, disassembly,
            mnemonic, condition, dirflags, cpsflags, setcc, args):

        self.addr = addr
        self.value = value
        self.disassembly = disassembly

        # Populate member fields with data.
        self.mnemonic = mnemonic
        self.condition = condition
        self.dirflags = dirflags
        self.cpsflags = cpsflags
        self.setcc = setcc
        self.args = args
        self.is_loop_cond = False

        self.output_registers = []
        self.input_registers = []

        if self.setcc:
            self.output_registers.append('cc')

        # decode must be overridden by child classes to work with the specific
        # instructions.
        #self.decode()

    def decode(self):
        raise NotImplementedError


class LoadStoreInstruction(ARMInstruction):
    '''ARM ldr/str[bh] instruction.'''
    def decode(self):
        #print 'args %s' % self.args
        g = ldrstr_args_re.match(self.args)
        assert g is not None
        args = g.groupdict()

        tmp_mnemonic = self.mnemonic
        sign_extend = False
        if tmp_mnemonic[-2:] == 'ex':
            tmp_mnemonic = tmp_mnemonic[:3] + tmp_mnemonic[5:]

        if self.mnemonic[-1] == 't':
            self.mnemonic = self.mnemonic[:-1]

        if len(tmp_mnemonic) == 5:
            assert tmp_mnemonic[-2] == 's'
            sign_extend = True
            # Fudge the mnemonic to something else.
            tmp_mnemonic = tmp_mnemonic[:3] + tmp_mnemonic[-1:]

        if len(tmp_mnemonic) == 4:
            suffix = tmp_mnemonic[-1]
            assert suffix in ('b', 'h')
            if suffix == 'b':
                access_size = 1
            elif suffix == 'h':
                access_size = 2
        else:
            assert len(tmp_mnemonic) == 3
            access_size = 4

        if tmp_mnemonic.startswith('ldr'):
            load = True
        else:
            assert tmp_mnemonic.startswith('str')
            load = False

        # Special handling for switch statements.
        #  if tmp_mnemonic == 'ldr' and args['target_reg'] == 'pc' and \
        #        self.condition == 'ls':
        #    decode_as_switch = True
        #else:
        #    decode_as_switch = False

        # Record input and output registers.
        # if load:
        self.output_registers.append(args['target_reg'])
            #self.input_registers.append('memory')
        # else:
        #    self.input_registers.append(args['target_reg'])
            #self.output_registers.append('memory')
        self.input_registers.append(args['base_addr_reg'])
        if args['incr_reg']:
            self.input_registers.append(args['incr_reg'])
        if args['incr_val']:
            self.input_registers.append('#' + args['incr_val'])
        if args['writeback_incr_reg']:
            self.input_registers.append(args['writeback_incr_reg'])
        #if args['writeback'] or \
        #        args['writeback_incr_reg'] or args['writeback_incr_amount']:
            #self.output_registers.append(args['base_addr_reg'])
        if args['writeback_incr_amount']:
            self.input_registers.append('#' + args['writeback_incr_amount'])
        if args.get('shift_by_reg') != None:
            self.shift_reg = args['shift_by_reg']
        if args.get('shift_amount') != None:
            self.shift_val = args['shift_amount']
        if args.get('shift_method') != None:
            self.shift_mode = args['shift_method']


class LoadStoreMultipleInstruction(ARMInstruction):
    '''ARM ldm*/stm* instruction.'''
    def decode(self):
        # Default direction.
        increment = +4
        after = True
        #strip everything after the ;, if any
        self.args = self.args.split(';',1)[0]
        addr_reg, reg_list = [x.strip() for x in self.args.split(',', 1)]
        writeback = addr_reg[-1] == '!'
        if writeback:
             self.output_registers.append('writeback')
             addr_reg = addr_reg.rstrip('!')
        #    self.output_registers.append(addr_reg)
        # self.input_registers.append(addr_reg)

        if reg_list[-1] == '^':
            # Saving/copying user-mode registers.
            # TODO: We didn't think of that! It doesn't matter too much
            # hopefully. But we should at least warn the user.
            reg_list = reg_list.rstrip('^')
        assert reg_list[0] == '{'
        assert reg_list[-1] == '}'

        rw_regs = reg_list.strip('{}')
        rw_regs = [x.strip() for x in rw_regs.split(',')]

        if self.dirflags is not None:
            if self.dirflags[0] == 'i':
                increment = +4
            elif self.dirflags[0] == 'd':
                increment = -4
                rw_regs.reverse()
            else:
                assert False, "Invalid direction flag (%s). Wanted i or d." % (
                    self.dirflags[0])
            if self.dirflags[1] == 'a':
                after = True
            elif self.dirflags[1] == 'b':
                after = False
            else:
                assert False, \
                    "Invalid after/before flag (%s). Wanted a or b." % (
                        self.dirflags[0])

        if self.mnemonic == 'ldm':
            load = True
            self.output_registers.extend(rw_regs)
            self.input_registers.append(addr_reg)
        #    self.input_registers.append('memory')
        elif self.mnemonic == 'stm':
            load = False
            self.input_registers.extend(rw_regs)
            self.output_registers.append(addr_reg)
        #    self.output_registers.append('memory')
        else:
            assert False, "Not an ldm/stm"

class PushPopInstruction(LoadStoreMultipleInstruction):
    def decode(self):
        # Translate us into a ldm/stm instruction.
        if self.mnemonic == 'push':
            self.mnemonic = 'stm'
            self.dirflags = 'db'
            self.args = 'sp!, %s' % (self.args)
        elif self.mnemonic == 'pop':
            self.mnemonic = 'ldm'
            self.dirflags = 'ia'
            self.args = 'sp!, %s' % (self.args)
        else:
            assert False, "Expected a push/pop to be a push or pop! Not %s" % (
                self.mnemonic)

        LoadStoreMultipleInstruction.decode(self)

class ArithmeticInstruction(ARMInstruction):
    '''ARM arithmetic instruction with 3 arguments and the result is stored
    in the first argument.'''
    def decode(self):
        g = tworegs_and_operand2_re.match(self.args)
        assert g is not None, "Failed to match op2: %s" % self.args

        args = g.groupdict()

        # Record input and output registers.
        self.output_registers.append(args['target_reg'])
        self.input_registers.append(args['source_reg'])
        if args['op2_reg'] is not None:
            self.input_registers.append(args['op2_reg'])
        if args['op2_val'] is not None:
            self.input_registers.append('#' + args['op2_val'])

        if args.get('shift_by_reg') != None:
            self.shift_reg = args['shift_by_reg']
        if args.get('shift_amount') != None:
            self.shift_val = args['shift_amount']
        if args.get('shift_method') != None:
            self.shift_mode = args['shift_method']

class RotateRighteXtendInstruction(ArithmeticInstruction):
    '''rrx - two arguments only.'''

    def decode(self):
        g = onereg_and_operand2_re.match(self.args)
        assert g is not None, "Failed to match op2: %s" % self.args

        args = g.groupdict()

        # Record input and output registers.
        self.output_registers.append(args['target_reg'])
        if args['op2_reg'] is not None:
            self.input_registers.append(args['op2_reg'])
        if args['op2_val'] is not None:
            self.input_registers.append('#' + args['op2_val'])

        if args.get('shift_by_reg') != None:
            self.shift_reg = args['shift_by_reg']
        if args.get('shift_amount') != None:
            self.shift_val = args['shift_amount']
        if args.get('shift_method') != None:
            self.shift_mode = args['shift_method']


class MoveInstruction(ARMInstruction):
    '''ARM move instruction with 2 arguments and the result is stored
    in the first argument.'''
    def decode(self):
        g = onereg_and_operand2_re.match(self.args)
        assert g is not None
        args = g.groupdict()

        # Record input and output registers.
        self.output_registers.append(args['target_reg'])
        if args['op2_reg'] is not None:
            self.input_registers.append(args['op2_reg'])
        if args['op2_val'] is not None:
            self.input_registers.append('#' + args['op2_val'])

class HalfMoveInstruction(ARMInstruction):
    '''ARM halfmove instruction (movt/movw).'''
    def decode(self):
        assert self.mnemonic in ('movt', 'movw')
        top_half = self.mnemonic[-1] == 't'

        dst_reg, imm = [x.strip() for x in self.args.split(',')]
        assert imm[0] == '#'

        # Record input and output registers.
        self.output_registers.append(dst_reg)
        self.input_registers.append(imm)
        if top_half:
            # We preserve the lower 16 bits of this.
            self.input_registers.append(dst_reg)

        imm = int(imm[1:])

class CompareInstruction(ARMInstruction):
    '''ARM comparison instruction with 2 arguments and the result is stored
    in the first argument.'''
    def decode(self):
        g = onereg_and_operand2_re.match(self.args)
        assert g is not None
        args = g.groupdict()

        # Record input and output registers.
        self.output_registers.append('cc')
        # "target_reg" is a misnomer here.
        self.input_registers.append(args['target_reg'])
        if args['op2_reg'] is not None:
            self.input_registers.append(args['op2_reg'])
        if args['op2_val'] is not None:
            self.input_registers.append('#' + args['op2_val'])

        if args.get('shift_by_reg') != None:
            self.shift_reg = args['shift_by_reg']
        if args.get('shift_amount') != None:
            self.shift_val = args['shift_amount']
        if args.get('shift_method') != None:
            self.shift_mode = args['shift_method']

class BranchInstruction(ARMInstruction):
    '''Nothing we(felix) need from this, just a dummy'''
    def decode(self):
        return


class IndirectBranchInstruction(ARMInstruction):
    def decode(self):
        reg = self.args
        self.input_registers.append(reg)
        self.output_registers.append('pc')

class ReturnFromExceptionInstruction(ARMInstruction):
    '''Implement rfe.'''
    def decode(self):
        pass

class NopInstruction(ARMInstruction):
    '''Implement the ARM nop instruction.'''
    def decode(self):
        # We do nothing!
        pass

class UnhandledInstruction(NopInstruction):
    # Treat unhandled instructions like a nop.
    def decode(self):
        NopInstruction.decode(self)
        print 'Unhandled instruction "%s" at %#x' % (self.mnemonic, self.addr)

class MRCInstruction(ARMInstruction):
    '''Provide a dummy implementation of the ARM mrc instruction.'''
    def decode(self):
        # Effectively a nop.
        cp, op2, reg, cp0, cp1, op1 = [x.strip() for x in self.args.split(',')]
        self.reg = reg

        self.output_registers.append(reg)


class MCRInstruction(ARMInstruction):
    '''Provide a dummy implementation of the ARM mcr instruction.'''
    def decode(self):
        # Effectively a nop.
        cp, op2, reg, cp0, cp1, op1 = [x.strip() for x in self.args.split(',')]
        self.reg = reg

        self.input_registers.append(reg)


class BitFieldExtractInstruction(ARMInstruction):
    '''Implement ARM's ubfx/sbfx instruction.'''

    def decode(self):
        assert self.mnemonic in ('ubfx', 'sbfx')
        sign_extend = (self.mnemonic[0] == 's')

        dst_reg, src_reg, start_bit, bit_length = [x.strip() for x in self.args.split(',')]
        assert start_bit[0] == '#'
        assert bit_length[0] == '#'
        start_bit = int(start_bit[1:])
        bit_length = int(bit_length[1:])

        # Record input and output registers.
        self.output_registers.append(dst_reg)
        self.input_registers.append(src_reg)

class SignExtendInstruction(ARMInstruction):
    '''Implement ARM's [us]xt[bh] instruction.'''
    def decode(self):
        assert self.mnemonic in ('uxtb', 'sxtb', 'uxth', 'sxth')
        #src_size = (self.mnemonic[-1]) # b or h
        #sign_extend = (self.mnemonic[0] == 's')

        dst_reg, src_reg = [x.strip() for x in self.args.split(',')]

        # Record input and output registers.
        self.output_registers.append(dst_reg)
        self.input_registers.append(src_reg)

mnemonic_groups_to_class_map = {
    ('ldr', 'str',
     'ldrb', 'ldrsb', 'strb',
     'ldrh', 'ldrsh', 'strh',
     'ldrex', 'strex',
     'ldrbt', 'strbt'): LoadStoreInstruction,
    ('ldm', 'stm'): LoadStoreMultipleInstruction,
    ('push', 'pop'): PushPopInstruction,
    ('add', 'adc', 'sub', 'sbc', 'rsb', 'rsc',
     'and', 'orr', 'bic', 'eor',
     'lsl', 'lsr', 'asr', 'ror',
     'mul'): ArithmeticInstruction,
    ('rrx',): RotateRighteXtendInstruction,
    ('mov', 'mvn'): MoveInstruction,
    ('movt', 'movw'): HalfMoveInstruction,
    ('nop',): NopInstruction,
    ('cmp', 'cmn', 'tst', 'teq'): CompareInstruction,
    ('b', 'bl'): BranchInstruction,
    ('bx', 'blx'): IndirectBranchInstruction,
    ('rfe',): ReturnFromExceptionInstruction,
    ('mrc',): MRCInstruction,
    ('mcr',): MCRInstruction,
    ('ubfx', 'sbfx'): BitFieldExtractInstruction,
    ('uxtb', 'sxtb', 'uxth', 'sxth'): SignExtendInstruction,
    #('bfi',): BitFieldInsertInstruction,
    #('bfc',): BitFieldClearInstruction,

    # Instructions that we can just treat as nops for now (FIXME)
    ('cps', 'mcrr', 'isb', 'dsb'): NopInstruction,

    # Don't bother simulating VFP
    ('vmrs', 'vmsr', 'vstmia', 'vldmia'): NopInstruction,

    # FIXME
    ('swp', 'svc'): NopInstruction,
}

# Convert above into mnemonic -> class map.
mnemonic_to_class_map = dict([(m, c)
        for ms, c in mnemonic_groups_to_class_map.iteritems()
        for m in ms])

def decode_instruction(addr, value, decoding):
    decoding = decoding.strip()
    bits = decoding.split(None, 1)
    if len(bits) == 1:
        instruction, args = bits[0], []
    else:
        instruction, args = bits

    g = valid_instruction_re.match(instruction)
    if g is None:
        raise FatalError("Unknown instruction %s at address %#x" % (instruction, addr))

    # Extract relevant data from re match groups.
    instruction = g.group('instruction1')
    if instruction is None:
        instruction = g.group('instruction2')

    condition = g.group('cond1')
    if condition is None:
        condition = g.group('cond2')

    dirflags = g.group('dirflags')
    cpsflags = g.group('cpsflags')
    setcc = g.group('setcc') == 's'

    # Trim trailing "ia/fd/etc..." suffixes.
    if dirflags is not None:
        instruction = instruction[:-len(dirflags)]
    if cpsflags is not None:
        instruction = instruction[:-len(cpsflags)]
    #print 'instruction :' + instruction
    cls = mnemonic_to_class_map.get(instruction, UnhandledInstruction)
    #print '%s: %s \n    instruction %s \n   condition %s\n    dirflags %s\n     cpsflags %s\n    setcc %s\n      args %s\n' % (addr,decoding, instruction,condition,dirflags,cpsflags,setcc,args)

    arm_inst = cls(addr, value, decoding,
        instruction, condition, dirflags, cpsflags, setcc, args)
    arm_inst.decode()

    mnemonic = arm_inst.mnemonic
    condition = arm_inst.condition
    dirflags = arm_inst.dirflags
    cpsflags = arm_inst.cpsflags
    setcc = arm_inst.setcc
    #args = arm_inst.args
    output_registers = arm_inst.output_registers
    input_registers = arm_inst.input_registers
    return arm_inst
