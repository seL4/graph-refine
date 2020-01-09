import re

pass
'''
Generate input file for RISCV Chronos

Working in progress

Regular expression based single instruction parsing utility.
Appopriated from previous work for interfacing with Chronos

Pleae do not blame the author for the madness if you have headaches
when reading this. So is the Chronos code.

'''

'''
The following constants culminate to valid_instruction_re, a regex search pattern,
which is used to decipher an instruction mnemonic into the base instruction and all
the possible modifiers that can apply to it.
'''

# set rd = imm
rd_imm = (
    'lui',
    'addpc',
    'jal',      # rd = pc + 4; pc = pc + offset; but use the absolute offset
)

zero_oprand = (
    'fence.i',
    'wfi',
    'nop'
)

imm_only = (
    'j',        # j #offset
)
# rd = rs1 some are pseudo instructions, but that does not matter
rd_rs1 = (
    'mv',
    'sfence.mva',
)

# rd = op rs2
rd_rs2 = (
    'neg',
    'negw',
)

# rd =  some op using rs1 and imm
rd_rs1_imm = (
    'lb',
    'lh',
    'lw',
    'lwu',
    'ld',
    'lbu',
    'lhu',
    'addi',  # rd = rs1 + imm
    'slti',
    'xori',
    'ori',
    'andi',
    'addiw',
    'slli',
    'slliw',
    'srli',
    'srliw',
    'srai',
    'sraiw',
    'not',      # not rd, rs1 == xori rd, rs1, #-1
    'sext.w',   # sext.w rd, rs1 == addiw rd, rs1, #0
    'seqz',     # seqz rd, rs1 == sltiu rd, rs1, #1
    'jalr',     # rd = pc + 4; pc = (rs1 + imm) * 2
    'ret',      # ret == jalr x0, 0(x1)
)

# ops using rs1, rs2, and imm
rs1_rs2_imm = (
    'sb',   # u8[rs1 + imm] = rs2
    'sh',
    'sw',
    'st',
    'beq',  # fi rs1 == rs2 pc = pc + imm
    'bne',
)

# ops using rd = rs1 op rs2
rd_rs1_rs2 = [
    'add',
    'addw',
    'sub',
    'subw',
    'sll',
    'sllw',
    'slt',
    'sltu',
    'xor',
    'srl',
    'srlw',
    'sra',
    'sraw',
    'or',
    'mul',
    'mulw',
    'mulh',
    'mulhsu',
    'mulhu',
    'div',
    'divw',
    'divu',
    'divuw',
    'rem',
    'remu',
    'remw',
    'remuw',
    'sltz',    # sltz rd, rs1 == slt rd, rs1, x0
    'sgtz',    # sgtz rd, rs2 == slt rd, x0, rs2
]

csr = (
    'csrrw',
    'csrrs',
    'csrrc',
    'csrrwi',
    'csrrsi',
    'csrrci',
    'csrr',
    'csrw',
    'csrs',
    'csrc',
)

all_registers = (
    'x0', 'x1',
    'x2', 'x3',
    'x4', 'x5',
    'x6', 'x7',
    'x8', 'x9',
    'x10','x11',
    'x12','x13',
    'x14','x15',
    'x16','x17',
    'x18','x19',
    'x20','x21',
    'x22','x23',
    'x24','x25',
    'x26','x27',
    'x28','x29',
    'x30','x31',
    'pc'
)

aliases = {
    'zero': 'x0',
    'ra': 'x1',
    'sp': 'x2',
    'gp': 'x3',
    'tp': 'x4',
    't0': 'x5',
    't1': 'x6',
    't2': 'x7',
    'fp': 'x8',
    's0': 'x8',
    's1': 'x9',
    'a0': 'x10',
    'a1': 'x11',
    'a2': 'x12',
    'a3': 'x13',
    'a4': 'x14',
    'a5': 'x15',
    'a6': 'x16',
    'a7': 'x17',
    's2': 'x18',
    's3': 'x19',
    's4': 'x20',
    's5': 'x21',
    's6': 'x22',
    's7': 'x23',
    's8': 'x24',
    's9': 'x25',
    's10': 'x26',
    's11': 'x27',
    't3':  'x28',
    't4': 'x29',
    't5': 'x30',
    't6': 'x31'
}

csrs = (
    'sstatus',
    'stvec',
    'sip',
    'sie',
    'scounteren',
    'sscratch',
    'sepc',
    'scause',
    'stval',
    'satp',
)

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



class RVInstruction:
    def __init__(self, addr, value, disassembly,
                 mnemonic, args):

        self.rd = ''
        self.rs1 = ''
        self.rs2 = ''
        self.imm = ''

        self.addr = addr
        self.value = value
        self.disassembly = disassembly

        # Populate member fields with data.
        self.mnemonic = mnemonic
        self.args = args
        self.is_loop_cond = False

        self.output_registers = []
        self.input_registers = []

    def decode(self):
        raise NotImplementedError


class RdImm(RVInstruction):
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

class ZeroOprand(RVInstruction):
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

class ImmOnly(RVInstruction):
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


class RdRs1(RVInstruction):
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

class RdRs2(RVInstruction):
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

class RdRs1Imm(RVInstruction):
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

class Rs1Rs2Imm(RVInstruction):
    '''Nothing we(felix) need from this, just a dummy'''
    def decode(self):
        return


class RdRs1Rs2(RVInstruction):
    def decode(self):
        reg = self.args
        self.input_registers.append(reg)
        self.output_registers.append('pc')

class CSR(RVInstruction):
    '''Implement rfe.'''
    def decode(self):
        pass

class UnhandledInstruction(RVInstruction):
    # Treat unhandled instructions like a nop.
    def decode(self):
        NopInstruction.decode(self)
        print 'Unhandled instruction "%s" at %#x' % (self.mnemonic, self.addr)

def decode_instruction(addr, value, decoding):
    decoding = decoding.strip()
    bits = decoding.split(None, 1)
    if len(bits) == 1:
        instruction, args = bits[0], []
    else:
        instruction, args = bits

    # original
    oi = instruction
    print instruction

    if oi in rd_imm:
        cls = RdImm
    elif oi in zero_oprand:
        cls = ZeroOprand
    elif oi in imm_only:
        cls = ImmOnly
    elif oi in rd_rs1:
        cls = RdRs1
    elif oi in rd_rs2:
        cls = RdRs2
    elif oi in rd_rs1_imm:
        cls = RdRs1Imm
    elif oi in rs1_rs2_imm:
        cls = Rs1Rs2Imm
    elif oi in rd_rs1_rs2:
        cls = RdRs1Rs2
    elif oi in csr:
        cls = CSR
    else:
        print "unsopported instructions %s" % oi
        assert False


    print '%s %s' % (instruction, cls)
    inst = cls(addr, value, decoding, instruction,args)

    inst.decode()

    mnemonic = inst.mnemonic
    output_registers = inst.output_registers
    input_registers = inst.input_registers
    return inst
