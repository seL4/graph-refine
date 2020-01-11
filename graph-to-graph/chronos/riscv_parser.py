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

rs1_imm = {
    'beqz',
    'bltz',
    'bgez',
}

rs2_imm = {
    'blez',
    'bgtz',
}

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
    'blt',
    'bltu',
    'bge',
    'bgeu',
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

def is_hex(imm):
    if imm[0] == '0' and imm[1] == 'x':
        return True
    for c in imm:
        if c in ['a', 'A', 'b', 'B', 'c', 'C', 'd', 'D', 'e', 'E', 'f', 'F']:
            return True

    return False


def to_int(imm):
    try:
        if is_hex(imm):
            return int(imm, base = 16)
        else:
            return int(imm)
    except:
        print 'fail to convert %s' % imm
        raise

def valid_gp_reg(reg):
    return reg in all_registers or reg in list(aliases.keys())

class RVInstruction:
    def __init__(self, addr, value, disassembly, mnemonic, args):
        self.rd = ''
        self.rs1 = ''
        self.rs2 = ''
        self.imm = ''
        self.imm_val = 0

        self.rd_csr = ''
        self.rs_csr = ''

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
        print 'args %s' % self.args
        fields = self.args.split(',')
        assert len(fields) == 2

        self.rd = fields[0].strip()
        assert valid_gp_reg(self.rd)
        self.imm = fields[1].strip()
        self.imm_val = to_int(self.imm)
        self.output_registers.append(self.rd)


class ZeroOprand(RVInstruction):
    def decode(self):
        pass

class ImmOnly(RVInstruction):
    def decode(self):
        self.imm = self.args.strip()
        self.imm_val = to_int(self.imm)

class RdRs1(RVInstruction):
    def decode(self):
        fs = self.args.split(',')
        assert len(fs) == 2
        self.rd = fs[0].strip()
        self.rs1 = fs[1].strip()
        assert valid_gp_reg(self.rd) and valid_gp_reg(self.rs1)
        self.output_registers.append(self.rd)
        self.input_registers.append(self.rs1)

class RdRs2(RVInstruction):
    def decode(self):
        fs = self.args.split(',')
        assert len(fs) == 2
        self.rd = fs[0].strip()
        self.rs2 = fs[1].strip()
        assert valid_gp_reg(self.rd) and valid_gp_reg(self.rs2)
        self.output_registers.append(self.rd)
        self.input_registers.append(self.rs2)

class RdRs1Imm(RVInstruction):
    def decode(self):
        fs = self.args.split(',')
        l = len(fs)
        assert l == 2 or l == 3

        '''
		if length is 2 we have the form:
			ld a1,64(a4)
		if the length is 3, the form:
			addi s0,sp,640
		'''
        if l == 2:
            self.rd = fs[0].strip()
            fs[1] = fs[1].strip()
            left = fs[1].find('(')
            right = fs[1].find(')')
            assert left != -1 and right != -1
            self.imm = fs[1][0:left]
            self.imm_val = to_int(self.imm)
            self.rs1 = fs[1][left + 1 : right]
            self.output_registers.append(self.rd)
            assert valid_gp_reg((self.rs1))

        if l == 3:
            self.rd = fs[0].strip()
            self.rs1 = fs[1].strip()
            self.imm = fs[2].strip()
            self.imm_val = to_int(self.imm)
            self.input_registers.append(self.rs1)
            self.output_registers.append(self.rd)

class Rs1Imm(RVInstruction):
    def decode(self):
        fs = self.args.split(',')
        assert len(fs) == 2
        self.rs1 = fs[0].strip()
        self.imm = fs[1].strip()
        self.imm_val = to_int(self.imm)
        self.input_registers.append(self.rs1)
        assert valid_gp_reg(self.rs1)

class Rs2Imm(RVInstruction):
    def decode(self):
        fs = self.args.split(',')
        assert len(fs) == 2
        self.rs2 = fs[0].strip()
        self.imm = fs[1].strip()
        self.imm_val = to_int(self.imm)
        self.input_registers.append(self.rs2)
        assert valid_gp_reg(self.rs2)

class Rs1Rs2Imm(RVInstruction):
    def decode(self):
        fs = self.args.split(',')
        l = len(fs)
        assert l == 2 or l == 3

        if l == 2:
            self.rs2 = fs[0]
            fs[1] = fs[1].strip()
            left = fs[1].find('(')
            right = fs[1].find(')')
            assert left != -1 and right != -1
            self.imm = fs[1][0:left]
            self.imm_val = to_int(self.imm)
            self.rs1 = fs[1][left + 1 : right]

        if l == 3:
            self.rs1 = fs[0].strip()
            self.rs2 = fs[1].strip()
            self.imm = fs[2].strip()
            self.imm_val = to_int(self.imm)

        assert valid_gp_reg(self.rs1) and valid_gp_reg(self.rs2)

class RdRs1Rs2(RVInstruction):
    def decode(self):
        fs = self.args.split(',')
        assert len(fs) == 3
        self.rd = fs[0].strip()
        self.rs1 = fs[1].strip()
        self.rs2 = fs[2].strip()
        assert valid_gp_reg(self.rd)
        assert valid_gp_reg(self.rs1)
        assert valid_gp_reg(self.rs2)
        self.input_registers.append(self.rs1)
        self.input_registers.append(self.rs2)
        self.output_registers.append(self.rd)


class CSR(RVInstruction):
    def decode(self):
        fs = self.args.split(',')
        if self.mnemonic in ['csrrw', 'csrrs', 'csrrc']:
            self.rd = fs[0].strip()
            self.rd_csr = self.rs_csr = fs[1].strip()
            self.rs1 = fs[2].strip()
            pass
        if self.mnemonic in ['csrwi']:
            self.rd_csr = fs[0].strip()
            self.imm = fs[1].strip()
            self.imm_val = to_int(self.imm)
            self.output_registers.append(self.rd_csr)
            assert self.rd_csr in csrs
        if self.mnemonic in ['csrrsi', 'csrrci']:
            self.rd = fs[0].strip()
            self.rs_csr = self.rd_csr = fs[1].strip()
            self.imm = fs[2].strip()
            self.imm_val = to_int(self.imm)
            self.output_registers.append(self.rd)
            self.output_registers.append(self.rd_csr)
            self.input_registers.append(self.rs_csr)
            assert valid_gp_reg(self.rd)
            assert self.rd_csr in csrs
        if self.mnemonic in ['csrr']:
            self.rd = fs[0].strip()
            self.rd_csr = fs[1].strip()
            assert valid_gp_reg(self.rd)
            assert self.rd_csr in csrs
        if self.mnemonic in ['csrw', 'csrc', 'csrs']:
            self.rd = fs[0].strip()
            self.rd_csr = self.rs_csr = fs[1].strip()
            self.rs1 = fs[2].strip()
            assert valid_gp_reg(self.rd)
            assert valid_gp_reg(self.rs1)
            assert self.rd_csr in csrs
            assert self.rs_csr in csrs
            self.output_registers.append(self.rd)
            self.output_registers.append(self.rd_csr)
            self.input_registers.append(self.rs1)
            self.input_registers.append(self.rs_csr)
        if self.mnemonic in ['csrwi', 'csrsi', 'csrci']:
            self.rd_csr = fs[0].strip()
            self.imm = fs[1].strip()
            self.imm_value = to_int(self.imm)
            assert self.rd_csr in csrs
            self.output_registers.append(self.rd_csr)

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
    elif oi in rs1_imm:
        cls = Rs1Imm
    elif oi in rs2_imm:
        cls = Rs2Imm
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
