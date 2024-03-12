"""
Represents the instruction set
"""

class Reg:
    """Constants to represent registers"""
    # ABI names
    zero = 0
    ra = 1
    sp = 2
    gp = 3
    tp = 4
    t0 = 5
    t1 = 6
    t2 = 7
    s0 = 8
    fp = 8
    s1 = 9
    a0 = 10
    a1 = 11
    a2 = 12
    a3 = 13
    a4 = 14
    a5 = 15
    a6 = 16
    a7 = 17
    s2 = 18
    s3 = 19
    s4 = 20
    s5 = 21
    s6 = 22
    s7 = 23
    s8 = 24
    s9 = 25
    s10 = 26
    s11 = 27
    t3 = 28
    t4 = 29
    t5 = 30
    t6 = 31
    # Register names
    x0 = 0
    x1 = 1
    x2 = 2
    x3 = 3
    x4 = 4
    x5 = 5
    x6 = 6
    x7 = 7
    x8 = 8
    x9 = 9
    x10 = 10
    x11 = 11
    x12 = 12
    x13 = 13
    x14 = 14
    x15 = 15
    x16 = 16
    x17 = 17
    x18 = 18
    x19 = 19
    x20 = 20
    x21 = 21
    x22 = 22
    x23 = 23
    x24 = 24
    x25 = 25
    x26 = 26
    x27 = 27
    x28 = 28
    x29 = 29
    x30 = 30
    x31 = 31

class Rtype:
    """R-type instructions"""
    def __init__(self, instr):
        self.func7 = instr.bin >> 25
        self.rs2 = (instr.bin >> 20) & 31
        self.rs1 = (instr.bin >> 15) & 31
        self.func3 = (instr.bin >> 12) & 7
        self.rd = (instr.bin >> 7) & 31
        self.opcode = instr.bin & 63

class Itype:
    """I-type instructions"""
    def __init__(self, instr):
        self.imm_11_0 = instr.bin >> 20
        self.rs1 = (instr.bin >> 15) & 31
        self.func3 = (instr.bin >> 12) & 7
        self.rd = (instr.bin >> 7) & 31
        self.opcode = instr.bin & 63
        sext = ((self.imm_11_0 >> 11) & 0xfffff) << 12
        self.imm = sext | self.imm_11_0

class Stype:
    """S-type instructions"""
    def __init__(self, instr):
        self.imm_15_5 = instr.bin >> 25
        self.rs2 = (instr.bin >> 20) & 31
        self.rs1 = (instr.bin >> 15) & 31
        self.func3 = (instr.bin >> 12) & 7
        self.imm_4_0 = (instr.bin >> 7) & 31
        self.opcode = instr.bin & 63
        imm = (self.imm_15_5 << 5) | self.imm_4_0
        sext = ((imm >> 15) & 0xffff) << 16
        self.imm = sext | imm

class Btype:
    """B-type instructions"""
    def __init__(self, instr):
        self.imm_12 = instr.bin >> 31
        self.imm_10_5 = (instr.bin >> 25) & 0x3f
        self.rs2 = (instr.bin >> 20) & 31
        self.rs1 = (instr.bin >> 15) & 31
        self.func3 = (instr.bin >> 12) & 7
        self.imm_4_1 = (instr.bin >> 1) & 15
        self.imm_11 = (instr.bin >> 7) & 1
        self.opcode = instr.bin & 63
        imm = (self.imm_12 << 12) | (self.imm_11 << 11) \
            | (self.imm_10_5 << 5) | (self.imm_4_1 << 1)
        sext = ((imm >> 12) & 0x7ffff) << 13
        self.imm = sext | imm

class Utype:
    """U-type instructions"""
    def __init__(self, instr):
        self.imm_31_12 = instr.bin >> 12
        self.imm_4_0 = (instr.bin >> 7) & 31
        self.rd = (instr.bin >> 7) & 31
        self.opcode = instr.bin & 63
        self.imm = self.imm_31_12 << 12

class Jtype:
    """J-type instructions"""
    def __init__(self, instr):
        self.imm_20 = instr.bin >> 31
        self.imm_10_1 = (instr.bin >> 21) & 0x3ff
        self.imm_11 = (instr.bin >> 20) & 1
        self.imm_19_12 = (instr.bin >> 12) & 0xff
        self.rd = (instr.bin >> 7) & 31
        self.opcode = instr.bin & 63
        imm = (self.imm_20 << 20) | (self.imm_19_12 << 12) \
            | (self.imm_11 << 11) | (self.imm_10_1 << 1)
        sext = ((self.imm_20) & 0x3ff) << 21
        self.imm = sext | imm

class MOItype:
    """Memory ordering instructions"""
    def __init__(self, instr):
        self.fm = instr.bin >> 28
        self.PI = (instr.bin >> 27) & 1
        self.PO = (instr.bin >> 26) & 1
        self.PR = (instr.bin >> 25) & 1
        self.PW = (instr.bin >> 24) & 1
        self.SI = (instr.bin >> 23) & 1
        self.SO = (instr.bin >> 22) & 1
        self.SR = (instr.bin >> 21) & 1
        self.SW = (instr.bin >> 20) & 1
        self.rs1 = (instr.bin >> 15) & 31
        self.func3 = (instr.bin >> 12) & 7
        self.rd = (instr.bin >> 7) & 31
        self.opcode = instr.bin & 63

class CRtype:
    """Compressed register"""
    def __init__(self, instr):
        self.funct4 = instr.bin >> 12
        r = (instr.bin >> 7) & 31
        self.rs2 = (instr.bin >> 2) & 31
        self.op = instr.bin & 3
        self.rs1 = r
        if instr.base() in CRtype.regreg:
            self.rd = r

    control = ['C.JR', 'C.JALR']
    regreg = ['C.MV', 'C.ADD']

class CItype:
    """Compressed immediate"""
    def __init__(self, instr):
        self.funct3 = instr.bin >> 13
        r = (instr.bin >> 7) & 31
        self.op = instr.bin & 3
        base = instr.base()
        if base == 'C.LUI/C.ADDI16SP':
            if r == Reg.sp:
                base = 'C.ADDI16SP'
            else:
                base = 'C.LUI'
        if base in CItype.SPload + CItype.constgen:
            self.rd = r
        if base in CItype.SPload:
            self.rs1 = Reg.sp
            self.offset = CItype.offset[base](instr.bin)
        if base == 'C.LI':
            self.imm = CItype.imm(instr.bin)
        if base == 'C.LUI':
            self.nzimm = CItype.imm(instr.bin) << 12
        if base in CItype.regimm:
            self.rd = r
            self.rs1 = r
        if base == 'C.ADDI':
            self.nzimm = CItype.imm(instr.bin)
        if base == 'C.ADDIW':
            self.imm = CItype.imm(instr.bin)
        if base == 'C.ADDI16SP':
            self.nzimm = CItype.immsp(instr.bin)
        if base == 'C.SLL':
            self.shamt = CItype.imm(instr.bin)

    SPload = ['C.LWSP', 'C.LDSP', 'C.LQSP', 'C.FLWSP', 'C.FLDSP']
    constgen = ['C.LI', 'C.LUI']
    regimm = ['C.ADDI', 'C.ADDIW', 'C.ADDI16SP', 'C.SLLI']

    Woffset = lambda i: (((i >> 12) & 1) << 5) | (((i >> 4) & 7) << 2) \
        | (((i >> 2) & 3) << 6)
    Doffset = lambda i: (((i >> 12) & 1) << 5) | (((i >> 5) & 3) << 3) \
        | (((i >> 2) & 7) << 6)
    Qoffset = lambda i: (((i >> 12) & 1) << 5) | (((i >> 6) & 1) << 4) \
        | (((i >> 2) & 15) << 6)
    imm = lambda i: (((i >> 12) & 1) << 5) | ((i >> 2) & 31)
    immsp = lambda i: (((i >> 12) & 1) << 9) | (((i >> 6) & 1) << 4) \
        | (((i >> 5) & 1) << 6) | (((i >> 3) & 3) << 7) \
        | (((i >> 2) & 1) << 5)

    offset = {
        'C.LWSP': Woffset,
        'C.LDSP': Doffset,
        'C.LQSP': Qoffset,
        'C.FLWSP': Woffset,
        'C.FLDSP': Doffset,
    }

class CSStype:
    """Compressed stack-relative store"""
    def __init__(self, instr):
        self.funct3 = instr.bin >> 13
        self.rs1 = Reg.sp
        self.rs2 = (instr.bin >> 2) & 31
        self.op = instr.bin & 3
        self.offset = CSStype.offset[instr.base()](instr.bin)

    Woffset = lambda i: (((i >> 9) & 15) << 2) | (((i >> 7) & 3) << 6)
    Doffset = lambda i: (((i >> 10) & 7) << 3) | (((i >> 7) & 7) << 6)
    Qoffset = lambda i: (((i >> 11) & 3) << 4) | (((i >> 7) & 15) << 6)

    offset = {
        'C.SWSP': Woffset,
        'C.SDSP': Doffset,
        'C.SQSP': Qoffset,
        'C.FSWSP': Woffset,
        'C.FSDSP': Doffset,
    }

class CIWtype:
    """Compressed wide immediate"""
    def __init__(self, instr):
        i = instr.bin
        self.funct3 = i >> 13
        rd_ = (i >> 2) & 7
        self.rd = rd_ + 8
        self.op = i & 3
        self.nzuimm = (((i >> 11) & 3) << 4) | (((i >> 7) & 15) << 6) \
            | (((i >> 6) & 1) << 2) | (((i >> 5) & 1) << 3)
        if instr.base() == 'C.ADDI4SPN':
            self.rs1 = Reg.sp

CLS_Woffset = lambda i: (((i >> 10) & 7) << 3) | (((i >> 6) & 1) << 2) \
    | (((i >> 5) & 1) << 6)
CLS_Doffset = lambda i: (((i >> 10) & 7) << 3) | (((i >> 5) & 3) << 6)
CLS_Qoffset = lambda i: (((i >> 11) & 3) << 4) | (((i >> 10) & 1) << 8) \
    | (((i >> 5) & 3) << 6)

class CLtype:
    """Compressed load"""
    def __init__(self, instr):
        self.funct3 = instr.bin >> 13
        rs1_ = (instr.bin >> 7) & 7
        rd_ = (instr.bin >> 2) & 7
        self.rs1 = rs1_ + 8
        self.rd = rd_ + 8
        self.op = instr.bin & 3
        self.offset = CLtype.offset[instr.base()](instr.bin)

    offset = {
        'C.LW': CLS_Woffset,
        'C.LD': CLS_Doffset,
        'C.LQ': CLS_Qoffset,
        'C.FLW': CLS_Woffset,
        'C.FLD': CLS_Doffset,
    }

class CStype:
    """Compressed store"""
    def __init__(self, instr):
        self.funct3 = instr.bin >> 13
        rs1_ = (instr.bin >> 7) & 7
        rs2_ = (instr.bin >> 2) & 7
        self.rs1 = rs1_ + 8
        self.rs2 = rs2_ + 8
        self.op = instr.bin & 3
        self.offset = CStype.offset[instr.base()](instr.bin)

    offset = {
        'C.SW': CLS_Woffset,
        'C.SD': CLS_Doffset,
        'C.SQ': CLS_Qoffset,
        'C.FSW': CLS_Woffset,
        'C.FSD': CLS_Doffset,
    }

class CAtype:
    """Compressed arithmetic"""
    def __init__(self, instr):
        self.funct6 = instr.bin >> 10
        r = (instr.bin >> 7) & 7
        self.rd = r + 8
        self.rs1 = r + 8
        self.funct2 = (instr.bin >> 5) & 3
        self.rs2 = ((instr.bin >> 2) & 7) + 8
        self.op = instr.bin & 3

class CBtype:
    """Compressed branch"""
    def __init__(self, instr):
        i = instr.bin
        base = instr.base()
        self.funct3 = i >> 13
        self.offset = (i >> 10) & 7
        rs1_ = (i >> 7) & 7
        self.rs1 = rs1_ + 8
        self.op = instr.bin & 3
        if base in CBtype.branch:
            self.offset = (((i >> 12) & 1) << 8) | (((i >> 10) & 3) << 3) \
                | (((i >> 5) & 3) << 6) | (((i >> 3) & 3) << 1) \
                | (((i >> 2) & 1) << 5)
        if base in CBtype.regimm:
            self.shamt = CItype.imm(i)
            self.rd = self.rs1

    branch = ['C.BEQZ', 'C.BNEZ']
    regimm = ['C.SRLI', 'C.SRAI', 'C.ANDI']

class CJtype:
    """Compressed jump"""
    def __init__(self, instr):
        self.funct3 = instr.bin >> 13
        assert instr.base() in ['C.J', 'C.JAL']
        self.offset = CJtype.offset(instr.bin)
        self.jump_target = (instr.bin >> 2) & 0x7ff
        self.op = instr.bin & 3

    offset = lambda i: (((i >> 12) & 1) << 11) | (((i << 11) & 1) << 4) \
        | (((i >> 9) & 3) << 8) | (((i >> 8) & 1) << 10) \
        | (((i >> 7) & 1) << 6) | (((i >> 6) & 1) << 7) \
        | (((i >> 3) & 1) << 1) | (((i >> 2) & 1) << 5)

class Instr:
    """Instructions"""

    table_16_4_RV32 = [
        ['C.ADDI4SPN', 'C.FLD', 'C.LW', 'C.FLW', 'Reserved', 'C.FSD', 'C.SW', 'C.FSW'],
        ['C.ADDI', 'C.JAL', 'C.LI', 'C.LUI/C.ADDI16SP', 'MISC-ALU', 'C.J', 'C.BEQZ', 'C.BNEZ'],
        ['C.SLLI', 'C.FLDSP', 'C.LWSP', 'C.FLWSP', 'C.J[AL]R/C.MV/C.ADD', 'C.FSDSP', 'C.SWSP', 'C.FSWSP'],
    ]

    table_24_1 = [
        ['LOAD', 'LOAD-FP', 'custom-0', 'MISC-MEM', 'OP-IMM', 'AUIPC', 'OP-IMM-32', '48b'],
        ['STORE', 'STORE-FP', 'custom-1', 'AMO', 'OP', 'LUI', 'OP-32', '64b'],
        ['MADD', 'MSUB', 'NMSUB', 'NMADD', 'OP-FP', 'reserved', 'custom-2/rv128', '48b'],
        ['BRANCH', 'JALR', 'reserved', 'JAL', 'SYSTEM', 'reserved', 'custom-3/rv128', '80b'],
    ]
    type_of_base = {
        'OP-IMM': Itype,
        'LUI': Utype,
        'AUIPC': Utype,
        'OP': Rtype,
        'JAL': Jtype,
        'JALR': Itype,
        'BRANCH': Btype,
        'LOAD': Itype,
        'STORE': Stype,
        'SYSTEM': Itype,
        'C.LWSP': CItype,
        'C.LDSP': CItype,
        'C.LQSP': CItype,
        'C.FLWSP': CItype,
        'C.FLDSP': CItype,
        'C.SWSP': CSStype,
        'C.SDSP': CSStype,
        'C.SQSP': CSStype,
        'C.FSWSP': CSStype,
        'C.FSDSP': CSStype,
        'C.LW': CLtype,
        'C.LD': CLtype,
        'C.LQ': CLtype,
        'C.FLW': CLtype,
        'C.FLD': CLtype,
        'C.SW': CStype,
        'C.SD': CStype,
        'C.SQ': CStype,
        'C.FSW': CStype,
        'C.FSD': CStype,
        'C.J': CJtype,
        'C.JAL': CJtype,
        'C.J[AL]R/C.MV/C.ADD': CRtype,
        'C.BEQZ': CBtype,
        'C.BNEZ': CBtype,
        'C.LI': CItype,
        'C.LUI/C.ADDI16SP': CItype,
        'C.ADDI': CItype,
        'C.ADDIW': CItype,
        'C.ADDI4SPN': CIWtype,
        'C.SLLI': CItype,
        'MISC-ALU': CAtype,
    }

    def __init__(self, bincode):
        self.bin = bincode
        self.inst_1_0 = self.bin & 3

    def base(self):
        """Get the name of the base instruction"""
        result = ""
        if self.is_compressed():
            line = self.bin & 3
            col = (self.bin >> 13) & 7
            result = Instr.table_16_4_RV32[line][col]
        else:
            line = (self.bin >> 5) & 3
            col = (self.bin >> 2) & 7
            result = Instr.table_24_1[line][col]
        return result

    def fields(self):
        """Get an object with the fields of the instruction"""
        return Instr.type_of_base[self.base()](self)

    def is_compressed(self):
        """Is the instruction from the C extension?"""
        return (self.bin & 3) < 3

    def has_WAW_from(self, other):
        """b.has_WAW_from(a) if a.rd == b.rd"""
        a = other.fields()
        b = self.fields()
        if not (hasattr(a, 'rd') and hasattr(b, 'rd')):
            return False
        return a.rd == b.rd and a.rd != 0

    def has_RAW_from(self, other):
        """b.has_RAW_from(a) if same b.rsX == a.rd"""
        a = other.fields()
        b = self.fields()
        if not hasattr(a, 'rd'):
            return False
        if hasattr(b, 'rs1') and a.rd == b.rs1:
            return True
        return hasattr(b, 'rs2') and a.rd == b.rs2

    def has_WAR_from(self, other):
        """b.has_WAR_from(a) if b.rd == a.rsX"""
        a = other.fields()
        b = self.fields()
        if not hasattr(b, 'rd'):
            return False
        if hasattr(a, 'rs1') and a.rs1 == b.rd:
            return True
        return hasattr(a, 'rs2') and a.rs2 == b.rd
