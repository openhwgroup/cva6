// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Florian Zaruba, ETH Zurich - Andreas Traber, ACP
// Date: 30.05.2017
// Description: Instruction tracer single instruction item

`ifndef VERILATOR
function string printPCexpr(input logic [63:0] imm);
  // check if the sign bit is set
  if ($signed(imm) > 0) begin
      return $sformatf("pc + %0d", $signed(imm));
  end else begin
      return $sformatf("pc - %0d", $signed(-imm));
  end
endfunction

class instr_trace_item;
    // keep a couple of general purpose information inside this instruction item
    time               simtime;
    longint unsigned   cycle;
    cva6_pkg::scoreboard_entry_t sbe;
    logic [31:0]       pc;
    logic [31:0]       instr;
    logic [63:0]       gp_reg_file [32];
    logic [63:0]       fp_reg_file [32];
    logic [4:0]        read_regs [$];
    logic              read_fpr [$];
    logic [4:0]        result_regs [$];
    logic              result_fpr [$];
    logic [63:0]       imm;
    logic [63:0]       result;
    logic [cva6_riscv::PLEN-1:0]       paddr;
    string             priv_lvl;
    cva6_pkg::bp_resolve_t       bp;

    logic [4:0] rs1, rs2, rs3, rd;

    // constructor creating a new instruction trace item, e.g.: a single instruction with all relevant information
    function new (time simtime, longint unsigned cycle, cva6_pkg::scoreboard_entry_t sbe, logic [31:0] instr, logic [63:0] gp_reg_file [32],
                logic [63:0] fp_reg_file [32], logic [63:0] result, logic [cva6_riscv::PLEN-1:0] paddr, cva6_riscv::priv_lvl_t priv_lvl, logic debug_mode, cva6_pkg::bp_resolve_t bp);
        this.simtime  = simtime;
        this.cycle    = cycle;
        this.pc       = sbe.pc;
        this.sbe      = sbe;
        this.gp_reg_file = gp_reg_file;
        this.fp_reg_file = fp_reg_file;
        this.result   = result;
        this.paddr    = paddr;
        this.bp       = bp;
        this.priv_lvl = (debug_mode) ? "D" : getPrivLevel(priv_lvl);
        this.rs1      = sbe.rs1[4:0];
        this.rs2      = sbe.rs2[4:0];
        this.rs3      = instr[31:27];
        this.rd       = sbe.rd[4:0];
        if (instr[1:0] != 2'b11) begin
            this.instr    = {16'b0, instr[15:0]};
        end else begin
            this.instr    = instr;
        end
    endfunction

    // convert gp register address to ABI compatible form
    function string regAddrToStr(logic [5:0] addr);
        case (addr[4:0])
            0: return "x0";
            1: return "ra";
            2: return "sp";
            3: return "gp";
            4: return "tp";
            5, 6, 7: return $sformatf("t%0d", (addr[4:0] - 5));
            8, 9: return $sformatf("s%0d", (addr[4:0] - 8));
            10, 11, 12, 13, 14, 15, 16, 17: return $sformatf("a%0d", (addr[4:0] - 10));
            28, 29, 30, 31: return $sformatf("t%0d", (addr[4:0] - 25));
            default: return $sformatf("s%0d", (addr[4:0] - 16));
        endcase
    endfunction
    // convert fp register address to ABI compatible form
    function string fpRegAddrToStr(logic [5:0] addr);
        case (addr) inside
            [0:7]   : return $sformatf("ft%0d", addr);
            [8:9]   : return $sformatf("fs%0d", (addr - 8));
            [10:17] : return $sformatf("fa%0d", (addr - 10));
            [18:27] : return $sformatf("fs%0d", (addr - 16));
            [28:31] : return $sformatf("ft%0d", (addr - 20));
        endcase
    endfunction

    function string fpFmtToStr(logic [1:0] fmt);
        case (fmt)
            2'b00 : return "s";
            2'b01 : return "d";
            2'b10 : return "h";
            2'b11 : return "b";
            default : return "XX";
        endcase
    endfunction

    function string fmvFpFmtToStr(logic [1:0] fmt);
        case (fmt)
            2'b00 : return "w";
            2'b01 : return "d";
            2'b10 : return "h";
            2'b11 : return "b";
            default : return "XX";
        endcase
    endfunction

    function string intFmtToStr(logic [1:0] ifmt);
        case (ifmt)
            2'b00 : return "w";
            2'b01 : return "wu";
            2'b10 : return "l";
            2'b11 : return "lu";
            default : return "XX";
        endcase
    endfunction

    function string fpRmToStr(logic [2:0] rm);
        case (rm)
            3'b000 : return "rne";
            3'b001 : return "rtz";
            3'b010 : return "rdn";
            3'b011 : return "rup";
            3'b100 : return "rmm";
            3'b111 : return "dyn"; // what is this called in rv binutils?
            default: return "INVALID";
        endcase
    endfunction

    function string csrAddrToStr(logic [11:0] addr);
        case (addr)
            cva6_riscv::CSR_FFLAGS:     return "fflags";
            cva6_riscv::CSR_FRM:        return "frm";
            cva6_riscv::CSR_FCSR:       return "fcsr";
            cva6_riscv::CSR_SSTATUS:    return "sstatus";
            cva6_riscv::CSR_SIE:        return "sie";
            cva6_riscv::CSR_STVEC:      return "stvec";
            cva6_riscv::CSR_SCOUNTEREN: return "scounteren";
            cva6_riscv::CSR_SSCRATCH:   return "sscratch";
            cva6_riscv::CSR_SEPC:       return "sepc";
            cva6_riscv::CSR_SCAUSE:     return "scause";
            cva6_riscv::CSR_STVAL:      return "stval";
            cva6_riscv::CSR_SIP:        return "sip";
            cva6_riscv::CSR_SATP:       return "satp";

            cva6_riscv::CSR_MSTATUS:    return "mstatus";
            cva6_riscv::CSR_MISA:       return "misa";
            cva6_riscv::CSR_MEDELEG:    return "medeleg";
            cva6_riscv::CSR_MIDELEG:    return "mideleg";
            cva6_riscv::CSR_MIE:        return "mie";
            cva6_riscv::CSR_MTVEC:      return "mtvec";
            cva6_riscv::CSR_MCOUNTEREN: return "mcounteren";
            cva6_riscv::CSR_MSCRATCH:   return "mscratch";
            cva6_riscv::CSR_MEPC:       return "mepc";
            cva6_riscv::CSR_MCAUSE:     return "mcause";
            cva6_riscv::CSR_MTVAL:      return "mtval";
            cva6_riscv::CSR_MIP:        return "mip";
            cva6_riscv::CSR_PMPCFG0:    return "pmpcfg0";
            cva6_riscv::CSR_PMPADDR0:   return "pmpaddr0";
            cva6_riscv::CSR_MVENDORID:  return "mvendorid";
            cva6_riscv::CSR_MARCHID:    return "marchid";
            cva6_riscv::CSR_MIMPID:     return "mimpid";
            cva6_riscv::CSR_MHARTID:    return "mhartid";
            cva6_riscv::CSR_MCYCLE:     return "mcycle";
            cva6_riscv::CSR_MINSTRET:   return "minstret";

            cva6_riscv::CSR_TSELECT:    return "tselect";
            cva6_riscv::CSR_TDATA1:     return "tdata1";
            cva6_riscv::CSR_TDATA2:     return "tdata2";
            cva6_riscv::CSR_TDATA3:     return "tdata3";
            cva6_riscv::CSR_TINFO:      return "tinfo";

            cva6_riscv::CSR_DCSR:       return "dcsr";
            cva6_riscv::CSR_DPC:        return "dpc";
            cva6_riscv::CSR_DSCRATCH0:  return "dscratch0";
            cva6_riscv::CSR_DSCRATCH1:  return "dscratch1";

            cva6_riscv::CSR_CYCLE:      return "cycle";
            cva6_riscv::CSR_TIME:       return "time";
            cva6_riscv::CSR_INSTRET:    return "instret";

            default:        return $sformatf("%0h", addr);
        endcase
    endfunction

    function string printInstr();
        string s;

        case (instr) inside
             // Aliases
            cva6_instr_tracer_pkg::INSTR_NOP:      s = this.printMnemonic("nop");
            // Regular opcodes
            cva6_instr_tracer_pkg::INSTR_LUI:      s = this.printUInstr("lui");
            cva6_instr_tracer_pkg::INSTR_AUIPC:    s = this.printUInstr("auipc");
            cva6_instr_tracer_pkg::INSTR_JAL:      s = this.printJump("jal");
            cva6_instr_tracer_pkg::INSTR_JALR:     s = this.printJump("jalr");
            // BRANCH
            cva6_instr_tracer_pkg::INSTR_BEQZ:     s = this.printSBInstr("beqz");
            cva6_instr_tracer_pkg::INSTR_BEQ:      s = this.printSBInstr("beq");
            cva6_instr_tracer_pkg::INSTR_BNEZ:     s = this.printSBInstr("bnez");
            cva6_instr_tracer_pkg::INSTR_BNE:      s = this.printSBInstr("bne");
            cva6_instr_tracer_pkg::INSTR_BLTZ:     s = this.printSBInstr("bltz");
            cva6_instr_tracer_pkg::INSTR_BLT:      s = this.printSBInstr("blt");
            cva6_instr_tracer_pkg::INSTR_BGEZ:     s = this.printSBInstr("bgez");
            cva6_instr_tracer_pkg::INSTR_BGE:      s = this.printSBInstr("bge");
            cva6_instr_tracer_pkg::INSTR_BLTU:     s = this.printSBInstr("bltu");
            cva6_instr_tracer_pkg::INSTR_BGEU:     s = this.printSBInstr("bgeu");
            // OPIMM
            cva6_instr_tracer_pkg::INSTR_LI:       s = this.printIInstr("li");
            cva6_instr_tracer_pkg::INSTR_ADDI:     s = this.printIInstr("addi");
            cva6_instr_tracer_pkg::INSTR_SLTI:     s = this.printIInstr("slti");
            cva6_instr_tracer_pkg::INSTR_SLTIU:    s = this.printIInstr("sltiu");
            cva6_instr_tracer_pkg::INSTR_XORI:     s = this.printIInstr("xori");
            cva6_instr_tracer_pkg::INSTR_ORI:      s = this.printIInstr("ori");
            cva6_instr_tracer_pkg::INSTR_ANDI:     s = this.printIInstr("andi");
            cva6_instr_tracer_pkg::INSTR_SLLI:     s = this.printIuInstr("slli");
            cva6_instr_tracer_pkg::INSTR_SRLI:     s = this.printIuInstr("srli");
            cva6_instr_tracer_pkg::INSTR_SRAI:     s = this.printIuInstr("srai");
            // OPIMM32
            cva6_instr_tracer_pkg::INSTR_ADDIW:    s = this.printIInstr("addiw");
            cva6_instr_tracer_pkg::INSTR_SLLIW:    s = this.printIuInstr("slliw");
            cva6_instr_tracer_pkg::INSTR_SRLIW:    s = this.printIuInstr("srliw");
            cva6_instr_tracer_pkg::INSTR_SRAIW:    s = this.printIuInstr("sraiw");
            // OP
            cva6_instr_tracer_pkg::INSTR_ADD:      s = this.printRInstr("add");
            cva6_instr_tracer_pkg::INSTR_SUB:      s = this.printRInstr("sub");
            cva6_instr_tracer_pkg::INSTR_SLL:      s = this.printRInstr("sll");
            cva6_instr_tracer_pkg::INSTR_SLT:      s = this.printRInstr("slt");
            cva6_instr_tracer_pkg::INSTR_SLTU:     s = this.printRInstr("sltu");
            cva6_instr_tracer_pkg::INSTR_XOR:      s = this.printRInstr("xor");
            cva6_instr_tracer_pkg::INSTR_SRL:      s = this.printRInstr("srl");
            cva6_instr_tracer_pkg::INSTR_SRA:      s = this.printRInstr("sra");
            cva6_instr_tracer_pkg::INSTR_OR:       s = this.printRInstr("or");
            cva6_instr_tracer_pkg::INSTR_AND:      s = this.printRInstr("and");
            cva6_instr_tracer_pkg::INSTR_MUL:      s = this.printMulInstr(1'b0);
            // OP32
            cva6_instr_tracer_pkg::INSTR_ADDW:     s = this.printRInstr("addw");
            cva6_instr_tracer_pkg::INSTR_SUBW:     s = this.printRInstr("subw");
            cva6_instr_tracer_pkg::INSTR_SLLW:     s = this.printRInstr("sllw");
            cva6_instr_tracer_pkg::INSTR_SRLW:     s = this.printRInstr("srlw");
            cva6_instr_tracer_pkg::INSTR_SRAW:     s = this.printRInstr("sraw");
            cva6_instr_tracer_pkg::INSTR_MULW:     s = this.printMulInstr(1'b1);
            // FP
            cva6_instr_tracer_pkg::INSTR_FMADD:    s = this.printR4Instr("fmadd");
            cva6_instr_tracer_pkg::INSTR_FMSUB:    s = this.printR4Instr("fmsub");
            cva6_instr_tracer_pkg::INSTR_FNSMSUB:  s = this.printR4Instr("fnmsub");
            cva6_instr_tracer_pkg::INSTR_FNMADD:   s = this.printR4Instr("fnmadd");

            cva6_instr_tracer_pkg::INSTR_FADD:     s = this.printRFBCInstr("fadd", 1'b1);
            cva6_instr_tracer_pkg::INSTR_FSUB:     s = this.printRFBCInstr("fsub", 1'b1);
            cva6_instr_tracer_pkg::INSTR_FMUL:     s = this.printRFInstr("fmul", 1'b1);
            cva6_instr_tracer_pkg::INSTR_FDIV:     s = this.printRFInstr("fdiv", 1'b1);
            cva6_instr_tracer_pkg::INSTR_FSQRT:    s = this.printRFInstr1Op("fsqrt", 1'b1);
            cva6_instr_tracer_pkg::INSTR_FSGNJ:    s = this.printRFInstr("fsgnj", 1'b0);
            cva6_instr_tracer_pkg::INSTR_FSGNJN:   s = this.printRFInstr("fsgnjn", 1'b0);
            cva6_instr_tracer_pkg::INSTR_FSGNJX:   s = this.printRFInstr("fsgnjx", 1'b0);
            cva6_instr_tracer_pkg::INSTR_FMIN:     s = this.printRFInstr("fmin", 1'b0);
            cva6_instr_tracer_pkg::INSTR_FMAX:     s = this.printRFInstr("fmax", 1'b0);
            cva6_instr_tracer_pkg::INSTR_FLE:      s = this.printRFInstr("fle", 1'b0);
            cva6_instr_tracer_pkg::INSTR_FLT:      s = this.printRFInstr("flt", 1'b0);
            cva6_instr_tracer_pkg::INSTR_FEQ:      s = this.printRFInstr("feq", 1'b0);

            cva6_instr_tracer_pkg::INSTR_FCLASS:   s = this.printRFInstr1Op("fclass", 1'b0);

            cva6_instr_tracer_pkg::INSTR_FCVT_F2F,
            cva6_instr_tracer_pkg::INSTR_FMV_F2X,
            cva6_instr_tracer_pkg::INSTR_FMV_X2F,
            cva6_instr_tracer_pkg::INSTR_FCVT_F2I,
            cva6_instr_tracer_pkg::INSTR_FCVT_I2F: s = this.printFpSpecialInstr(); // these are a mess to do nicely
            // FENCE
            cva6_instr_tracer_pkg::INSTR_FENCE:    s = this.printMnemonic("fence");
            cva6_instr_tracer_pkg::INSTR_FENCEI:   s = this.printMnemonic("fence.i");
            // SYSTEM (CSR manipulation)
            cva6_instr_tracer_pkg::INSTR_CSRW:     s = this.printCSRInstr("csrw");
            cva6_instr_tracer_pkg::INSTR_CSRRW:    s = this.printCSRInstr("csrrw");
            cva6_instr_tracer_pkg::INSTR_CSRR:     s = this.printCSRInstr("csrr");
            cva6_instr_tracer_pkg::INSTR_CSRRS:    s = this.printCSRInstr("csrrs");
            cva6_instr_tracer_pkg::INSTR_CSRS:     s = this.printCSRInstr("csrs");
            cva6_instr_tracer_pkg::INSTR_CSRRC:    s = this.printCSRInstr("csrrc");
            cva6_instr_tracer_pkg::INSTR_CSRC:     s = this.printCSRInstr("csrc");

            cva6_instr_tracer_pkg::INSTR_CSRWI:    s = this.printCSRInstr("csrwi");
            cva6_instr_tracer_pkg::INSTR_CSRRWI:   s = this.printCSRInstr("csrrwi");
            cva6_instr_tracer_pkg::INSTR_CSRSI:    s = this.printCSRInstr("csrsi");
            cva6_instr_tracer_pkg::INSTR_CSRRSI:   s = this.printCSRInstr("csrrsi");
            cva6_instr_tracer_pkg::INSTR_CSRCI:    s = this.printCSRInstr("csrci");
            cva6_instr_tracer_pkg::INSTR_CSRRCI:   s = this.printCSRInstr("csrrci");
            // SYSTEM (others)
            cva6_instr_tracer_pkg::INSTR_ECALL:    s = this.printMnemonic("ecall");
            cva6_instr_tracer_pkg::INSTR_EBREAK:   s = this.printMnemonic("ebreak");
            cva6_instr_tracer_pkg::INSTR_MRET:     s = this.printMnemonic("mret");
            cva6_instr_tracer_pkg::INSTR_SRET:     s = this.printMnemonic("sret");
            cva6_instr_tracer_pkg::INSTR_DRET:     s = this.printMnemonic("dret");
            cva6_instr_tracer_pkg::INSTR_WFI:      s = this.printMnemonic("wfi");
            cva6_instr_tracer_pkg::INSTR_SFENCE:   s = this.printMnemonic("sfence.vma");
            // loads and stores
            cva6_instr_tracer_pkg::LB:             s = this.printLoadInstr("lb");
            cva6_instr_tracer_pkg::LH:             s = this.printLoadInstr("lh");
            cva6_instr_tracer_pkg::LW:             s = this.printLoadInstr("lw");
            cva6_instr_tracer_pkg::LD:             s = this.printLoadInstr("ld");
            cva6_instr_tracer_pkg::LBU:            s = this.printLoadInstr("lbu");
            cva6_instr_tracer_pkg::LHU:            s = this.printLoadInstr("lhu");
            cva6_instr_tracer_pkg::LWU:            s = this.printLoadInstr("lwu");
            cva6_instr_tracer_pkg::FLW:            s = this.printLoadInstr("flw");
            cva6_instr_tracer_pkg::FLD:            s = this.printLoadInstr("fld");
            cva6_instr_tracer_pkg::FLQ:            s = this.printLoadInstr("flq");
            cva6_instr_tracer_pkg::FSW:            s = this.printLoadInstr("fsw");
            cva6_instr_tracer_pkg::FSD:            s = this.printLoadInstr("fsd");
            cva6_instr_tracer_pkg::FSQ:            s = this.printLoadInstr("fsq");
            cva6_instr_tracer_pkg::SB:             s = this.printStoreInstr("sb");
            cva6_instr_tracer_pkg::SH:             s = this.printStoreInstr("sh");
            cva6_instr_tracer_pkg::SW:             s = this.printStoreInstr("sw");
            cva6_instr_tracer_pkg::SD:             s = this.printStoreInstr("sd");
            cva6_instr_tracer_pkg::FSW:            s = this.printStoreInstr("fsw");
            cva6_instr_tracer_pkg::FSD:            s = this.printStoreInstr("fsd");
            cva6_instr_tracer_pkg::FSQ:            s = this.printStoreInstr("fsq");
            cva6_instr_tracer_pkg::INSTR_AMO:      s = this.printAMOInstr();
            // Compressed Instructions
            cva6_instr_tracer_pkg::C_FLD:          s = this.printLoadInstr("c.fld");
            cva6_instr_tracer_pkg::C_LW:           s = this.printLoadInstr("c.lw");
            cva6_instr_tracer_pkg::C_LD:           s = this.printLoadInstr("c.ld");
            cva6_instr_tracer_pkg::C_LWSP:         s = this.printLoadInstr("c.lwsp");
            cva6_instr_tracer_pkg::C_LDSP:         s = this.printLoadInstr("c.ldsp");
            cva6_instr_tracer_pkg::C_FLDSP:        s = this.printLoadInstr("c.fldsp");
            cva6_instr_tracer_pkg::C_SDSP:         s = this.printStoreInstr("c.sdsp");
            cva6_instr_tracer_pkg::C_SWSP:         s = this.printStoreInstr("c.swsp");
            cva6_instr_tracer_pkg::C_FSDSP:        s = this.printStoreInstr("c.fsdsp");
            cva6_instr_tracer_pkg::C_SW:           s = this.printStoreInstr("c.sw");
            cva6_instr_tracer_pkg::C_SD:           s = this.printStoreInstr("c.sd");
            cva6_instr_tracer_pkg::C_FSD:          s = this.printStoreInstr("c.fsd");
            cva6_instr_tracer_pkg::C_J:            s = this.printJump("c.j");
            cva6_instr_tracer_pkg::C_JR:           s = this.printJump("c.jr");
            cva6_instr_tracer_pkg::C_JALR:         s = this.printJump("c.jalr");
            cva6_instr_tracer_pkg::C_MV:           s = this.printRInstr("c.mv");
            cva6_instr_tracer_pkg::C_ADD:          s = this.printRInstr("c.add");
            cva6_instr_tracer_pkg::C_BEQZ:         s = this.printSBInstr("c.beqz");
            cva6_instr_tracer_pkg::C_BNEZ:         s = this.printSBInstr("c.bnez");
            cva6_instr_tracer_pkg::C_LUI:          s = this.printUInstr("c.lui");
            cva6_instr_tracer_pkg::C_LI:           s = this.printIInstr("c.li");
            cva6_instr_tracer_pkg::C_ADDI:         s = this.printIInstr("c.addi");
            cva6_instr_tracer_pkg::C_ADDI16SP:     s = this.printIInstr("c.addi16sp");
            cva6_instr_tracer_pkg::C_ADDIW:        s = this.printIInstr("c.addiw");
            cva6_instr_tracer_pkg::C_SLLI:         s = this.printIInstr("c.slli");
            cva6_instr_tracer_pkg::C_SRLI:         s = this.printIInstr("c.srli");
            cva6_instr_tracer_pkg::C_SRAI:         s = this.printIInstr("c.srai");
            cva6_instr_tracer_pkg::C_ANDI:         s = this.printIInstr("c.andi");
            cva6_instr_tracer_pkg::C_ADDI4SPN:     s = this.printIInstr("c.addi4spn");
            cva6_instr_tracer_pkg::C_SUB:          s = this.printRInstr("c.sub");
            cva6_instr_tracer_pkg::C_XOR:          s = this.printRInstr("c.xor");
            cva6_instr_tracer_pkg::C_OR:           s = this.printRInstr("c.or");
            cva6_instr_tracer_pkg::C_AND:          s = this.printRInstr("c.and");
            cva6_instr_tracer_pkg::C_SUBW:         s = this.printRInstr("c.subw");
            cva6_instr_tracer_pkg::C_ADDW:         s = this.printRInstr("c.addw");
            cva6_instr_tracer_pkg::C_NOP:          s = this.printMnemonic("c.nop");
            cva6_instr_tracer_pkg::C_EBREAK:       s = this.printMnemonic("c.ebreak");
            default:                          s = this.printMnemonic("INVALID");
        endcase

        s = $sformatf("%8dns %8d %s %h %h %h %-36s", simtime,
                                             cycle,
                                             priv_lvl,
                                             sbe.pc,
                                             bp.is_mispredict & bp.valid,
                                             instr,
                                             s);

        // s = $sformatf("%s %h %h %-36s",
        //                                      priv_lvl,
        //                                      sbe.pc,
        //                                      instr,
        //                                      s);

        foreach (result_regs[i]) begin
            if (result_fpr[i])
                s = $sformatf("%s %-4s:%16x", s, fpRegAddrToStr(result_regs[i]), this.result);
            else if (result_regs[i] != 0)
                s = $sformatf("%s %-4s:%16x", s, regAddrToStr(result_regs[i]), this.result);
        end

        foreach (read_regs[i]) begin
            if (read_fpr[i])
                s = $sformatf("%s %-4s:%16x", s, fpRegAddrToStr(read_regs[i]), fp_reg_file[read_regs[i]]);
            else if (read_regs[i] != 0)
                s = $sformatf("%s %-4s:%16x", s, regAddrToStr(read_regs[i]), gp_reg_file[read_regs[i]]);
        end

        case (instr) inside
            // check of the instruction was a load or store
            cva6_instr_tracer_pkg::C_SDSP,
            cva6_instr_tracer_pkg::C_SWSP,
            cva6_instr_tracer_pkg::C_FSWSP,
            cva6_instr_tracer_pkg::C_FSDSP,
            cva6_instr_tracer_pkg::C_SW,
            cva6_instr_tracer_pkg::C_SD,
            cva6_instr_tracer_pkg::C_FSW,
            cva6_instr_tracer_pkg::C_FSD,
            cva6_instr_tracer_pkg::SB,
            cva6_instr_tracer_pkg::SH,
            cva6_instr_tracer_pkg::SW,
            cva6_instr_tracer_pkg::SD,
            cva6_instr_tracer_pkg::FSW,
            cva6_instr_tracer_pkg::FSD,
            cva6_instr_tracer_pkg::FSQ: begin
                logic [cva6_riscv::VLEN-1:0] vaddress = gp_reg_file[read_regs[1]] + this.imm;
                s = $sformatf("%s VA: %x PA: %x", s, vaddress, this.paddr);
            end

            cva6_instr_tracer_pkg::C_FLD,
            cva6_instr_tracer_pkg::C_FLW,
            cva6_instr_tracer_pkg::C_LW,
            cva6_instr_tracer_pkg::C_LD,
            cva6_instr_tracer_pkg::C_LWSP,
            cva6_instr_tracer_pkg::C_LDSP,
            cva6_instr_tracer_pkg::C_FLWSP,
            cva6_instr_tracer_pkg::C_FLDSP,
            cva6_instr_tracer_pkg::LB,
            cva6_instr_tracer_pkg::LH,
            cva6_instr_tracer_pkg::LW,
            cva6_instr_tracer_pkg::LD,
            cva6_instr_tracer_pkg::LBU,
            cva6_instr_tracer_pkg::LHU,
            cva6_instr_tracer_pkg::LWU,
            cva6_instr_tracer_pkg::FLW,
            cva6_instr_tracer_pkg::FLD,
            cva6_instr_tracer_pkg::FLQ: begin
                logic [cva6_riscv::VLEN-1:0] vaddress = gp_reg_file[read_regs[0]] + this.imm;
                s = $sformatf("%s VA: %x PA: %x", s, vaddress, this.paddr);
            end
        endcase
        return s;
    endfunction : printInstr

    // Return the current privilege level as a string
    function string getPrivLevel(input cva6_riscv::priv_lvl_t priv_lvl);
        case (priv_lvl)
            cva6_riscv::PRIV_LVL_M: return "M";
            cva6_riscv::PRIV_LVL_S: return "S";
            cva6_riscv::PRIV_LVL_U: return "U";
        endcase
    endfunction : getPrivLevel

    function string printMnemonic(input string mnemonic);
        return mnemonic;
    endfunction // printMnemonic

    function string printRInstr(input string mnemonic);

        result_regs.push_back(rd);
        result_fpr.push_back(1'b0);
        read_regs.push_back(rs1);
        read_fpr.push_back(1'b0);
        read_regs.push_back(rs2);
        read_fpr.push_back(1'b0);

        return $sformatf("%-12s %4s, %s, %s", mnemonic, regAddrToStr(rd), regAddrToStr(rs1), regAddrToStr(rs2));
    endfunction // printRInstr

    function string printRFBCInstr(input string mnemonic, input bit use_rnd);

        result_regs.push_back(rd);
        result_fpr.push_back(cva6_pkg::is_rd_fpr(sbe.op));
        read_regs.push_back(rs2);
        read_fpr.push_back(cva6_pkg::is_rs2_fpr(sbe.op));
        read_regs.push_back(sbe.result[4:0]);
        read_fpr.push_back(cva6_pkg::is_imm_fpr(sbe.op));

        if (use_rnd && instr[14:12]!=3'b111)
            return $sformatf("%-12s %4s, %s, %s, %s", $sformatf("%s.%s",mnemonic, fpFmtToStr(instr[26:25])), cva6_pkg::is_rd_fpr(sbe.op)?fpRegAddrToStr(rd):regAddrToStr(rd), cva6_pkg::is_rs2_fpr(sbe.op)?fpRegAddrToStr(rs2):regAddrToStr(rs2), cva6_pkg::is_imm_fpr(sbe.op)?fpRegAddrToStr(sbe.result[4:0]):regAddrToStr(sbe.result[4:0]), fpRmToStr(instr[14:12]));
        else
            return $sformatf("%-12s %4s, %s, %s", $sformatf("%s.%s",mnemonic, fpFmtToStr(instr[26:25])), cva6_pkg::is_rd_fpr(sbe.op)?fpRegAddrToStr(rd):regAddrToStr(rd), cva6_pkg::is_rs2_fpr(sbe.op)?fpRegAddrToStr(rs2):regAddrToStr(rs2), cva6_pkg::is_imm_fpr(sbe.op)?fpRegAddrToStr(sbe.result[4:0]):regAddrToStr(sbe.result[4:0]));
    endfunction // printRFInstr

    function string printRFInstr(input string mnemonic, input bit use_rnd);

        result_regs.push_back(rd);
        result_fpr.push_back(cva6_pkg::is_rd_fpr(sbe.op));
        read_regs.push_back(rs1);
        read_fpr.push_back(cva6_pkg::is_rs1_fpr(sbe.op));
        read_regs.push_back(rs2);
        read_fpr.push_back(cva6_pkg::is_rs2_fpr(sbe.op));

        if (use_rnd && instr[14:12]!=3'b111)
            return $sformatf("%-12s %4s, %s, %s, %s", $sformatf("%s.%s",mnemonic, fpFmtToStr(instr[26:25])), cva6_pkg::is_rd_fpr(sbe.op)?fpRegAddrToStr(rd):regAddrToStr(rd), cva6_pkg::is_rs1_fpr(sbe.op)?fpRegAddrToStr(rs1):regAddrToStr(rs1), cva6_pkg::is_rs2_fpr(sbe.op)?fpRegAddrToStr(rs2):regAddrToStr(rs2), fpRmToStr(instr[14:12]));
        else
            return $sformatf("%-12s %4s, %s, %s", $sformatf("%s.%s",mnemonic, fpFmtToStr(instr[26:25])), cva6_pkg::is_rd_fpr(sbe.op)?fpRegAddrToStr(rd):regAddrToStr(rd), cva6_pkg::is_rs1_fpr(sbe.op)?fpRegAddrToStr(rs1):regAddrToStr(rs1), cva6_pkg::is_rs2_fpr(sbe.op)?fpRegAddrToStr(rs2):regAddrToStr(rs2));
    endfunction // printRFInstr

    function string printRFInstr1Op(input string mnemonic, input bit use_rnd);

        result_regs.push_back(rd);
        result_fpr.push_back(cva6_pkg::is_rd_fpr(sbe.op));
        read_regs.push_back(rs1);
        read_fpr.push_back(cva6_pkg::is_rs1_fpr(sbe.op));

        if (use_rnd && instr[14:12]!=3'b111)
            return $sformatf("%-12s %4s, %s, %s", $sformatf("%s.%s",mnemonic, fpFmtToStr(instr[26:25])), cva6_pkg::is_rd_fpr(sbe.op)?fpRegAddrToStr(rd):regAddrToStr(rd), cva6_pkg::is_rs1_fpr(sbe.op)?fpRegAddrToStr(rs1):regAddrToStr(rs1), fpRmToStr(instr[14:12]));
        else
            return $sformatf("%-12s %4s, %s", $sformatf("%s.%s",mnemonic, fpFmtToStr(instr[26:25])), cva6_pkg::is_rd_fpr(sbe.op)?fpRegAddrToStr(rd):regAddrToStr(rd), cva6_pkg::is_rs1_fpr(sbe.op)?fpRegAddrToStr(rs1):regAddrToStr(rs1));
    endfunction // printRFInstr1Op

    function string printR4Instr(input string mnemonic);

        result_regs.push_back(rd);
        result_fpr.push_back(1'b1);
        read_regs.push_back(rs1);
        read_fpr.push_back(1'b1);
        read_regs.push_back(rs2);
        read_fpr.push_back(1'b1);
        read_regs.push_back(rs3);
        read_fpr.push_back(1'b1);

        return $sformatf("%-12s %4s, %s, %s, %s, %s", $sformatf("%s.%s",mnemonic, fpFmtToStr(instr[26:25])), fpRegAddrToStr(rd), fpRegAddrToStr(rs1), fpRegAddrToStr(rs2), fpRegAddrToStr(instr[31:27]), fpRmToStr(instr[14:12]));
    endfunction // printR4Instr

    function string printFpSpecialInstr();

        result_regs.push_back(rd);
        result_fpr.push_back(cva6_pkg::is_rd_fpr(sbe.op));
        read_regs.push_back(rs1);
        read_fpr.push_back(cva6_pkg::is_rs1_fpr(sbe.op));

        case (sbe.op)
            cva6_instr_tracer_pkg::INSTR_FCVT_F2F : return $sformatf("%-12s %4s, %s, %s", $sformatf("fcvt.%s.%s", fpFmtToStr(instr[26:25]), fpFmtToStr(instr[21:20])), fpRegAddrToStr(rd), fpRegAddrToStr(rs1), fpRmToStr(instr[14:12]));
            cva6_instr_tracer_pkg::INSTR_FCVT_F2I : return $sformatf("%-12s %4s, %s, %s", $sformatf("fcvt.%s.%s", intFmtToStr(instr[21:20]), fpFmtToStr(instr[26:25])), regAddrToStr(rd), fpRegAddrToStr(rs1), fpRmToStr(instr[14:12]));
            cva6_instr_tracer_pkg::INSTR_FCVT_I2F : return $sformatf("%-12s %4s, %s, %s", $sformatf("fcvt.%s.%s", fpFmtToStr(instr[26:25]), intFmtToStr(instr[21:20])), fpRegAddrToStr(rd), regAddrToStr(rs1), fpRmToStr(instr[14:12]));
            cva6_instr_tracer_pkg::INSTR_FMV_F2X  : return $sformatf("%-12s %4s, %s", $sformatf("fmv.x.%s", fmvFpFmtToStr(instr[26:25])), regAddrToStr(rd), fpRegAddrToStr(rs1));
            cva6_instr_tracer_pkg::INSTR_FMV_X2F  : return $sformatf("%-12s %4s, %s", $sformatf("fmv.%s.x", fmvFpFmtToStr(instr[26:25])), fpRegAddrToStr(rd), regAddrToStr(rs1));
        endcase
    endfunction

    function string printIInstr(input string mnemonic);

        result_regs.push_back(rd);
        result_fpr.push_back(1'b0);
        read_regs.push_back(rs1);
        read_fpr.push_back(1'b0);

        if (rs1 == 0)
            return $sformatf("%-12s %4s, %0d", mnemonic, regAddrToStr(rd), $signed(sbe.result));

        return $sformatf("%-12s %4s, %s, %0d", mnemonic, regAddrToStr(rd), regAddrToStr(rs1), $signed(sbe.result));
    endfunction // printIInstr

    function string printIuInstr(input string mnemonic);

        result_regs.push_back(rd);
        result_fpr.push_back(1'b0);
        read_regs.push_back(rs1);
        read_fpr.push_back(1'b0);

        return $sformatf("%-12s %4s, %s, 0x%0x", mnemonic, regAddrToStr(rd), regAddrToStr(rs1), sbe.result);
    endfunction // printIuInstr

    function string printSBInstr(input string mnemonic);

        read_regs.push_back(rs1);
        read_fpr.push_back(1'b0);
        read_regs.push_back(rs2);
        read_fpr.push_back(1'b0);

        if (rs2 == 0) begin
            return $sformatf("%-12s %4s, %s", mnemonic, regAddrToStr(rs1), printPCexpr(sbe.result));
        end else begin
            return $sformatf("%-12s %4s, %s, %s", mnemonic, regAddrToStr(rs1), regAddrToStr(rs2), printPCexpr(sbe.result));
        end
    endfunction // printIuInstr

    function string printUInstr(input string mnemonic);

        result_regs.push_back(rd);
        result_fpr.push_back(1'b0);

        return $sformatf("%-12s %4s, 0x%0h", mnemonic, regAddrToStr(rd), sbe.result[31:12]);
    endfunction // printUInstr

    function string printJump(input string mnemonic);
        case (instr[6:0])
            cva6_riscv::OpcodeJalr: begin
                // is this a return?
                if (rd == 'b0 && (rs1 == 'h1 || rs1 == 'h5)) return this.printMnemonic("ret");
            end
            cva6_riscv::OpcodeJal: begin
                if (rd == 'b0) return this.printUJInstr("j");
            end
        endcase
        return this.printIInstr(mnemonic);
    endfunction

    function string printUJInstr(input string mnemonic);

        result_regs.push_back(rd);
        result_fpr.push_back(1'b0);
        // jump instruction
        if (rd == 0)
            return $sformatf("%-12s   %s", mnemonic, printPCexpr(sbe.result));
        else
            return $sformatf("%-12s %4s, %s", mnemonic, regAddrToStr(rd), printPCexpr(sbe.result));
    endfunction // printUJInstr

    function string printCSRInstr(input string mnemonic);

        result_regs.push_back(rd);
        result_fpr.push_back(1'b0);
        if (instr[14] == 0) begin
        read_regs.push_back(rs1);
        read_fpr.push_back(1'b0);
            if (rd != 0 && rs1 != 0) begin
                  return $sformatf("%-12s %4s, %s, %s", mnemonic, regAddrToStr(rd), regAddrToStr(rs1), csrAddrToStr(sbe.result[11:0]));
            // don't display instructions which write to zero
            end else if (rd == 0) begin
                  return $sformatf("%-12s %4s, %s", mnemonic, regAddrToStr(rs1), csrAddrToStr(sbe.result[11:0]));
            end else if (rs1 == 0) begin
                return $sformatf("%-12s %4s, %s", mnemonic, regAddrToStr(rd), csrAddrToStr(sbe.result[11:0]));
            end
        end else begin
            if (rd != 0 && rs1 != 0) begin
                  return $sformatf("%-12s %4s, %d, %s", mnemonic, regAddrToStr(rd), $unsigned(rs1), csrAddrToStr(sbe.result[11:0]));
            // don't display instructions which write to zero
            end else if (rd == 0) begin
                  return $sformatf("%-14s %2d, %s", mnemonic, $unsigned(rs1), csrAddrToStr(sbe.result[11:0]));
            end else if (rs1 == 0) begin
                return $sformatf("%-12s %4s, %s", mnemonic, regAddrToStr(rd), csrAddrToStr(sbe.result[11:0]));
            end
        end
    endfunction // printCSRInstr

    function string printLoadInstr(input string mnemonic);
        result_regs.push_back(rd);
        result_fpr.push_back(cva6_pkg::is_rd_fpr(sbe.op));
        read_regs.push_back(rs1);
        read_fpr.push_back(1'b0);
        // save the immediate for calculating the virtual address
        this.imm = sbe.result;

        if (instr[6:0] == cva6_riscv::OpcodeLoadFp)
            return $sformatf("%-12s %4s, %0d(%s)", mnemonic, fpRegAddrToStr(rd), $signed(sbe.result), regAddrToStr(rs1));
        else
            return $sformatf("%-12s %4s, %0d(%s)", mnemonic, regAddrToStr(rd), $signed(sbe.result), regAddrToStr(rs1));
    endfunction

    function string printStoreInstr(input string mnemonic);
        read_regs.push_back(rs2);
        read_fpr.push_back(cva6_pkg::is_rs2_fpr(sbe.op));
        read_regs.push_back(rs1);
        read_fpr.push_back(1'b0);
        // save the immediate for calculating the virtual address
        this.imm = sbe.result;

        if (instr[6:0] == cva6_riscv::OpcodeStoreFp)
            return $sformatf("%-12s %4s, %0d(%s)", mnemonic, fpRegAddrToStr(rs2), $signed(sbe.result), regAddrToStr(rs1));
        else
            return $sformatf("%-12s %4s, %0d(%s)", mnemonic, regAddrToStr(rs2), $signed(sbe.result), regAddrToStr(rs1));
    endfunction // printSInstr

    function string printAMOInstr();
        string mnemonic;
        // words
        if (instr[14:12] == 3'h2) begin
            case (instr[31:27])
                5'h0:  mnemonic = "amoadd.w";
                5'h1:  mnemonic = "amoswap.w";
                5'h2:  mnemonic = "lr.w";
                5'h3:  mnemonic = "sc.w";
                5'h4:  mnemonic = "amoxor.w";
                5'h8:  mnemonic = "amoor.w";
                5'hC:  mnemonic = "amoand.w";
                5'h10: mnemonic = "amomin.w";
                5'h14: mnemonic = "amomax.w";
                5'h18: mnemonic = "amominu.w";
                5'h1C: mnemonic = "amomax.w";
                default: return printMnemonic("INVALID");
            endcase
        // doubles
        end else if (instr[14:12] == 3'h3) begin
            case (instr[31:27])
                5'h0:  mnemonic = "amoadd.d";
                5'h1:  mnemonic = "amoswap.d";
                5'h2:  mnemonic = "lr.d";
                5'h3:  mnemonic = "sc.d";
                5'h4:  mnemonic = "amoxor.d";
                5'h8:  mnemonic = "amoor.d";
                5'hC:  mnemonic = "amoand.d";
                5'h10: mnemonic = "amomin.d";
                5'h14: mnemonic = "amomax.d";
                5'h18: mnemonic = "amominu.d";
                5'h1C: mnemonic = "amomax.d";
                default: return printMnemonic("INVALID");
            endcase
        end else return printMnemonic("INVALID");

        result_regs.push_back(sbe.rd);
        read_regs.push_back(sbe.rs2);
        read_regs.push_back(sbe.rs1);
        // save the immediate for calculating the virtual address
        this.imm = 0;

        return $sformatf("%-16s %s, %s,(%s)", mnemonic, regAddrToStr(sbe.rd), regAddrToStr(sbe.rs2), regAddrToStr(sbe.rs1));
    endfunction

    function string printMulInstr(logic is_op32);
        string s = "";
        case (this.instr[14:12])
            3'b000: s = "mul";
            3'b001: s = "mulh";
            3'b010: s = "mulhsu";
            3'b011: s = "mulhu";
            3'b100: s = "div";
            3'b101: s = "divu";
            3'b110: s = "rem";
            3'b111: s = "remu";
        endcase
        // if it is a 32 bit instruction concatenate a w on it
        if (is_op32) s = {s, "w"};
        return this.printRInstr(s);
    endfunction
  endclass
`endif
