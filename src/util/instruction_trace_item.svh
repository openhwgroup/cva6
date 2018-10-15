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

class instruction_trace_item;
    // keep a couple of general purpose information inside this instruction item
    time               simtime;
    longint unsigned   cycle;
    scoreboard_entry_t sbe;
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
    logic [63:0]       paddr;
    string             priv_lvl;
    branchpredict_t    bp;

    logic [4:0] rs1, rs2, rs3, rd;

    // constructor creating a new instruction trace item, e.g.: a single instruction with all relevant information
    function new (time simtime, longint unsigned cycle, scoreboard_entry_t sbe, logic [31:0] instr, logic [63:0] gp_reg_file [32],
                logic [63:0] fp_reg_file [32], logic [63:0] result, logic [63:0] paddr, riscv::priv_lvl_t priv_lvl, logic debug_mode, branchpredict_t bp);
        this.simtime  = simtime;
        this.cycle    = cycle;
        this.pc       = sbe.pc;
        this.sbe      = sbe;
        this.instr    = instr;
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
            riscv::CSR_FFLAGS:     return "fflags";
            riscv::CSR_FRM:        return "frm";
            riscv::CSR_FCSR:       return "fcsr";
            riscv::CSR_SSTATUS:    return "sstatus";
            riscv::CSR_SIE:        return "sie";
            riscv::CSR_STVEC:      return "stvec";
            riscv::CSR_SCOUNTEREN: return "scounteren";
            riscv::CSR_SSCRATCH:   return "sscratch";
            riscv::CSR_SEPC:       return "sepc";
            riscv::CSR_SCAUSE:     return "scause";
            riscv::CSR_STVAL:      return "stval";
            riscv::CSR_SIP:        return "sip";
            riscv::CSR_SATP:       return "satp";

            riscv::CSR_MSTATUS:    return "mstatus";
            riscv::CSR_MISA:       return "misa";
            riscv::CSR_MEDELEG:    return "medeleg";
            riscv::CSR_MIDELEG:    return "mideleg";
            riscv::CSR_MIE:        return "mie";
            riscv::CSR_MTVEC:      return "mtvec";
            riscv::CSR_MCOUNTEREN: return "mcounteren";
            riscv::CSR_MSCRATCH:   return "mscratch";
            riscv::CSR_MEPC:       return "mepc";
            riscv::CSR_MCAUSE:     return "mcause";
            riscv::CSR_MTVAL:      return "mtval";
            riscv::CSR_MIP:        return "mip";
            riscv::CSR_PMPCFG0:    return "pmpcfg0";
            riscv::CSR_PMPADDR0:   return "pmpaddr0";
            riscv::CSR_MVENDORID:  return "mvendorid";
            riscv::CSR_MARCHID:    return "marchid";
            riscv::CSR_MIMPID:     return "mimpid";
            riscv::CSR_MHARTID:    return "mhartid";
            riscv::CSR_MCYCLE:     return "mcycle";
            riscv::CSR_MINSTRET:   return "minstret";

            riscv::CSR_TSELECT:    return "tselect";
            riscv::CSR_TDATA1:     return "tdata1";
            riscv::CSR_TDATA2:     return "tdata2";
            riscv::CSR_TDATA3:     return "tdata3";
            riscv::CSR_TINFO:      return "tinfo";

            riscv::CSR_DCSR:       return "dcsr";
            riscv::CSR_DPC:        return "dpc";
            riscv::CSR_DSCRATCH0:  return "dscratch0";
            riscv::CSR_DSCRATCH1:  return "dscratch1";

            riscv::CSR_CYCLE:      return "cycle";
            riscv::CSR_TIME:       return "time";
            riscv::CSR_INSTRET:    return "instret";

            default:        return $sformatf("%0h", addr);
        endcase
    endfunction

    function string printInstr();
        string s;

        case (instr) inside
             // Aliases
            32'h00_00_00_13:           s = this.printMnemonic("nop");
            // Regular opcodes
            INSTR_LUI:                 s = this.printUInstr("lui");
            INSTR_AUIPC:               s = this.printUInstr("auipc");
            INSTR_JAL:                 s = this.printJump();
            INSTR_JALR:                s = this.printJump();
            // BRANCH
            INSTR_BEQZ:                s = this.printSBInstr("beqz");
            INSTR_BEQ:                 s = this.printSBInstr("beq");
            INSTR_BNEZ:                s = this.printSBInstr("bnez");
            INSTR_BNE:                 s = this.printSBInstr("bne");
            INSTR_BLTZ:                s = this.printSBInstr("bltz");
            INSTR_BLT:                 s = this.printSBInstr("blt");
            INSTR_BGEZ:                s = this.printSBInstr("bgez");
            INSTR_BGE:                 s = this.printSBInstr("bge");
            INSTR_BLTU:                s = this.printSBInstr("bltu");
            INSTR_BGEU:                s = this.printSBInstr("bgeu");
            // OPIMM
            INSTR_LI:                  s = this.printIInstr("li");
            INSTR_ADDI:                s = this.printIInstr("addi");
            INSTR_SLTI:                s = this.printIInstr("slti");
            INSTR_SLTIU:               s = this.printIInstr("sltiu");
            INSTR_XORI:                s = this.printIInstr("xori");
            INSTR_ORI:                 s = this.printIInstr("ori");
            INSTR_ANDI:                s = this.printIInstr("andi");
            INSTR_SLLI:                s = this.printIuInstr("slli");
            INSTR_SRLI:                s = this.printIuInstr("srli");
            INSTR_SRAI:                s = this.printIuInstr("srai");
            // OPIMM32
            INSTR_ADDIW:               s = this.printIInstr("addiw");
            INSTR_SLLIW:               s = this.printIuInstr("slliw");
            INSTR_SRLIW:               s = this.printIuInstr("srliw");
            INSTR_SRAIW:               s = this.printIuInstr("sraiw");
            // OP
            INSTR_ADD:                 s = this.printRInstr("add");
            INSTR_SUB:                 s = this.printRInstr("sub");
            INSTR_SLL:                 s = this.printRInstr("sll");
            INSTR_SLT:                 s = this.printRInstr("slt");
            INSTR_SLTU:                s = this.printRInstr("sltu");
            INSTR_XOR:                 s = this.printRInstr("xor");
            INSTR_SRL:                 s = this.printRInstr("srl");
            INSTR_SRA:                 s = this.printRInstr("sra");
            INSTR_OR:                  s = this.printRInstr("or");
            INSTR_AND:                 s = this.printRInstr("and");
            INSTR_MUL:                 s = this.printMulInstr(1'b0);
            // OP32
            INSTR_ADDW:                s = this.printRInstr("addw");
            INSTR_SUBW:                s = this.printRInstr("subw");
            INSTR_SLLW:                s = this.printRInstr("sllw");
            INSTR_SRLW:                s = this.printRInstr("srlw");
            INSTR_SRAW:                s = this.printRInstr("sraw");
            INSTR_MULW:                s = this.printMulInstr(1'b1);
            // FP
            INSTR_FMADD:               s = this.printR4Instr("fmadd");
            INSTR_FMSUB:               s = this.printR4Instr("fmsub");
            INSTR_FNSMSUB:             s = this.printR4Instr("fnmsub");
            INSTR_FNMADD:              s = this.printR4Instr("fnmadd");

            INSTR_FADD:                s = this.printRFBCInstr("fadd", 1'b1);
            INSTR_FSUB:                s = this.printRFBCInstr("fsub", 1'b1);
            INSTR_FMUL:                s = this.printRFInstr("fmul", 1'b1);
            INSTR_FDIV:                s = this.printRFInstr("fdiv", 1'b1);
            INSTR_FSQRT:               s = this.printRFInstr1Op("fsqrt", 1'b1);
            INSTR_FSGNJ:               s = this.printRFInstr("fsgnj", 1'b0);
            INSTR_FSGNJN:              s = this.printRFInstr("fsgnjn", 1'b0);
            INSTR_FSGNJX:              s = this.printRFInstr("fsgnjx", 1'b0);
            INSTR_FMIN:                s = this.printRFInstr("fmin", 1'b0);
            INSTR_FMAX:                s = this.printRFInstr("fmax", 1'b0);
            INSTR_FLE:                 s = this.printRFInstr("fle", 1'b0);
            INSTR_FLT:                 s = this.printRFInstr("flt", 1'b0);
            INSTR_FEQ:                 s = this.printRFInstr("feq", 1'b0);

            INSTR_FCLASS:              s = this.printRFInstr1Op("fclass", 1'b0);

            INSTR_FCVT_F2F,
            INSTR_FMV_F2X,
            INSTR_FMV_X2F,
            INSTR_FCVT_F2I,
            INSTR_FCVT_I2F:            s = this.printFpSpecialInstr(); // these are a mess to do nicely
            // FENCE
            INSTR_FENCE:               s = this.printMnemonic("fence");
            INSTR_FENCEI:              s = this.printMnemonic("fence.i");
            // SYSTEM (CSR manipulation)
            INSTR_CSRW:                s = this.printCSRInstr("csrw");
            INSTR_CSRRW:               s = this.printCSRInstr("csrrw");
            INSTR_CSRR:                s = this.printCSRInstr("csrr");
            INSTR_CSRRS:               s = this.printCSRInstr("csrrs");
            INSTR_CSRS:                s = this.printCSRInstr("csrs");
            INSTR_CSRRC:               s = this.printCSRInstr("csrrc");
            INSTR_CSRC:                s = this.printCSRInstr("csrc");

            INSTR_CSRWI:               s = this.printCSRInstr("csrwi");
            INSTR_CSRRWI:              s = this.printCSRInstr("csrrwi");
            INSTR_CSRSI:               s = this.printCSRInstr("csrsi");
            INSTR_CSRRSI:              s = this.printCSRInstr("csrrsi");
            INSTR_CSRCI:               s = this.printCSRInstr("csrci");
            INSTR_CSRRCI:              s = this.printCSRInstr("csrrci");
            // SYSTEM (others)
            INSTR_ECALL:               s = this.printMnemonic("ecall");
            INSTR_EBREAK:              s = this.printMnemonic("ebreak");
            INSTR_MRET:                s = this.printMnemonic("mret");
            INSTR_SRET:                s = this.printMnemonic("sret");
            INSTR_DRET:                s = this.printMnemonic("dret");
            INSTR_WFI:                 s = this.printMnemonic("wfi");
            INSTR_SFENCE:              s = this.printMnemonic("sfence.vma");
            // loads and stores
            INSTR_LOAD,
            INSTR_LOAD_FP:             s = this.printLoadInstr();
            INSTR_STORE,
            INSTR_STORE_FP:            s = this.printStoreInstr();
            INSTR_AMO:                 s = this.printAMOInstr();
            default:                   s = this.printMnemonic("INVALID");
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
            // check of the instrction was a load or store
            INSTR_STORE,
            INSTR_STORE_FP: begin
                logic [63:0] vaddress = gp_reg_file[read_regs[1]] + this.imm;
                s = $sformatf("%s VA: %x PA: %x", s, vaddress, this.paddr);
            end
            INSTR_LOAD,
            INSTR_LOAD_FP: begin
                logic [63:0] vaddress = gp_reg_file[read_regs[0]] + this.imm;
                s = $sformatf("%s VA: %x PA: %x", s, vaddress, this.paddr);
            end
        endcase
        return s;
    endfunction : printInstr

    // Return the current privilege level as a string
    function string getPrivLevel(input riscv::priv_lvl_t priv_lvl);
        case (priv_lvl)
            riscv::PRIV_LVL_M: return "M";
            riscv::PRIV_LVL_S: return "S";
            riscv::PRIV_LVL_U: return "U";
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
        result_fpr.push_back(is_rd_fpr(sbe.op));
        read_regs.push_back(rs2);
        read_fpr.push_back(is_rs2_fpr(sbe.op));
        read_regs.push_back(sbe.result[4:0]);
        read_fpr.push_back(is_imm_fpr(sbe.op));

        if (use_rnd && instr[14:12]!=3'b111)
            return $sformatf("%-12s %4s, %s, %s, %s", $sformatf("%s.%s",mnemonic, fpFmtToStr(instr[26:25])), is_rd_fpr(sbe.op)?fpRegAddrToStr(rd):regAddrToStr(rd), is_rs2_fpr(sbe.op)?fpRegAddrToStr(rs2):regAddrToStr(rs2), is_imm_fpr(sbe.op)?fpRegAddrToStr(sbe.result[4:0]):regAddrToStr(sbe.result[4:0]), fpRmToStr(instr[14:12]));
        else
            return $sformatf("%-12s %4s, %s, %s", $sformatf("%s.%s",mnemonic, fpFmtToStr(instr[26:25])), is_rd_fpr(sbe.op)?fpRegAddrToStr(rd):regAddrToStr(rd), is_rs2_fpr(sbe.op)?fpRegAddrToStr(rs2):regAddrToStr(rs2), is_imm_fpr(sbe.op)?fpRegAddrToStr(sbe.result[4:0]):regAddrToStr(sbe.result[4:0]));
    endfunction // printRFInstr

    function string printRFInstr(input string mnemonic, input bit use_rnd);

        result_regs.push_back(rd);
        result_fpr.push_back(is_rd_fpr(sbe.op));
        read_regs.push_back(rs1);
        read_fpr.push_back(is_rs1_fpr(sbe.op));
        read_regs.push_back(rs2);
        read_fpr.push_back(is_rs2_fpr(sbe.op));

        if (use_rnd && instr[14:12]!=3'b111)
            return $sformatf("%-12s %4s, %s, %s, %s", $sformatf("%s.%s",mnemonic, fpFmtToStr(instr[26:25])), is_rd_fpr(sbe.op)?fpRegAddrToStr(rd):regAddrToStr(rd), is_rs1_fpr(sbe.op)?fpRegAddrToStr(rs1):regAddrToStr(rs1), is_rs2_fpr(sbe.op)?fpRegAddrToStr(rs2):regAddrToStr(rs2), fpRmToStr(instr[14:12]));
        else
            return $sformatf("%-12s %4s, %s, %s", $sformatf("%s.%s",mnemonic, fpFmtToStr(instr[26:25])), is_rd_fpr(sbe.op)?fpRegAddrToStr(rd):regAddrToStr(rd), is_rs1_fpr(sbe.op)?fpRegAddrToStr(rs1):regAddrToStr(rs1), is_rs2_fpr(sbe.op)?fpRegAddrToStr(rs2):regAddrToStr(rs2));
    endfunction // printRFInstr

    function string printRFInstr1Op(input string mnemonic, input bit use_rnd);

        result_regs.push_back(rd);
        result_fpr.push_back(is_rd_fpr(sbe.op));
        read_regs.push_back(rs1);
        read_fpr.push_back(is_rs1_fpr(sbe.op));

        if (use_rnd && instr[14:12]!=3'b111)
            return $sformatf("%-12s %4s, %s, %s", $sformatf("%s.%s",mnemonic, fpFmtToStr(instr[26:25])), is_rd_fpr(sbe.op)?fpRegAddrToStr(rd):regAddrToStr(rd), is_rs1_fpr(sbe.op)?fpRegAddrToStr(rs1):regAddrToStr(rs1), fpRmToStr(instr[14:12]));
        else
            return $sformatf("%-12s %4s, %s", $sformatf("%s.%s",mnemonic, fpFmtToStr(instr[26:25])), is_rd_fpr(sbe.op)?fpRegAddrToStr(rd):regAddrToStr(rd), is_rs1_fpr(sbe.op)?fpRegAddrToStr(rs1):regAddrToStr(rs1));
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
        result_fpr.push_back(is_rd_fpr(sbe.op));
        read_regs.push_back(rs1);
        read_fpr.push_back(is_rs1_fpr(sbe.op));

        case (sbe.op)
            FCVT_F2F : return $sformatf("%-12s %4s, %s, %s", $sformatf("fcvt.%s.%s", fpFmtToStr(instr[26:25]), fpFmtToStr(instr[21:20])), fpRegAddrToStr(rd), fpRegAddrToStr(rs1), fpRmToStr(instr[14:12]));
            FCVT_F2I : return $sformatf("%-12s %4s, %s, %s", $sformatf("fcvt.%s.%s", intFmtToStr(instr[21:20]), fpFmtToStr(instr[26:25])), regAddrToStr(rd), fpRegAddrToStr(rs1), fpRmToStr(instr[14:12]));
            FCVT_I2F : return $sformatf("%-12s %4s, %s, %s", $sformatf("fcvt.%s.%s", fpFmtToStr(instr[26:25]), intFmtToStr(instr[21:20])), fpRegAddrToStr(rd), regAddrToStr(rs1), fpRmToStr(instr[14:12]));
            FMV_F2X  : return $sformatf("%-12s %4s, %s", $sformatf("fmv.x.%s", fmvFpFmtToStr(instr[26:25])), regAddrToStr(rd), fpRegAddrToStr(rs1));
            FMV_X2F  : return $sformatf("%-12s %4s, %s", $sformatf("fmv.%s.x", fmvFpFmtToStr(instr[26:25])), fpRegAddrToStr(rd), regAddrToStr(rs1));
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

        if (rs2 == 0)
            return $sformatf("%-12s %4s, pc + %0d", mnemonic, regAddrToStr(rs1), $signed(sbe.result));
        else
            return $sformatf("%-12s %4s, %s, pc + %0d", mnemonic, regAddrToStr(rs1), regAddrToStr(rs2), $signed(sbe.result));
    endfunction // printIuInstr

    function string printUInstr(input string mnemonic);

        result_regs.push_back(rd);
        result_fpr.push_back(1'b0);

        return $sformatf("%-12s %4s, 0x%0h", mnemonic, regAddrToStr(rd), sbe.result[31:12]);
    endfunction // printUInstr

    function string printJump();
        string mnemonic;
        case (instr[6:0])
            riscv::OpcodeJalr: begin
                // is this a return?
                if (rd == 'b0 && (rs1 == 'h1 || rs1 == 'h5)) begin
                    return this.printMnemonic("ret");
                end else begin
                    return this.printIInstr("jalr");
                end
            end

            riscv::OpcodeJal: begin
                if (rd == 'b0)
                    return this.printUJInstr("j");
                else
                return this.printUJInstr("jal");
            end
        endcase

    endfunction

    function string printUJInstr(input string mnemonic);

        result_regs.push_back(rd);
        result_fpr.push_back(1'b0);
        // jump instruction
        if (rd == 0)
            return $sformatf("%-12s   pc + %0d", mnemonic, $signed(sbe.result));
        else
            return $sformatf("%-12s %4s, pc + %0d", mnemonic, regAddrToStr(rd), $signed(sbe.result));
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

    function string printLoadInstr();
      string mnemonic;

        case (instr[14:12])
          3'b000: mnemonic = "lb";
          3'b001: mnemonic = "lh";
          3'b010: mnemonic = "lw";
          3'b100: mnemonic = "lbu";
          3'b101: mnemonic = "lhu";
          3'b110: mnemonic = "lwu";
          3'b011: mnemonic = "ld";
          default: return printMnemonic("INVALID");
        endcase

        if (instr[6:0] == riscv::OpcodeLoadFp)
            mnemonic = $sformatf("f%s",mnemonic);

        result_regs.push_back(rd);
        result_fpr.push_back(is_rd_fpr(sbe.op));
        read_regs.push_back(rs1);
        read_fpr.push_back(1'b0);
        // save the immediate for calculating the virtual address
        this.imm = sbe.result;

        if (instr[6:0] == riscv::OpcodeLoadFp)
            return $sformatf("%-12s %4s, %0d(%s)", mnemonic, fpRegAddrToStr(rd), $signed(sbe.result), regAddrToStr(rs1));
        else
            return $sformatf("%-12s %4s, %0d(%s)", mnemonic, regAddrToStr(rd), $signed(sbe.result), regAddrToStr(rs1));
    endfunction

    function string printStoreInstr();
        string mnemonic;
        case (instr[14:12])
          3'b000:  mnemonic = "sb";
          3'b001:  mnemonic = "sh";
          3'b010:  mnemonic = "sw";
          3'b011:  mnemonic = "sd";
          default: return printMnemonic("INVALID");
        endcase

        if (instr[6:0] == riscv::OpcodeStoreFp)
            mnemonic = $sformatf("f%s",mnemonic);

        read_regs.push_back(rs2);
        read_fpr.push_back(is_rs2_fpr(sbe.op));
        read_regs.push_back(rs1);
        read_fpr.push_back(1'b0);
        // save the immediate for calculating the virtual address
        this.imm = sbe.result;

        if (instr[6:0] == riscv::OpcodeStoreFp)
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
        if (is_op32)
            s = {s, "w"};

        return this.printRInstr(s);

    endfunction
  endclass
