// Author: Florian Zaruba, ETH Zurich - Andreas Traber, ACP
// Date: 30.05.2017
// Description: Instruction tracer single instruction item
//
// Copyright (C) 2017 ETH Zurich, University of Bologna
// All rights reserved.
//
// This code is under development and not yet released to the public.
// Until it is released, the code is under the copyright of ETH Zurich and
// the University of Bologna, and may contain confidential and/or unpublished
// work. Any reuse/redistribution is strictly forbidden without written
// permission from ETH Zurich.
//
// Bug fixes and contributions will eventually be released under the
// SolderPad open hardware license in the context of the PULP platform
// (http://www.pulp-platform.org), under the copyright of ETH Zurich and the
// University of Bologna.
//
class instruction_trace_item;
    // keep a couple of general purpose information inside this instruction item
    time               simtime;
    longint unsigned   cycle;
    scoreboard_entry   sbe;
    logic [31:0]       pc;
    logic [31:0]       instr;
    logic [63:0]       reg_file [32];
    logic [4:0]        read_regs [$];
    logic [4:0]        result_regs [$];
    logic [63:0]       imm;
    logic [63:0]       result;
    logic [63:0]       paddr;

    // constructor creating a new instruction trace item, e.g.: a single instruction with all relevant information
    function new (time simtime, longint unsigned cycle, scoreboard_entry sbe, logic [31:0] instr, logic [63:0] reg_file [32], logic [63:0] result, logic [63:0] paddr);
        this.simtime  = simtime;
        this.cycle    = cycle;
        this.pc       = sbe.pc;
        this.sbe      = sbe;
        this.instr    = instr;
        this.reg_file = reg_file;
        this.result   = result;
        this.paddr    = paddr;
    endfunction
    // convert register address to ABI compatible form
    function string regAddrToStr(logic [5:0] addr);
        case (addr)
            0: return "x0";
            1: return "ra";
            2: return "sp";
            3: return "gp";
            4: return "tp";
            5, 6, 7: return $sformatf("t%0d", (addr - 5));
            8, 9: return $sformatf("s%0d", (addr - 8));
            10, 11, 12, 13, 14, 15, 16, 17: return $sformatf("a%0d", (addr-10));
            28, 29, 30, 31: return $sformatf("t%0d", (addr-25));
            default: return $sformatf("s%0d", (addr - 16));
        endcase
    endfunction

    function string csrAddrToStr(logic [11:0] addr);
        case (addr)
            CSR_SSTATUS:    return "sstatus";
            CSR_SIE:        return "sie";
            CSR_STVEC:      return "stvec";
            CSR_SSCRATCH:   return "sscratch";
            CSR_SEPC:       return "sepc";
            CSR_SCAUSE:     return "scause";
            CSR_STVAL:      return "stval";
            CSR_SIP:        return "sip";
            CSR_SATP:       return "satp";

            CSR_MSTATUS:    return "mstatus";
            CSR_MISA:       return "misa";
            CSR_MEDELEG:    return "medeleg";
            CSR_MIDELEG:    return "mideleg";
            CSR_MIE:        return "mie";
            CSR_MTVEC:      return "mtvec";
            CSR_MSCRATCH:   return "mscratch";
            CSR_MEPC:       return "mepc";
            CSR_MCAUSE:     return "mcause";
            CSR_MTVAL:      return "mtval";
            CSR_MIP:        return "mip";
            CSR_MVENDORID:  return "mvendorid";
            CSR_MARCHID:    return "marchid";
            CSR_MIMPID:     return "mimpid";
            CSR_MHARTID:    return "mhartid";
            CSR_CYCLE:      return "cycle";
            CSR_TIME:       return "time";
            CSR_INSTRET:    return "instret";

            default:        return $sformatf("%0h", addr);
        endcase
    endfunction

    function string printInstr();
        string s;

        casex (instr)
             // Aliases
            32'h00_00_00_13:           s = this.printMnemonic("nop");
            // Regular opcodes
            INSTR_LUI:                 s = this.printUInstr("lui");
            INSTR_AUIPC:               s = this.printUInstr("auipc");
            INSTR_J:                   s = this.printUJInstr("j");
            INSTR_JAL:                 s = this.printUJInstr("jal");
            INSTR_JALR:                s = this.printIInstr("jalr");
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
            // OP32
            INSTR_ADDW:                s = this.printRInstr("addw");
            INSTR_SUBW:                s = this.printRInstr("subw");
            INSTR_SLLW:                s = this.printRInstr("sllw");
            INSTR_SRLW:                s = this.printRInstr("srlw");
            INSTR_SRAW:                s = this.printRInstr("sraw");
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
            INSTR_WFI:                 s = this.printMnemonic("wfi");
            INSTR_SFENCE:              s = this.printMnemonic("sfence.vma");
            // loads and stores
            INSTR_LOAD:                s = this.printLoadInstr();
            INSTR_STORE:               s = this.printStoreInstr();
            default:                   s = this.printMnemonic("INVALID");
        endcase


        s = $sformatf("%10t %10d %h %h %-36s", simtime,
                                             cycle,
                                             sbe.pc,
                                             instr,
                                             s);

        foreach (result_regs[i]) begin
            if (result_regs[i] != 0)
                s = $sformatf("%s %-4s:%16x", s, regAddrToStr(result_regs[i]), this.result);
        end


        foreach (read_regs[i]) begin
            if (read_regs[i] != 0)
                s = $sformatf("%s %-4s:%16x", s, regAddrToStr(read_regs[i]), reg_file[read_regs[i]]);
        end
        casex (instr)
            // check of the instrction was a load or store
            INSTR_LOAD, INSTR_STORE: begin
                logic [63:0] vaddress = reg_file[read_regs[0]] + this.imm;
                s = $sformatf("%s VA: %x PA: %x", s, vaddress, this.paddr);
            end
        endcase
        return s;
    endfunction

    function string printMnemonic(input string mnemonic);
        return mnemonic;
    endfunction // printMnemonic

    function string printRInstr(input string mnemonic);

        result_regs.push_back(sbe.rd);
        read_regs.push_back(sbe.rs1);
        read_regs.push_back(sbe.rs2);

        return $sformatf("%-16s %s, %s, %s", mnemonic, regAddrToStr(sbe.rd), regAddrToStr(sbe.rs1), regAddrToStr(sbe.rs2));
    endfunction // printRInstr

    function string printIInstr(input string mnemonic);

        result_regs.push_back(sbe.rd);
        read_regs.push_back(sbe.rs1);

        if (sbe.rs1 == 0)
            return $sformatf("%-16s %s, %0d", mnemonic, regAddrToStr(sbe.rd), $signed(sbe.result));

        return $sformatf("%-16s %s, %s, %0d", mnemonic, regAddrToStr(sbe.rd), regAddrToStr(sbe.rs1), $signed(sbe.result));
    endfunction // printIInstr

    function string printIuInstr(input string mnemonic);

        result_regs.push_back(sbe.rd);
        read_regs.push_back(sbe.rs1);

        return $sformatf("%-16s %s, %s, 0x%0x", mnemonic, regAddrToStr(sbe.rd), regAddrToStr(sbe.rs1), sbe.result);
    endfunction // printIuInstr

    function string printSBInstr(input string mnemonic);

        read_regs.push_back(sbe.rs1);
        read_regs.push_back(sbe.rs2);

        if (sbe.rs2 == 0)
            return $sformatf("%-16s %s, pc + %0d", mnemonic, regAddrToStr(sbe.rs1), $signed(sbe.result));
        else
            return $sformatf("%-16s %s, %s, pc + %0d", mnemonic, regAddrToStr(sbe.rs1), regAddrToStr(sbe.rs2), $signed(sbe.result));
    endfunction // printIuInstr

    function string printUInstr(input string mnemonic);

        result_regs.push_back(sbe.rd);

        return $sformatf("%-16s %s, 0x%0h", mnemonic, regAddrToStr(sbe.rd), sbe.result[31:12]);
    endfunction // printUInstr

    function string printUJInstr(input string mnemonic);

        result_regs.push_back(sbe.rd);
        // jump instruction
        if (sbe.rd == 0)
            return $sformatf("%-16s pc + %0d", mnemonic, $signed(sbe.result));
        else
            return $sformatf("%-16s %s, pc + %0d", mnemonic, regAddrToStr(sbe.rd), $signed(sbe.result));
    endfunction // printUJInstr

    function string printCSRInstr(input string mnemonic);

        result_regs.push_back(sbe.rd);
        if (instr[14] == 0) begin
        read_regs.push_back(sbe.rs1);
            if (sbe.rd != 0 && sbe.rs1 != 0) begin
                  return $sformatf("%-16s %s, %s, %s", mnemonic, regAddrToStr(sbe.rd), regAddrToStr(sbe.rs1), csrAddrToStr(sbe.result[11:0]));
            // don't display instructions which write to zero
            end else if (sbe.rd == 0) begin
                  return $sformatf("%-16s %s, %s", mnemonic, regAddrToStr(sbe.rs1), csrAddrToStr(sbe.result[11:0]));
            end else if (sbe.rs1 == 0) begin
                return $sformatf("%-16s %s, %s", mnemonic, regAddrToStr(sbe.rd), csrAddrToStr(sbe.result[11:0]));
            end
        end else begin
            if (sbe.rd != 0 && sbe.rs1 != 0) begin
                  return $sformatf("%-16s %s, %d, %s", mnemonic, regAddrToStr(sbe.rd), $unsigned(sbe.rs1), csrAddrToStr(sbe.result[11:0]));
            // don't display instructions which write to zero
            end else if (sbe.rd == 0) begin
                  return $sformatf("%-16s %d, %s", mnemonic, $unsigned(sbe.rs1), csrAddrToStr(sbe.result[11:0]));
            end else if (sbe.rs1 == 0) begin
                return $sformatf("%-16s %s, %s", mnemonic, regAddrToStr(sbe.rd), csrAddrToStr(sbe.result[11:0]));
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

        read_regs.push_back(sbe.rs1);
        result_regs.push_back(sbe.rd);
        // save the immediate for calculating the virtual address
        this.imm = sbe.result;

        return $sformatf("%-16s %s, %0d(%s)", mnemonic, regAddrToStr(sbe.rd), $signed(sbe.result), regAddrToStr(sbe.rs1));
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

        read_regs.push_back(sbe.rs1);
        read_regs.push_back(sbe.rs2);
        // save the immediate for calculating the virtual address
        this.imm = sbe.result;

        return $sformatf("%-16s %s, %0d(%s)", mnemonic, regAddrToStr(sbe.rs2), $signed(sbe.result), regAddrToStr(sbe.rs1));

    endfunction // printSInstr

    function string printMulInstr();
      // string mnemonic;
      // string str_suf;
      // string str_imm;
      // string str_asm;
      // begin

      //   // always read rs1 and rs2 and write rd
      //   regs_read.push_back('{rs1, rs1_value});
      //   regs_read.push_back('{rs2, rs2_value});
      //   regs_write.push_back('{rd, 'x});

      //   if (instr[12])
      //     regs_read.push_back('{rd, rs3_value});

      //   case ({instr[31:30], instr[14]})
      //     3'b000: str_suf = "u";
      //     3'b001: str_suf = "uR";
      //     3'b010: str_suf = "hhu";
      //     3'b011: str_suf = "hhuR";
      //     3'b100: str_suf = "s";
      //     3'b101: str_suf = "sR";
      //     3'b110: str_suf = "hhs";
      //     3'b111: str_suf = "hhsR";
      //   endcase

      //   if (instr[12])
      //     mnemonic = "p.mac";
      //   else
      //     mnemonic = "p.mul";

      //   if (imm_s3_type[4:0] != 5'b00000)
      //     str_asm = $sformatf("%s%sN", mnemonic, str_suf);
      //   else
      //     str_asm = $sformatf("%s%s", mnemonic, str_suf);

      //   if (instr[29:25] != 5'b00000)
      //     str = $sformatf("%-16s x%0d, x%0d, x%0d, %0d", str_asm, rd, rs1, rs2, $unsigned(imm_s3_type[4:0]));
      //   else
      //     str = $sformatf("%-16s x%0d, x%0d, x%0d", str_asm, rd, rs1, rs2);
      // end
      return "";
    endfunction
  endclass