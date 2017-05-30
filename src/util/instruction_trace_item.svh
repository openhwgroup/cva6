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
    logic [63:0]       result;

    // constructor creating a new instruction trace item, e.g.: a single instruction with all relevant information
    function new (time simtime, longint unsigned cycle, scoreboard_entry sbe, logic [31:0] instr, logic [63:0] reg_file [32], logic [63:0] result);
        this.simtime  = simtime;
        this.cycle    = cycle;
        this.pc       = sbe.pc;
        this.sbe      = sbe;
        this.instr    = instr;
        this.reg_file = reg_file;
        this.result   = result;
    endfunction

    function string regAddrToStr(logic [5:0] addr);
          return $sformatf("x%0d:", addr);
    endfunction

    function string printInstr();
        string s;

        casex (instr)
             // Aliases
            32'h00_00_00_13:           s = this.printMnemonic("nop");
            // Regular opcodes
            INSTR_LUI:                 s = this.printUInstr("lui");
            INSTR_AUIPC:               s = this.printUInstr("auipc");
            INSTR_JAL:                 s = this.printUJInstr("jal");
            INSTR_JALR:                s = this.printIInstr("jalr");
            // BRANCH
            INSTR_BEQ:                 s = this.printSBInstr("beq");
            INSTR_BNE:                 s = this.printSBInstr("bne");
            INSTR_BLT:                 s = this.printSBInstr("blt");
            INSTR_BGE:                 s = this.printSBInstr("bge");
            INSTR_BLTU:                s = this.printSBInstr("bltu");
            INSTR_BGEU:                s = this.printSBInstr("bgeu");
            // OPIMM
            INSTR_ADDI:                s = this.printIInstr("addi");
            INSTR_SLTI:                s = this.printIInstr("slti");
            INSTR_SLTIU:               s = this.printIInstr("sltiu");
            INSTR_XORI:                s = this.printIInstr("xori");
            INSTR_ORI:                 s = this.printIInstr("ori");
            INSTR_ANDI:                s = this.printIInstr("andi");
            INSTR_SLLI:                s = this.printIuInstr("slli");
            INSTR_SRLI:                s = this.printIuInstr("srli");
            INSTR_SRAI:                s = this.printIuInstr("srai");
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
            // FENCE
            INSTR_FENCE:               s = this.printMnemonic("fence");
            INSTR_FENCEI:              s = this.printMnemonic("fencei");
            // SYSTEM (CSR manipulation)
            INSTR_CSRRW:               s = this.printCSRInstr("csrrw");
            INSTR_CSRRS:               s = this.printCSRInstr("csrrs");
            INSTR_CSRRC:               s = this.printCSRInstr("csrrc");
            INSTR_CSRRWI:              s = this.printCSRInstr("csrrwi");
            INSTR_CSRRSI:              s = this.printCSRInstr("csrrsi");
            INSTR_CSRRCI:              s = this.printCSRInstr("csrrci");
            // SYSTEM (others)
            INSTR_ECALL:               s = this.printMnemonic("ecall");
            INSTR_EBREAK:              s = this.printMnemonic("ebreak");
            INSTR_ERET:                s = this.printMnemonic("eret");
            INSTR_WFI:                 s = this.printMnemonic("wfi");
            // loads and stores
            INSTR_LOAD:                s = this.printLoadInstr();
            INSTR_STORE:               s = this.printStoreInstr();
            default:                   s = this.printMnemonic("INVALID");
        endcase


        s = $sformatf("%t %15d %h %h %-36s", simtime,
                                             cycle,
                                             sbe.pc,
                                             instr,
                                             s);

        foreach (result_regs[i]) begin
            if (result_regs[i] != 0)
                s = $sformatf(s, " %-4s%16x", regAddrToStr(result_regs[i]), this.result);
        end


        foreach (read_regs[i]) begin
            if (read_regs[i] != 0)
                s = $sformatf(s, " %-4s%16x", regAddrToStr(read_regs[i]), reg_file[read_regs[i]]);
        end

        return s;
        // if (mem_access.size() > 0) begin
        //   mem_acc = mem_access.pop_front();

        //   $fwrite(f, "  PA:%08x", mem_acc.addr);
        // end

        // $fwrite(f, "\n");
    endfunction

    function string printMnemonic(input string mnemonic);
        return mnemonic;
    endfunction // printMnemonic

    function string printRInstr(input string mnemonic);

        result_regs.push_back(sbe.rd);
        read_regs.push_back(sbe.rs1);
        read_regs.push_back(sbe.rs2);

        return $sformatf("%-16s x%0d, x%0d, x%0d", mnemonic, sbe.rd, sbe.rs1, sbe.rs2);
    endfunction // printRInstr

    function string printIInstr(input string mnemonic);

        result_regs.push_back(sbe.rd);
        read_regs.push_back(sbe.rs1);

        return $sformatf("%-16s x%0d, x%0d, %0d", mnemonic, sbe.rd, sbe.rs1, $signed(sbe.result));
    endfunction // printIInstr

    function string printIuInstr(input string mnemonic);

        result_regs.push_back(sbe.rd);
        read_regs.push_back(sbe.rs1);

        return $sformatf("%-16s x%0d, x%0d, 0x%0x", mnemonic, sbe.rd, sbe.rs1, sbe.result);
    endfunction // printIuInstr

    function string printSBInstr(input string mnemonic);

        result_regs.push_back(sbe.rd);
        read_regs.push_back(sbe.rs1);

        return $sformatf("%-16s x%0d, x%0d, 0x%0x", mnemonic, sbe.rd, sbe.rs1, sbe.result);
    endfunction // printIuInstr

    function string printUInstr(input string mnemonic);

        result_regs.push_back(sbe.rd);

        return $sformatf("%-16s x%0d, 0x%0h", mnemonic, sbe.rd, sbe.result);
    endfunction // printUInstr

    function string printUJInstr(input string mnemonic);

        result_regs.push_back(sbe.rd);

        return $sformatf("%-16s x%0d, %0d", mnemonic, sbe.rd, $signed(sbe.result));
    endfunction // printUJInstr

    function string printCSRInstr(input string mnemonic);

        result_regs.push_back(sbe.rd);
        read_regs.push_back(sbe.rs1);

        if (instr[14] == 1'b0) begin
          return $sformatf("%-16s x%0d, x%0d, 0x%h", mnemonic, sbe.rd, sbe.rs1, sbe.result[11:0]);
        end else begin
          return $sformatf("%-16s x%0d, 0x%h, 0x%h", mnemonic, sbe.rd, sbe.rs1, sbe.result[11:0]);
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

        result_regs.push_back(sbe.rd);
        read_regs.push_back(sbe.rs1);

        return $sformatf("%-16s x%0d, %0d(x%0d)", mnemonic, sbe.rd, $signed(sbe.result), sbe.rs1);
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

        return $sformatf("%-16s x%0d, %0d(x%0d)", mnemonic, sbe.rs2, $signed(sbe.result), sbe.rs1);

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