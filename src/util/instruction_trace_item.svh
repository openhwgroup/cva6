class instruction_trace_item;
    time         simtime;
    integer      cycles;
    logic [31:0] pc;
    logic [31:0] instr;
    string       str;

    function new ();

    endfunction

    function string regAddrToStr(logic [5:0] addr);
          return $sformatf("x%0d", addr);
    endfunction

    function string printInstr(logic [63:0] instr);
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
            // SYSTEM (CSR man         ipulation)
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
            // opcodes with custom decoding
            {25'b?, OPCODE_LOAD}:      s = this.printLoadInstr();
            {25'b?, OPCODE_STORE}:     s = this.printStoreInstr();
            default:                   s = this.printMnemonic("INVALID");
        endcase

        return s;
        // $fwrite(f, "%t %15d %h %h %-36s", simtime,
        //                                   cycles,
        //                                   pc,
        //                                   instr,
        //                                   str);

        // foreach(regs_write[i]) begin
        //   if (regs_write[i].addr != 0)
        //     $fwrite(f, " %s=%08x", regAddrToStr(regs_write[i].addr), regs_write[i].value);
        // end

        // foreach(regs_read[i]) begin
        //   if (regs_read[i].addr != 0)
        //     $fwrite(f, " %s:%08x", regAddrToStr(regs_read[i].addr), regs_read[i].value);
        // end

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
        // return $sformatf("%-16s x%0d, x%0d, x%0d", mnemonic, rd, rs1, rs2);
        return mnemonic;
    endfunction // printRInstr

    function string printIInstr(input string mnemonic);
      // begin
      //   regs_read.push_back('{rs1, rs1_value});
      //   regs_write.push_back('{rd, 'x});
      //   str = $sformatf("%-16s x%0d, x%0d, %0d", mnemonic, rd, rs1, $signed(imm_i_type));
      // end
      return mnemonic;
    endfunction // printIInstr

    function string printIuInstr(input string mnemonic);
      // begin
      //   regs_read.push_back('{rs1, rs1_value});
      //   regs_write.push_back('{rd, 'x});
      //   str = $sformatf("%-16s x%0d, x%0d, 0x%0x", mnemonic, rd, rs1, imm_i_type);
      // end
      return mnemonic;
    endfunction // printIuInstr

    function string printSBInstr(input string mnemonic);
      // begin
      //   regs_read.push_back('{rs1, rs1_value});
      //   regs_write.push_back('{rd, 'x});
      //   str = $sformatf("%-16s x%0d, x%0d, 0x%0x", mnemonic, rd, rs1, imm_i_type);
      // end
      return mnemonic;
    endfunction // printIuInstr

    function string printUInstr(input string mnemonic);
      // begin
      //   regs_write.push_back('{rd, 'x});
      //   str = $sformatf("%-16s x%0d, 0x%0h", mnemonic, rd, {imm_u_type[31:12], 12'h000});
      // end
      return mnemonic;
    endfunction // printUInstr

    function string printUJInstr(input string mnemonic);
      // begin
      //   regs_write.push_back('{rd, 'x});
      //   str =  $sformatf("%-16s x%0d, %0d", mnemonic, rd, $signed(imm_uj_type));
      // end
      return mnemonic;
    endfunction // printUJInstr

    function string printCSRInstr(input string mnemonic);
      // logic [11:0] csr;
      // begin
      //   csr = instr[31:20];

      //   regs_write.push_back('{rd, 'x});

      //   if (instr[14] == 1'b0) begin
      //     regs_read.push_back('{rs1, rs1_value});
      //     str = $sformatf("%-16s x%0d, x%0d, 0x%h", mnemonic, rd, rs1, csr);
      //   end else begin
      //     str = $sformatf("%-16s x%0d, 0x%h, 0x%h", mnemonic, rd, imm_z_type, csr);
      //   end
      // end
      return mnemonic;
    endfunction // printCSRInstr

    function string printLoadInstr();
      // string mnemonic;
      // logic [2:0] size;
      // begin
      //   // detect reg-reg load and find size
      //   size = instr[14:12];
      //   if (instr[14:12] == 3'b111)
      //     size = instr[30:28];

      //   case (size)
      //     3'b000: mnemonic = "lb";
      //     3'b001: mnemonic = "lh";
      //     3'b010: mnemonic = "lw";
      //     3'b100: mnemonic = "lbu";
      //     3'b101: mnemonic = "lhu";
      //     3'b110: mnemonic = "p.elw";
      //     3'b011,
      //     3'b111: begin
      //       printMnemonic("INVALID");
      //       return;
      //     end
      //   endcase

      //   regs_write.push_back('{rd, 'x});

      //   if (instr[14:12] != 3'b111) begin
      //     // regular load
      //     if (instr[6:0] != OPCODE_LOAD_POST) begin
      //       regs_read.push_back('{rs1, rs1_value});
      //       str = $sformatf("%-16s x%0d, %0d(x%0d)", mnemonic, rd, $signed(imm_i_type), rs1);
      //     end else begin
      //       regs_read.push_back('{rs1, rs1_value});
      //       regs_write.push_back('{rs1, 'x});
      //       str = $sformatf("p.%-14s x%0d, %0d(x%0d!)", mnemonic, rd, $signed(imm_i_type), rs1);
      //     end
      //   end else begin
      //     // reg-reg load
      //     if (instr[6:0] != OPCODE_LOAD_POST) begin
      //       regs_read.push_back('{rs2, rs2_value});
      //       regs_read.push_back('{rs1, rs1_value});
      //       str = $sformatf("%-16s x%0d, x%0d(x%0d)", mnemonic, rd, rs2, rs1);
      //     end else begin
      //       regs_read.push_back('{rs2, rs2_value});
      //       regs_read.push_back('{rs1, rs1_value});
      //       regs_write.push_back('{rs1, 'x});
      //       str = $sformatf("p.%-14s x%0d, x%0d(x%0d!)", mnemonic, rd, rs2, rs1);
      //     end
      //   end
      // end
      return "";
    endfunction

    function string printStoreInstr();
      // string mnemonic;
      // begin

      //   case (instr[13:12])
      //     2'b00:  mnemonic = "sb";
      //     2'b01:  mnemonic = "sh";
      //     2'b10:  mnemonic = "sw";
      //     2'b11: begin
      //       printMnemonic("INVALID");
      //       return;
      //     end
      //   endcase

      //   if (instr[14] == 1'b0) begin
      //     // regular store
      //     if (instr[6:0] != OPCODE_STORE_POST) begin
      //       regs_read.push_back('{rs2, rs2_value});
      //       regs_read.push_back('{rs1, rs1_value});
      //       str = $sformatf("%-16s x%0d, %0d(x%0d)", mnemonic, rs2, $signed(imm_s_type), rs1);
      //     end else begin
      //       regs_read.push_back('{rs2, rs2_value});
      //       regs_read.push_back('{rs1, rs1_value});
      //       regs_write.push_back('{rs1, 'x});
      //       str = $sformatf("p.%-14s x%0d, %0d(x%0d!)", mnemonic, rs2, $signed(imm_s_type), rs1);
      //     end
      //   end else begin
      //     // reg-reg store
      //     if (instr[6:0] != OPCODE_STORE_POST) begin
      //       regs_read.push_back('{rs2, rs2_value});
      //       regs_read.push_back('{rs3, rs3_value});
      //       regs_read.push_back('{rs1, rs1_value});
      //       str = $sformatf("p.%-14s x%0d, x%0d(x%0d)", mnemonic, rs2, rs3, rs1);
      //     end else begin
      //       regs_read.push_back('{rs2, rs2_value});
      //       regs_read.push_back('{rs3, rs3_value});
      //       regs_read.push_back('{rs1, rs1_value});
      //       regs_write.push_back('{rs1, 'x});
      //       str = $sformatf("p.%-14s x%0d, x%0d(x%0d!)", mnemonic, rs2, rs3, rs1);
      //     end
      //   end
      // end
      return "";
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