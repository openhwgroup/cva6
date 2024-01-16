module zcmp_decoder  #(
  parameter config_pkg::cva6_cfg_t CVA6Cfg = config_pkg::cva6_cfg_empty) 
  (
  input   logic [31:0]  instr_i,
  input   logic         clk_i,  // Clock
  input   logic         rst_ni,  // Synchronous reset
  input   logic         is_push_pop_instr_i,
  input   logic         illegal_instr_i,
  input   logic         is_compressed_i,
  output  logic [31:0]  instr_o,
  output  logic         illegal_instr_o,
  output  logic         is_compressed_o,
  output  logic         fetch_stall //Wait while push/pop instructions expand
);
  
  // FSM States
  enum logic [2:0] {
    IDLE, INIT, PUSH_ADDI, POPRETZ_1, MOVE, PUSH_POP_INSTR_2
  } state_d, state_q;

  // Instruction Types
  enum logic[2:0] {
    PUSH, POP, POPRETZ, POPRET, MVA01S, MVSA01
  } zcmp_instr_type;

  // Temporary registers
  logic [3:0] reg_numbers;
  logic [8:0] stack_adj;
  logic [4:0] xreg1;
  logic [4:0] xreg2;
  logic [3:0] reg_numbers_d;
  logic [3:0] reg_numbers_q;
  logic [4:0] store_reg_q;
  logic [4:0] store_reg_d;
  logic [1:0] popretz_inst_q;
  logic [1:0] popretz_inst_d;  
  logic [11:0] offset_q;
  logic [11:0] offset_d;

  riscv::itype_t itype_inst;

  always_comb begin
    illegal_instr_o = 1'b0;
    fetch_stall     = 1'b0;
    instr_o         = instr_i;
    is_compressed_o = is_push_pop_instr_i ? 1'b1 : is_compressed_i;
    reg_numbers     = '0;
    stack_adj       = '0;
          
    state_d = state_q;
    offset_d = offset_q;
    reg_numbers_d = reg_numbers_q;
    store_reg_d = store_reg_q;
    popretz_inst_d = popretz_inst_q;

    if (is_push_pop_instr_i) begin
      unique case (instr_i[12:10])
        // push or pop
        3'b110: begin
          unique case (instr_i[9:8]) 
            2'b00: begin
              zcmp_instr_type = PUSH;  
            end
            2'b10: begin
              zcmp_instr_type = POP;  
            end
            default: begin
              illegal_instr_o = 1'b1;  
            end
          endcase 
        end
        // popret or popretz
        3'b111: begin
          unique case (instr_i[9:8]) 
            2'b00: begin
              zcmp_instr_type = POPRETZ;  
            end
            2'b10: begin
              zcmp_instr_type = POPRET;  
            end
            default: begin
              illegal_instr_o = 1'b1;  
            end
          endcase
        end
        // mvq01s or mvsa01
        3'b011: begin
          unique case (instr_i[6:5]) 
            2'b01: begin
              zcmp_instr_type = MVSA01;  
            end
            2'b11: begin
              zcmp_instr_type = MVA01S;  
            end
            default: begin
              illegal_instr_o = 1'b1;  
            end
          endcase
        end
        default: begin
          illegal_instr_o = 1'b1;
        end
      endcase

      if (zcmp_instr_type == MVSA01 || zcmp_instr_type == MVA01S) begin
        if(instr_i[9:7] != instr_i[4:2]) begin
          xreg1 = {instr_i[9:8] > 0, instr_i[9:8] == 0, instr_i[9:7]};
          xreg2 = {instr_i[4:3] > 0, instr_i[4:3] == 0, instr_i[4:2]};
        end else begin
          illegal_instr_o = 1'b1;
        end        
      end else begin
        xreg1 = '0;
        xreg2 = '0;
      end
      
      // push/pop/popret/popretz instructions
      unique case (instr_i[7:4])
        4'b0100: reg_numbers = 4'b0001; // 4
        4'b0101: reg_numbers = 4'b0010; // 5
        4'b0110: reg_numbers = 4'b0011; // 6
        4'b0111: reg_numbers = 4'b0100; // 7
        4'b1000: reg_numbers = 4'b0101; // 8
        4'b1001: reg_numbers = 4'b0110; // 9
        4'b1010: reg_numbers = 4'b0111; // 10
        4'b1011: reg_numbers = 4'b1000; // 11
        4'b1100: reg_numbers = 4'b1001; // 12
        4'b1101: reg_numbers = 4'b1010; // 13
        4'b1110: reg_numbers = 4'b1011; // 14
        4'b1111: reg_numbers = 4'b1100; // 15
        default: illegal_instr_o = 1'b1;
      endcase

      if (riscv::XLEN==32) begin
        unique case (instr_i[7:4])
          4'b0100, 4'b0101, 4'b0110, 4'b0111: begin
            unique case (instr_i[3:2])
              2'b00: stack_adj = 16;
              2'b01: stack_adj = 32;
              2'b10: stack_adj = 48;
              2'b11: stack_adj = 64;
            endcase
          end
          4'b1000, 4'b1001, 4'b1010, 4'b1011: begin
            unique case (instr_i[3:2])
              2'b00: stack_adj = 32;
              2'b01: stack_adj = 48;
              2'b10: stack_adj = 64;
              2'b11: stack_adj = 80;
            endcase
          end
          4'b1100, 4'b1101, 4'b1110: begin
            unique case (instr_i[3:2])
              2'b00: stack_adj = 48;
              2'b01: stack_adj = 64;
              2'b10: stack_adj = 80;
              2'b11: stack_adj = 96;
            endcase
          end
          4'b1111: begin
            unique case (instr_i[3:2])
              2'b00: stack_adj = 64;
              2'b01: stack_adj = 80;
              2'b10: stack_adj = 96;
              2'b11: stack_adj = 112;
            endcase
          end
          default: illegal_instr_o = 1'b1;
        endcase
      end else begin
        unique case (instr_i[7:4])
          4'b0100, 4'b0101: begin
            unique case (instr_i[3:2])
              2'b00: stack_adj = 16;
              2'b01: stack_adj = 32;
              2'b10: stack_adj = 48;
              2'b11: stack_adj = 64;
            endcase
          end
          4'b0110, 4'b0111: begin
            unique case (instr_i[3:2])
              2'b00: stack_adj = 32;
              2'b01: stack_adj = 48;
              2'b10: stack_adj = 64;
              2'b11: stack_adj = 80;
            endcase
          end
          4'b1000, 4'b1001: begin
            unique case (instr_i[3:2])
              2'b00: stack_adj = 48;
              2'b01: stack_adj = 64;
              2'b10: stack_adj = 80;
              2'b11: stack_adj = 96;
            endcase
          end
          4'b1010, 4'b1011: begin
            unique case (instr_i[3:2])
              2'b00: stack_adj = 64;
              2'b01: stack_adj = 80;
              2'b10: stack_adj = 96;
              2'b11: stack_adj = 112;
            endcase
          end
          4'b1100, 4'b1101: begin
            unique case (instr_i[3:2])
              2'b00: stack_adj = 80;
              2'b01: stack_adj = 96;
              2'b10: stack_adj = 112;
              2'b11: stack_adj = 128;
            endcase
          end
          4'b1110: begin
            unique case (instr_i[3:2])
              2'b00: stack_adj = 96;
              2'b01: stack_adj = 112;
              2'b10: stack_adj = 128;
              2'b11: stack_adj = 144;
            endcase
          end
          4'b1111: begin
            unique case (instr_i[3:2])
              2'b00: stack_adj = 112;
              2'b01: stack_adj = 128;
              2'b10: stack_adj = 144;
              2'b11: stack_adj = 160;
            endcase
          end
        endcase
      end

      //Take 2's compliment in case of PUSH instruction
      if(zcmp_instr_type == PUSH) begin
        itype_inst.imm = ~stack_adj + 1'b1;
      end else begin
        itype_inst.imm = stack_adj - 3'b100;
      end
    end else begin
      illegal_instr_o = illegal_instr_i;
    end    

    unique case(state_q)
      IDLE: begin
        if (is_push_pop_instr_i) begin
          reg_numbers_d = reg_numbers;
          state_d = INIT;   
          case (zcmp_instr_type)
            PUSH: begin
              offset_d = 12'hFFC;
            end
            POP,POPRETZ,POPRET: begin
              offset_d = itype_inst.imm;
              case (zcmp_instr_type)
                POPRETZ: begin
                  popretz_inst_d = 2'b11;
                end
                POPRET: begin
                  popretz_inst_d = 2'b01;
                end
                default: begin
                  popretz_inst_d = 'b0;
                end
              endcase             
            end
            default: begin
              illegal_instr_o = 1'b1; 
            end
          endcase
          // when rlist is 4, max reg is x18 i.e. 14(const) + 4
          // when rlist is 12, max reg is x27 i.e. 15(const) + 12 
          if(reg_numbers == 4'b1100) begin
            store_reg_d = 4'b1111 + reg_numbers;
          end else begin
            store_reg_d = 4'b1110 + reg_numbers;
          end  
        end
      end
      INIT: begin
        if(is_push_pop_instr_i && zcmp_instr_type == PUSH) begin
         // state_d =   PUSH_POP_INSTR_1;
          fetch_stall = 1'b1;  // stall inst fetch

          if (reg_numbers_q == 4'b0001) begin
            if (riscv::XLEN == 64) begin
              instr_o = {offset_d[11:5],5'h1,5'h2,3'h3,offset_d[4:0],riscv::OpcodeStore};
            end else begin
              instr_o = {offset_d[11:5],5'h1,5'h2,3'h2,offset_d[4:0],riscv::OpcodeStore};
            end
            state_d =   PUSH_ADDI;
          end

          if (reg_numbers_q == 4'b0010) begin
            if (riscv::XLEN == 64) begin
              instr_o = {offset_d[11:5],5'h8,5'h2,3'h3,offset_d[4:0],riscv::OpcodeStore};
            end else begin
              instr_o = {offset_d[11:5],5'h8,5'h2,3'h2,offset_d[4:0],riscv::OpcodeStore};
            end
            reg_numbers_d = reg_numbers_q -1;
            offset_d = offset_q + 12'hFFC;  // decrement offset by -4 i.e. add 2's compilment of 4
          end
          
          if (reg_numbers_q == 4'b0011) begin
            if (riscv::XLEN == 64) begin
              instr_o = {offset_d[11:5],5'h9,5'h2,3'h3,offset_d[4:0],riscv::OpcodeStore};
            end else begin
              instr_o = {offset_d[11:5],5'h9,5'h2,3'h2,offset_d[4:0],riscv::OpcodeStore};
            end
            reg_numbers_d = reg_numbers_q -1;
            offset_d = offset_q + 12'hFFC;  
          end

          if (reg_numbers_q >= 4 && reg_numbers_q <= 12) begin
            if (riscv::XLEN == 64) begin
              instr_o = {offset_d[11:5],store_reg_q,5'h2,3'h3,offset_d[4:0],riscv::OpcodeStore};
            end else begin
              instr_o = {offset_d[11:5], store_reg_q, 5'h2, 3'h2, offset_d[4:0], riscv::OpcodeStore};
            end
              reg_numbers_d = reg_numbers_q - 1;
              store_reg_d = store_reg_q - 1;
              offset_d = offset_q + 12'hFFC;
              if (reg_numbers_q == 12) begin
                state_d = PUSH_POP_INSTR_2;
              end
          end
        end

        if (is_push_pop_instr_i && (zcmp_instr_type == POP || zcmp_instr_type == POPRETZ || zcmp_instr_type == POPRET)) begin
         // state_d = PUSH_POP_INSTR_1;
          fetch_stall = 1;  // stall inst fetch
          if (reg_numbers_q == 1) begin
            if (riscv::XLEN == 64) begin
              instr_o = {offset_d[11:5],5'h1,5'h2,3'h3,offset_d[4:0],riscv::OpcodeLoad};
            end else begin
              instr_o = {offset_d[11:0],5'h2,3'h2, 5'h1,riscv::OpcodeLoad};
            end
            unique case (zcmp_instr_type)
              PUSH,POP,POPRET: begin
                state_d =   PUSH_ADDI;  
              end
              POPRETZ: begin
                state_d = POPRETZ_1;  
              end
              default: begin
                state_d = state_q;
              end
            endcase
          end

          if (reg_numbers_q == 2) begin
            if (riscv::XLEN == 64) begin
              instr_o = {offset_d[11:5],5'h8,5'h2,3'h3,offset_d[4:0],riscv::OpcodeLoad};
            end else begin
              instr_o = {offset_d[11:0],5'h2,3'h2, 5'h8,riscv::OpcodeLoad};
            end
            reg_numbers_d = reg_numbers_q -1;
            offset_d = offset_q + 12'hFFC;  // decrement offset by -4 i.e. add 2's compilment of 4
          end
          
          if (reg_numbers_q == 3) begin
            if (riscv::XLEN == 64) begin
              instr_o = {offset_d[11:5],5'h9,5'h2,3'h3,offset_d[4:0],riscv::OpcodeLoad};
            end else begin
              instr_o = {offset_d[11:0],5'h2,3'h2, 5'h9,riscv::OpcodeLoad};
            end
            reg_numbers_d = reg_numbers_q -1;
            offset_d = offset_q + 12'hFFC;  
          end

          if (reg_numbers_q >= 4 && reg_numbers_q <= 12) begin
            if (riscv::XLEN == 64) begin
              instr_o = {offset_d[11:5],store_reg_q,5'h2,3'h3,offset_d[4:0],riscv::OpcodeLoad};
            end else begin
              instr_o = {offset_d[11:0],5'h2,3'h2,store_reg_q,riscv::OpcodeLoad};
            end
              reg_numbers_d = reg_numbers_q - 1;
              store_reg_d = store_reg_q - 1;
              offset_d = offset_q + 12'hFFC;
              if (reg_numbers_q == 12) begin
                state_d = PUSH_POP_INSTR_2;
              end
          end
        end

        if (is_push_pop_instr_i && zcmp_instr_type == MVSA01) begin
          fetch_stall = 1;
          instr_o = {12'h0,5'hA, 3'h0,xreg1,riscv::OpcodeOpImm};
          state_d = MOVE;
        end

        if (is_push_pop_instr_i && zcmp_instr_type == MVA01S) begin
          fetch_stall = 1;
          instr_o = {12'h0,xreg1, 3'h0,5'hA,riscv::OpcodeOpImm};
          state_d = MOVE;
        end
      end

      MOVE: begin
        case (zcmp_instr_type)
          MVSA01:  begin
            instr_o = {12'h0,5'hB, 3'h0,xreg2,riscv::OpcodeOpImm};
          end
          MVA01S: begin
            instr_o = {12'h0,xreg2, 3'h0,5'hB,riscv::OpcodeOpImm};
          end
          default: begin
            illegal_instr_o = 1'b1;
          end
        endcase
        fetch_stall = 0;
        state_d = IDLE;
      end

      PUSH_ADDI:begin
        if (zcmp_instr_type == PUSH) begin
          instr_o = {itype_inst.imm,5'h2, 3'h0,5'h2,riscv::OpcodeOpImm};
        end else begin
          instr_o = {stack_adj,5'h2, 3'h0,5'h2,riscv::OpcodeOpImm};
        end
        if (zcmp_instr_type == POPRETZ || zcmp_instr_type == POPRET) begin
          state_d = POPRETZ_1;
        end else begin
          state_d = IDLE;
          fetch_stall = 0;
        end
      end

      PUSH_POP_INSTR_2:begin
        if (riscv::XLEN == 64) begin
            case(zcmp_instr_type)
              PUSH: begin
                instr_o = {offset_d[11:5], store_reg_q, 5'h2, 3'h3, offset_d[4:0], riscv::OpcodeStore};
              end
              POP,POPRETZ,POPRET: begin
                instr_o = {offset_d[11:0],5'h2,3'h3, store_reg_q,riscv::OpcodeLoad};
              end
            endcase
        end else begin
              case(zcmp_instr_type)
                PUSH: begin
                  instr_o = {offset_d[11:5], store_reg_q, 5'h2, 3'h2, offset_d[4:0], riscv::OpcodeStore};
                end
                POP,POPRETZ,POPRET: begin
                  instr_o = {offset_d[11:0],5'h2,3'h2,store_reg_q,riscv::OpcodeLoad};
                end
                default: begin
                  illegal_instr_o = 1'b1;
                end
              endcase
        end
        offset_d = offset_q + 12'hFFC;
        store_reg_d = store_reg_q - 1;
        state_d = INIT;
      end

      POPRETZ_1: begin
        unique case (popretz_inst_q)
          2'b11: begin
            instr_o = {20'h0,5'hA,riscv::OpcodeLui};  //lui a0, 0x0
            popretz_inst_d = popretz_inst_d - 1;
          end
          2'b10: begin
            instr_o = {12'h0,5'hA, 3'h0,5'hA,riscv::OpcodeOpImm};  //addi a0, a0, 0x0
            popretz_inst_d = popretz_inst_d - 1;  
            state_d = PUSH_ADDI;
          end
          2'b01: begin
            instr_o = {12'h0,5'h1,3'h0,5'h0,riscv::OpcodeJalr};  //ret - jalr x0, x1, 0
            state_d = IDLE;
            fetch_stall = 0;
            popretz_inst_d = popretz_inst_d - 1;  
          end
          default: begin
            illegal_instr_o = 1'b1; 
          end
        endcase
      end
      
      default: begin
        state_d = IDLE;
      end
    endcase
  end  

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) begin
      state_q <= IDLE;
      offset_q <= '0;
      popretz_inst_q <= '0;
      reg_numbers_q <= '0;
      store_reg_q <= '0;
    end else begin
      state_q <= state_d;
      offset_q <= offset_d;
      reg_numbers_q <= reg_numbers_d;
      store_reg_q <= store_reg_d;
      popretz_inst_q <= popretz_inst_d;
    end
  end
endmodule