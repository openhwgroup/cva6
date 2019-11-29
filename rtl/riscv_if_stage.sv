// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Engineer:       Renzo Andri - andrire@student.ethz.ch                      //
//                                                                            //
// Additional contributions by:                                               //
//                 Igor Loi - igor.loi@unibo.it                               //
//                 Andreas Traber - atraber@student.ethz.ch                   //
//                 Sven Stucki - svstucki@student.ethz.ch                     //
//                                                                            //
// Design Name:    Instruction Fetch Stage                                    //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Instruction fetch unit: Selection of the next PC, and      //
//                 buffering (sampling) of the read instruction               //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////


import riscv_defines::*;

module riscv_if_stage
#(
  parameter N_HWLP          = 2,
  parameter RDATA_WIDTH     = 32,
  parameter FPU             = 0,
  parameter DM_HaltAddress  = 32'h1A110800
)
(
    input  logic        clk,
    input  logic        rst_n,

    // Used to calculate the exception offsets
    input  logic [23:0] m_trap_base_addr_i,
    input  logic [23:0] u_trap_base_addr_i,
    input  logic        trap_addr_mux_i,
    // Used for boot address
    input  logic [30:0] boot_addr_i,

    // instruction request control
    input  logic        req_i,

    // instruction cache interface
    output logic                   instr_req_o,
    output logic            [31:0] instr_addr_o,
    input  logic                   instr_gnt_i,
    input  logic                   instr_rvalid_i,
    input  logic [RDATA_WIDTH-1:0] instr_rdata_i,
    input  logic                   instr_err_pmp_i,

    // Output of IF Pipeline stage
    output logic [N_HWLP-1:0] hwlp_dec_cnt_id_o,     // currently served instruction was the target of a hwlp
    output logic              is_hwlp_id_o,          // currently served instruction was the target of a hwlp
    output logic              instr_valid_id_o,      // instruction in IF/ID pipeline is valid
    output logic       [31:0] instr_rdata_id_o,      // read instruction is sampled and sent to ID stage for decoding
    output logic              is_compressed_id_o,    // compressed decoder thinks this is a compressed instruction
    output logic              illegal_c_insn_id_o,   // compressed decoder thinks this is an invalid instruction
    output logic       [31:0] pc_if_o,
    output logic       [31:0] pc_id_o,
    output logic              is_fetch_failed_o,

    // Forwarding ports - control signals
    input  logic        clear_instr_valid_i,   // clear instruction valid bit in IF/ID pipe
    input  logic        pc_set_i,              // set the program counter to a new value
    input  logic [31:0] mepc_i,    // address used to restore PC when the interrupt/exception is served
    input  logic [31:0] uepc_i,    // address used to restore PC when the interrupt/exception is served

    input  logic [31:0] depc_i,    // address used to restore PC when the debug is served

    input  logic  [2:0] pc_mux_i,              // sel for pc multiplexer
    input  logic  [2:0] exc_pc_mux_i,          // selects ISR address
    input  logic  [4:0] exc_vec_pc_mux_i,      // selects ISR address for vectorized interrupt lines

    // jump and branch target and decision
    input  logic [31:0] jump_target_id_i,      // jump target address
    input  logic [31:0] jump_target_ex_i,      // jump target address

    // from hwloop controller
    input  logic [N_HWLP-1:0] [31:0] hwlp_start_i,          // hardware loop start addresses
    input  logic [N_HWLP-1:0] [31:0] hwlp_end_i,            // hardware loop end addresses
    input  logic [N_HWLP-1:0] [31:0] hwlp_cnt_i,            // hardware loop counters

    // pipeline stall
    input  logic        halt_if_i,
    input  logic        id_ready_i,

    // misc signals
    output logic        if_busy_o,             // is the IF stage busy fetching instructions?
    output logic        perf_imiss_o           // Instruction Fetch Miss
);

  // offset FSM
  enum logic[0:0] {WAIT, IDLE } offset_fsm_cs, offset_fsm_ns;

  logic              if_valid, if_ready;
  logic              valid;

  // prefetch buffer related signals
  logic              prefetch_busy;
  logic              branch_req;
  logic       [31:0] fetch_addr_n;

  logic              fetch_valid;
  logic              fetch_ready;
  logic       [31:0] fetch_rdata;
  logic       [31:0] fetch_addr;
  logic              is_hwlp_id_q, fetch_is_hwlp;

  logic       [31:0] exc_pc;

  // hardware loop related signals
  logic              hwlp_jump, hwlp_branch;
  logic       [31:0] hwlp_target;
  logic [N_HWLP-1:0] hwlp_dec_cnt, hwlp_dec_cnt_if;

  logic [23:0]       trap_base_addr;
  logic              fetch_failed;


  // exception PC selection mux
  always_comb
  begin : EXC_PC_MUX
    exc_pc = '0;

    unique case (trap_addr_mux_i)
      TRAP_MACHINE: trap_base_addr = m_trap_base_addr_i;
      TRAP_USER:    trap_base_addr = u_trap_base_addr_i;
      default:;
    endcase

    unique case (exc_pc_mux_i)
      EXC_PC_EXCEPTION:                        exc_pc = { trap_base_addr, 8'h0 }; //1.10 all the exceptions go to base address
      EXC_PC_IRQ:                              exc_pc = { trap_base_addr, 1'b0, exc_vec_pc_mux_i[4:0], 2'b0 };
      EXC_PC_DBD:                              exc_pc = { DM_HaltAddress       };
      default:;
    endcase
  end

  // fetch address selection
  always_comb
  begin
    fetch_addr_n = '0;

    unique case (pc_mux_i)
      PC_BOOT:      fetch_addr_n = {boot_addr_i, 1'b0};
      PC_JUMP:      fetch_addr_n = jump_target_id_i;
      PC_BRANCH:    fetch_addr_n = jump_target_ex_i;
      PC_EXCEPTION: fetch_addr_n = exc_pc;             // set PC to exception handler
      PC_MRET:      fetch_addr_n = mepc_i; // PC is restored when returning from IRQ/exception
      PC_URET:      fetch_addr_n = uepc_i; // PC is restored when returning from IRQ/exception
      PC_DRET:      fetch_addr_n = depc_i; //
      PC_FENCEI:    fetch_addr_n = pc_id_o + 4; // jump to next instr forces prefetch buffer reload
      default:;
    endcase
  end

  generate
    if (RDATA_WIDTH == 32) begin : prefetch_32
      // prefetch buffer, caches a fixed number of instructions
      riscv_prefetch_buffer prefetch_buffer_i
      (
        .clk               ( clk                         ),
        .rst_n             ( rst_n                       ),

        .req_i             ( req_i                       ),

        .branch_i          ( branch_req                  ),
        .addr_i            ( {fetch_addr_n[31:1], 1'b0}  ),

        .hwloop_i          ( hwlp_jump                   ),
        .hwloop_target_i   ( hwlp_target                 ),
        .hwlp_branch_o     ( hwlp_branch                 ),

        .ready_i           ( fetch_ready                 ),
        .valid_o           ( fetch_valid                 ),
        .rdata_o           ( fetch_rdata                 ),
        .addr_o            ( fetch_addr                  ),
        .is_hwlp_o         ( fetch_is_hwlp               ),

        // goes to instruction memory / instruction cache
        .instr_req_o       ( instr_req_o                 ),
        .instr_addr_o      ( instr_addr_o                ),
        .instr_gnt_i       ( instr_gnt_i                 ),
        .instr_rvalid_i    ( instr_rvalid_i              ),
        .instr_err_pmp_i   ( instr_err_pmp_i             ),
        .fetch_failed_o    ( fetch_failed                ),
        .instr_rdata_i     ( instr_rdata_i               ),

        // Prefetch Buffer Status
        .busy_o            ( prefetch_busy               )
      );
    end else if (RDATA_WIDTH == 128) begin : prefetch_128
      // prefetch buffer, caches a fixed number of instructions
      riscv_prefetch_L0_buffer prefetch_buffer_i
      (
        .clk               ( clk                         ),
        .rst_n             ( rst_n                       ),

        .req_i             ( 1'b1                        ),

        .branch_i          ( branch_req                  ),
        .addr_i            ( {fetch_addr_n[31:1], 1'b0}  ),

        .hwloop_i          ( hwlp_jump                   ),
        .hwloop_target_i   ( hwlp_target                 ),

        .ready_i           ( fetch_ready                 ),
        .valid_o           ( fetch_valid                 ),
        .rdata_o           ( fetch_rdata                 ),
        .addr_o            ( fetch_addr                  ),
        .is_hwlp_o         ( fetch_is_hwlp               ),

        // goes to instruction memory / instruction cache
        .instr_req_o       ( instr_req_o                 ),
        .instr_addr_o      ( instr_addr_o                ),
        .instr_gnt_i       ( instr_gnt_i                 ),
        .instr_rvalid_i    ( instr_rvalid_i              ),
        .instr_rdata_i     ( instr_rdata_i               ),

        // Prefetch Buffer Status
        .busy_o            ( prefetch_busy               )
       );

       assign hwlp_branch  = 1'b0;
       assign fetch_failed = 1'b0;

    end
  endgenerate

  // offset FSM state
  always_ff @(posedge clk, negedge rst_n)
  begin
    if (rst_n == 1'b0) begin
      offset_fsm_cs     <= IDLE;
    end else begin
      offset_fsm_cs     <= offset_fsm_ns;
    end
  end

  // offset FSM state transition logic
  always_comb
  begin
    offset_fsm_ns = offset_fsm_cs;

    fetch_ready   = 1'b0;
    branch_req    = 1'b0;
    valid         = 1'b0;

    unique case (offset_fsm_cs)
      // no valid instruction data for ID stage
      // assume aligned
      IDLE: begin
        if (req_i) begin
          branch_req    = 1'b1;
          offset_fsm_ns = WAIT;
        end
      end

      // serving aligned 32 bit or 16 bit instruction, we don't know yet
      WAIT: begin
        if (fetch_valid) begin
          valid   = 1'b1; // an instruction is ready for ID stage

          if (req_i && if_valid) begin
            fetch_ready   = 1'b1;
            offset_fsm_ns = WAIT;
          end
        end
      end

      default: begin
        offset_fsm_ns = IDLE;
      end
    endcase


    // take care of jumps and branches
    if (pc_set_i) begin
      valid = 1'b0;

      // switch to new PC from ID stage
      branch_req    = 1'b1;
      offset_fsm_ns = WAIT;
    end
    else begin
      if(hwlp_branch)
        valid = 1'b0;
    end
  end

  // Hardware Loops
  riscv_hwloop_controller
  #(
    .N_REGS ( N_HWLP )
  )
  hwloop_controller_i
  (
    .current_pc_i          ( fetch_addr        ),

    .hwlp_jump_o           ( hwlp_jump         ),
    .hwlp_targ_addr_o      ( hwlp_target       ),

    // from hwloop_regs
    .hwlp_start_addr_i     ( hwlp_start_i      ),
    .hwlp_end_addr_i       ( hwlp_end_i        ),
    .hwlp_counter_i        ( hwlp_cnt_i        ),

    // to hwloop_regs
    .hwlp_dec_cnt_o        ( hwlp_dec_cnt      ),
    .hwlp_dec_cnt_id_i     ( hwlp_dec_cnt_id_o & {N_HWLP{is_hwlp_id_o}} )
  );


  assign pc_if_o         = fetch_addr;

  assign if_busy_o       = prefetch_busy;

  assign perf_imiss_o    = (~fetch_valid) | branch_req;


  // compressed instruction decoding, or more precisely compressed instruction
  // expander
  //
  // since it does not matter where we decompress instructions, we do it here
  // to ease timing closure
  logic [31:0] instr_decompressed;
  logic        illegal_c_insn;
  logic        instr_compressed_int;

  riscv_compressed_decoder
    #(
      .FPU(FPU)
     )
  compressed_decoder_i
  (
    .instr_i         ( fetch_rdata          ),
    .instr_o         ( instr_decompressed   ),
    .is_compressed_o ( instr_compressed_int ),
    .illegal_instr_o ( illegal_c_insn       )
  );

  // prefetch -> IF registers
  always_ff @(posedge clk, negedge rst_n)
  begin
    if (rst_n == 1'b0)
    begin
      hwlp_dec_cnt_if <= '0;
    end
    else
    begin
      if (hwlp_jump)
        hwlp_dec_cnt_if <= hwlp_dec_cnt;
    end
  end

  // IF-ID pipeline registers, frozen when the ID stage is stalled
  always_ff @(posedge clk, negedge rst_n)
  begin : IF_ID_PIPE_REGISTERS
    if (rst_n == 1'b0)
    begin
      instr_valid_id_o      <= 1'b0;
      instr_rdata_id_o      <= '0;
      illegal_c_insn_id_o   <= 1'b0;
      is_compressed_id_o    <= 1'b0;
      pc_id_o               <= '0;
      is_hwlp_id_q          <= 1'b0;
      hwlp_dec_cnt_id_o     <= '0;
      is_fetch_failed_o     <= 1'b0;

    end
    else
    begin

      if (if_valid)
      begin
        instr_valid_id_o    <= 1'b1;
        instr_rdata_id_o    <= instr_decompressed;
        illegal_c_insn_id_o <= illegal_c_insn;
        is_compressed_id_o  <= instr_compressed_int;
        pc_id_o             <= pc_if_o;
        is_hwlp_id_q        <= fetch_is_hwlp;
        is_fetch_failed_o   <= 1'b0;

        if (fetch_is_hwlp)
          hwlp_dec_cnt_id_o   <= hwlp_dec_cnt_if;

      end else if (clear_instr_valid_i) begin
        instr_valid_id_o    <= 1'b0;
        is_fetch_failed_o   <= fetch_failed;
      end

    end
  end

  assign is_hwlp_id_o = is_hwlp_id_q & instr_valid_id_o;

  assign if_ready = valid & id_ready_i;
  assign if_valid = (~halt_if_i) & if_ready;

  //----------------------------------------------------------------------------
  // Assertions
  //----------------------------------------------------------------------------
  `ifndef VERILATOR
    // there should never be a grant when there is no request
    assert property (
      @(posedge clk) (instr_gnt_i) |-> (instr_req_o) )
      else $warning("There was a grant without a request");
  `endif
endmodule
