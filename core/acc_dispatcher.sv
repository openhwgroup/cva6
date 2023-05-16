// Copyright 2020 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Matheus Cavalcante, ETH Zurich
// Date: 20.11.2020
// Description: Functional unit that dispatches CVA6 instructions to accelerators.

module acc_dispatcher import ariane_pkg::*; import riscv::*; (
    input  logic                                  clk_i,
    input  logic                                  rst_ni,
    input  logic                                  flush_i,
    // Interface with the CSR regfile
    input  logic                                  acc_cons_en_i,        // Accelerator memory consistent mode
    // Interface with the CSRs
    input logic                             [2:0] fcsr_frm_i,
    // Interface with the issue stage
    input  fu_data_t                              acc_data_i,
    output logic                                  acc_ready_o,          // FU is ready
    input  logic                                  acc_valid_i,          // Output is valid
    output logic                                  acc_ld_disp_o,
    output logic                                  acc_st_disp_o,
    output logic                                  acc_flush_undisp_o,
    output logic              [TRANS_ID_BITS-1:0] acc_trans_id_o,
    output xlen_t                                 acc_result_o,
    output logic                                  acc_valid_o,
    output exception_t                            acc_exception_o,
    // Interface with the commit stage
    // This avoids sending speculative instructions to the accelerator.
    input  logic                                  acc_commit_i,
    input  logic              [TRANS_ID_BITS-1:0] acc_commit_trans_id_i,
    // Interface with the load/store unit
    input  logic                                  acc_no_st_pending_i,
    // Accelerator interface
    output accelerator_req_t                      acc_req_o,
    output logic                                  acc_req_valid_o,
    input  logic                                  acc_req_ready_i,
    input  accelerator_resp_t                     acc_resp_i,
    input  logic                                  acc_resp_valid_i,
    output logic                                  acc_resp_ready_o
  );

  `include "common_cells/registers.svh"

  import cf_math_pkg::idx_width;

  /***********************
   *  Instruction queue  *
   ***********************/

  localparam InstructionQueueDepth = 3;

  fu_data_t                                        acc_insn_queue_o;
  logic                                            acc_insn_queue_pop;
  logic                                            acc_insn_queue_empty;
  logic     [idx_width(InstructionQueueDepth)-1:0] acc_insn_queue_usage;

  fifo_v3 #(
    .DEPTH       (InstructionQueueDepth),
    .FALL_THROUGH(1'b1                 ),
    .dtype       (fu_data_t            )
  ) i_acc_insn_queue (
    .clk_i     (clk_i               ),
    .rst_ni    (rst_ni              ),
    .flush_i   (flush_i             ),
    .testmode_i(1'b0                ),
    .data_i    (acc_data_i          ),
    .push_i    (acc_valid_i         ),
    .full_o    (/* Unused */        ),
    .data_o    (acc_insn_queue_o    ),
    .pop_i     (acc_insn_queue_pop  ),
    .empty_o   (acc_insn_queue_empty),
    .usage_o   (acc_insn_queue_usage)
  );

  // We are ready if the instruction queue is able to accept at least one more entry.
  assign acc_ready_o = acc_insn_queue_usage < (InstructionQueueDepth-1);

  // Flush undispatched accelerator instructions.
  assign acc_flush_undisp_o = flush_i;

  /**********************************
   *  Non-speculative instructions  *
   **********************************/

  // Keep track of the instructions that were received by the dispatcher.
  logic [NR_SB_ENTRIES-1:0] insn_pending_d, insn_pending_q;
  `FF(insn_pending_q, insn_pending_d, '0)

  // Only non-speculative instructions can be issued to the accelerators.
  // The following block keeps track of which transaction IDs reached the
  // top of the scoreboard, and are therefore no longer speculative.
  logic [NR_SB_ENTRIES-1:0] insn_ready_d, insn_ready_q;
  `FF(insn_ready_q, insn_ready_d, '0)

  always_comb begin: p_non_speculative_ff
    // Maintain state
    insn_pending_d = insn_pending_q;
    insn_ready_d   = insn_ready_q;

    // We received a new instruction
    if (acc_valid_i)
      insn_pending_d[acc_data_i.trans_id] = 1'b1;
    // Flush all received instructions
    if (flush_i)
      insn_pending_d = '0;

    // An accelerator instruction is no longer speculative.
    if (acc_commit_i && insn_pending_q[acc_commit_trans_id_i]) begin
      insn_ready_d[acc_commit_trans_id_i]   = 1'b1;
      insn_pending_d[acc_commit_trans_id_i] = 1'b0;
    end

    // An accelerator instruction was issued.
    if (acc_req_valid_o)
      insn_ready_d[acc_req_o.trans_id] = 1'b0;
  end: p_non_speculative_ff

  /*************************
   *  Accelerator request  *
   *************************/

  accelerator_req_t acc_req;
  logic             acc_req_valid;
  logic             acc_req_ready;

  accelerator_req_t acc_req_int;
  fall_through_register #(
    .T(accelerator_req_t)
  ) i_accelerator_req_register (
    .clk_i     (clk_i          ),
    .rst_ni    (rst_ni         ),
    .clr_i     (1'b0           ),
    .testmode_i(1'b0           ),
    .data_i    (acc_req        ),
    .valid_i   (acc_req_valid  ),
    .ready_o   (acc_req_ready  ),
    .data_o    (acc_req_int    ),
    .valid_o   (acc_req_valid_o),
    .ready_i   (acc_req_ready_i)
  );

  assign acc_req_o = '{
      insn         : acc_req_int.insn,
      rs1          : acc_req_int.rs1,
      rs2          : acc_req_int.rs2,
      frm          : acc_req_int.frm,
      trans_id     : acc_req_int.trans_id,
      store_pending: !acc_no_st_pending_i && acc_cons_en_i
    };

  always_comb begin: accelerator_req_dispatcher
    // Do not fetch from the instruction queue
    acc_insn_queue_pop = 1'b0;

    // Default values
    acc_req       = '0;
    acc_req_valid = 1'b0;

    // Unpack fu_data_t into accelerator_req_t
    if (!acc_insn_queue_empty) begin
      acc_req = '{
        // Instruction is forwarded from the decoder as an immediate
        // -
        // frm rounding information is up to date during a valid request to the accelerator
        // The scoreboard synchronizes it with previous fcsr writes, and future fcsr writes
        // do not take place until the accelerator answers (Ariane commits in-order)
        insn    : acc_insn_queue_o.imm[31:0],
        rs1     : acc_insn_queue_o.operand_a,
        rs2     : acc_insn_queue_o.operand_b,
        frm     : fpnew_pkg::roundmode_e'(fcsr_frm_i),
        trans_id: acc_insn_queue_o.trans_id,
        default : '0
      };
      // Wait until the instruction is no longer speculative.
      acc_req_valid      = insn_ready_q[acc_insn_queue_o.trans_id] ||
                           (acc_commit_i && insn_pending_q[acc_commit_trans_id_i]);
      acc_insn_queue_pop = acc_req_valid && acc_req_ready;
    end
  end

  /**************************
   *  Accelerator response  *
   **************************/

  // Unpack the accelerator response
  assign acc_trans_id_o  = acc_resp_i.trans_id;
  assign acc_result_o    = acc_resp_i.result;
  assign acc_valid_o     = acc_resp_valid_i;
  assign acc_exception_o = '{
      cause: riscv::ILLEGAL_INSTR,
      tval : '0,
      valid: acc_resp_i.error
    };
  // Always ready to receive responses
  assign acc_resp_ready_o = 1'b1;

  // Signal dispatched load/store to issue stage
  assign acc_ld_disp_o = acc_req_valid && (acc_insn_queue_o.operator == ACCEL_OP_LOAD);
  assign acc_st_disp_o = acc_req_valid && (acc_insn_queue_o.operator == ACCEL_OP_STORE);
endmodule : acc_dispatcher
