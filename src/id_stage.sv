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
// Author: Florian Zaruba, ETH Zurich
// Date: 15.04.2017
// Description: Instruction decode, contains the logic for decode,
//              issue and read operands.

module id_stage (
    input  logic                          clk_i,
    input  logic                          rst_ni,

    input  logic                          flush_i,
    input  logic                          debug_req_i,
    // from CSR file
    input  riscv::priv_lvl_t              priv_lvl_i,          // current privilege level
    input  riscv::xs_t                    fs_i,                // floating point extension status
    input  logic [2:0]                    frm_i,               // floating-point dynamic rounding mode
    input  logic [1:0]                    irq_i,
    input  ariane_pkg::irq_ctrl_t         irq_ctrl_i,
    input  logic                          debug_mode_i,        // we are in debug mode
    input  logic                          tvm_i,
    input  logic                          tw_i,
    input  logic                          tsr_i,
    // to ID
    output ariane_pkg::scoreboard_entry_t [ariane_pkg::ISSUE_WIDTH-1:0] issue_entry_o,       // a decoded instruction
    output logic [ariane_pkg::ISSUE_WIDTH-1:0]                          issue_entry_valid_o, // issue entry is valid
    output logic [ariane_pkg::ISSUE_WIDTH-1:0]                          is_ctrl_flow_o,      // the instruction we issue is a ctrl flow instructions
    input  logic [ariane_pkg::ISSUE_WIDTH-1:0]                          issue_instr_ack_i,   // issue stage acknowledged sampling of instructions
    // from IF
    input  ariane_pkg::fetch_entry_t [ariane_pkg::ISSUE_WIDTH-1:0]      fetch_entry_i,
    input  logic [ariane_pkg::ISSUE_WIDTH-1:0]                          fetch_entry_valid_i,
    output logic [ariane_pkg::ISSUE_WIDTH-1:0]                          fetch_entry_ready_o  // acknowledge the instruction (fetch entry)
);
    // ID/ISSUE register stage
    typedef struct packed {
        logic                          valid;
        ariane_pkg::scoreboard_entry_t sbe;
        logic                          is_ctrl_flow;
    } issue_reg_t;
    issue_reg_t [ariane_pkg::ISSUE_WIDTH-1:0] issue_n, issue_q, issue_candidates;
    issue_reg_t [ariane_pkg::ISSUE_WIDTH*2-1:0] issue_n_extended;

    logic [ariane_pkg::ISSUE_WIDTH-1:0]                            is_control_flow_instr;
    ariane_pkg::scoreboard_entry_t [ariane_pkg::ISSUE_WIDTH-1:0]   decoded_instruction;

    // generate new issue instructions
    logic [ariane_pkg::ISSUE_WIDTH-1:0]                cf_exist;
    logic [ariane_pkg::ISSUE_WIDTH-1:0]                decoded_instruction_valid;
    logic [ariane_pkg::ISSUE_WIDTH-1:0]                issue_reg_usage;

    logic [ariane_pkg::ISSUE_WIDTH_BITS-1:0]           issue_reg_lead_avail_cnt, issue_reg_trail_avail_cnt;
    logic [ariane_pkg::ISSUE_WIDTH_BITS:0]             issue_reg_avail_cnt, issue_reg_busy_cnt;
    logic                                              issue_reg_lead_all_avail, issue_reg_trail_all_avail;
    logic [ariane_pkg::ISSUE_WIDTH*2-1:0]              fetch_ready_mask_extended;
    logic [ariane_pkg::ISSUE_WIDTH-1:0]                fetch_ready_mask;


    logic [ariane_pkg::ISSUE_WIDTH-1:0]                is_illegal;
    logic [ariane_pkg::ISSUE_WIDTH-1:0][31:0]          instruction;
    logic [ariane_pkg::ISSUE_WIDTH-1:0]                is_compressed;

    for (genvar i = 0; i < ariane_pkg::ISSUE_WIDTH; i++) begin : gen_decoder
        // ---------------------------------------------------------
        // 1. Check if they are compressed and expand in case they are
        // ---------------------------------------------------------
        compressed_decoder compressed_decoder_i (
            .instr_i                 ( fetch_entry_i[i].instruction ),
            .instr_o                 ( instruction[i]               ),
            .illegal_instr_o         ( is_illegal[i]                ),
            .is_compressed_o         ( is_compressed[i]             )
        );
        // ---------------------------------------------------------
        // 2. Decode and emit instruction to issue stage
        // ---------------------------------------------------------
        decoder decoder_i (
            .debug_req_i,
            .irq_ctrl_i,
            .irq_i,
            .pc_i                    ( fetch_entry_i[i].address           ),
            .is_compressed_i         ( is_compressed[i]                   ),
            .is_illegal_i            ( is_illegal[i]                      ),
            .instruction_i           ( instruction[i]                     ),
            .compressed_instr_i      ( fetch_entry_i[i].instruction[15:0] ),
            .branch_predict_i        ( fetch_entry_i[i].branch_predict    ),
            .ex_i                    ( fetch_entry_i[i].ex                ),
            .priv_lvl_i              ( priv_lvl_i                         ),
            .debug_mode_i            ( debug_mode_i                       ),
            .fs_i,
            .frm_i,
            .tvm_i,
            .tw_i,
            .tsr_i,
            .instruction_o           ( decoded_instruction[i]             ),
            .is_control_flow_instr_o ( is_control_flow_instr[i]           )
        );

        // ------------------
        // Pipeline Register
        // ------------------
        assign issue_entry_o[i] = issue_q[i].sbe;
        assign issue_entry_valid_o[i] = issue_q[i].valid;
        assign is_ctrl_flow_o[i] = issue_q[i].is_ctrl_flow;

        // --------------------------------------------------------------
        // Check if the instruction is valid
        // The instruction is not valid if
        // 1. CSR instruction exists before it
        // 1. control flow exists before it
        // --------------------------------------------------------------
        if (i == 0) begin
            assign cf_exist[i] = 1'b0;
        end else begin
            assign cf_exist[i] = (|is_control_flow_instr[i-1:0]);
        end

        assign decoded_instruction_valid[i] = fetch_entry_valid_i[i] & ~cf_exist[i];

        // --------------------------------------------------------------
        // Availble issue registers. "1" means busy and "0" means available.
        // A register is busy if it is valid and issue stage is not currently
        // acknowledging it
        // --------------------------------------------------------------
        assign issue_reg_usage[i] = issue_q[i].valid & ~issue_instr_ack_i[i];

        assign issue_candidates[i] = '{decoded_instruction_valid[i], decoded_instruction[i], is_control_flow_instr[i]};
    end

    // count how many new instructions we can shift into the registers
    // For example, when we have i2 i1 i0 in issue q, fetched instructions i5 i4 i3
    // and current register usage is 0 1 0 (i1 is still busy and i2 is invalid),
    // in the next cycle the issue q should be i4 i3 i1.
    generate
        if (ariane_pkg::ISSUE_WIDTH != 1) begin
            lzc #(
              .WIDTH ( ariane_pkg::ISSUE_WIDTH )
            ) i_lzc_issue_reg_lead_usage (
              .in_i    ( issue_reg_usage          ),
              .cnt_o   ( issue_reg_trail_avail_cnt ),
              .empty_o ( issue_reg_trail_all_avail )
            );

            lzc #(
              .WIDTH ( ariane_pkg::ISSUE_WIDTH ),
              .MODE  ( 1'b1                    )
            ) i_lzc_issue_reg_trail_usage (
              .in_i    ( issue_reg_usage          ),
              .cnt_o   ( issue_reg_lead_avail_cnt ),
              .empty_o ( issue_reg_lead_all_avail )
            );

            assign issue_reg_avail_cnt = issue_reg_trail_avail_cnt + issue_reg_lead_avail_cnt;
            assign issue_reg_busy_cnt = ($bits(issue_reg_busy_cnt))'(ISSUE_WIDTH) - issue_reg_avail_cnt;

            // mark which fetch entry could be used
            assign fetch_ready_mask_extended = {{{ariane_pkg::ISSUE_WIDTH}{1'b0}}, {{ariane_pkg::ISSUE_WIDTH}{1'b1}}} << issue_reg_avail_cnt;
            assign fetch_ready_mask = issue_reg_trail_all_avail ? {{ariane_pkg::ISSUE_WIDTH}{1'b1}}
                                                                : fetch_ready_mask_extended[ariane_pkg::ISSUE_WIDTH*2-1:ariane_pkg::ISSUE_WIDTH];
        end else begin
            assign fetch_ready_mask = ~issue_reg_usage;
        end
    endgenerate

    // send back handshake signals if we have space in the register
    // and the fetch entry is valid
    assign fetch_entry_ready_o = fetch_ready_mask & decoded_instruction_valid;

    always_comb begin
        issue_n = issue_q;
        issue_n_extended = {issue_candidates, issue_q};

        for (int unsigned i = 0; i < ariane_pkg::ISSUE_WIDTH; i++) begin
            // Clear the valid flag if issue has acknowledged the instruction
            if (issue_instr_ack_i[i])
                issue_n_extended[i].valid = 1'b0;
        end

        if (ISSUE_WIDTH == 1) begin
            issue_n[0] = issue_reg_usage[0] ? issue_n_extended[0] : issue_n_extended[1];
        end else begin
            for (int unsigned i = 0; i < ariane_pkg::ISSUE_WIDTH; i++) begin
                issue_n[i] = (i < issue_reg_busy_cnt) ? issue_n_extended[i+issue_reg_trail_avail_cnt]
                                                      : issue_n_extended[i-issue_reg_busy_cnt+ISSUE_WIDTH];
            end
            issue_n = issue_reg_trail_all_avail ? issue_candidates : issue_n;
        end

        for (int unsigned i = 0; i < ariane_pkg::ISSUE_WIDTH; i++) begin
            // invalidate the pipeline register on a flush
            if (flush_i) begin
                issue_n[i].valid = 1'b0;
            end
        end
    end
    // -------------------------
    // Registers (ID <-> Issue)
    // -------------------------
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if(~rst_ni) begin
            issue_q <= '{default:0};
        end else begin
            issue_q <= issue_n;
        end
    end
endmodule
