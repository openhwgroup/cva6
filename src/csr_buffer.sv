// Author: Florian Zaruba, ETH Zurich
// Date: 05.05.2017
// Description: Buffer to hold CSR address, this acts like a functional unit
//              to the scoreboard.
//
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
import ariane_pkg::*;

module csr_buffer (
    input  logic                     clk_i,          // Clock
    input  logic                     rst_ni,         // Asynchronous reset active low
    input  logic                     flush_i,

    input  fu_op                     operator_i,
    input  logic [63:0]              operand_a_i,
    input  logic [63:0]              operand_b_i,
    input  logic [TRANS_ID_BITS-1:0] trans_id_i,     // transaction id, needed for WB

    output logic                     csr_ready_o,    // FU is ready e.g. not busy
    input  logic                     csr_valid_i,    // Input is valid
    output logic [TRANS_ID_BITS-1:0] csr_trans_id_o, // ID of scoreboard entry at which to write back
    output logic [63:0]              csr_result_o,
    output logic                     csr_valid_o,    // transaction id for which the output is the requested one
    input  logic                     commit_i,       // commit the pending CSR OP

    // to CSR file
    input  logic  [11:0]             csr_addr_o      // CSR address to commit stage
);
    // control logic, scoreboard signals
    assign csr_trans_id_o = trans_id_i;
    assign csr_valid_o    = csr_reg_q.valid | csr_valid_i;
    assign csr_result_o   = operand_a_i;
    assign csr_ready_o    = (csr_reg_q.valid && ~commit_i) ? 1'b0 : 1'b1;
    assign csr_addr_o     = csr_reg_q.csr_address;

    // this is a single entry store buffer for the address of the CSR
    // which we are going to need in the commit stage
    struct {
        logic [11:0] csr_address;
        logic        valid;
    } csr_reg_n, csr_reg_q;

    // write logic
    always_comb begin : write
        csr_reg_n = csr_reg_q;

        // if we got a valid from the scoreboard
        // store the CSR address
        if (csr_valid_i) begin
            csr_reg_n.csr_address = operand_b_i[11:0];
            csr_reg_n.valid       = 1'b1;
        end
        // if we get a commit and no new valid instruction -> clear the valid bit
        if (commit_i && ~csr_valid_i) begin
            csr_reg_n.valid       = 1'b0;
        end
    end
    // sequential process
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if(~rst_ni) begin
            csr_reg_q <= '{default: 0};
        end else begin
            csr_reg_q <= csr_reg_n;
        end
    end

endmodule