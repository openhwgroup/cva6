// Author: Florian Zaruba, ETH Zurich
// Date: 03.10.2017
// Description: Re-name registers
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

module re_name (
    input  logic                                   clk_i,    // Clock
    input  logic                                   rst_ni,   // Asynchronous reset active low
    // coming from scoreboard
    input  scoreboard_entry                        issue_instr_i,
    input  logic                                   issue_instr_valid_i,
    output logic                                   issue_ack_o,
    // coming from scoreboard
    output scoreboard_entry                        issue_instr_o,
    output logic                                   issue_instr_valid_o,
    input  logic                                   issue_ack_i
);

    // pass through handshaking signals
    assign issue_instr_valid_o = issue_instr_valid_i;
    assign issue_ack_o         = issue_ack_i;

    // keep track of re-naming data structures
    logic [31:0] re_name_table_n, re_name_table_q;

    // -------------------
    // Re-naming
    // -------------------
    always_comb begin

        // default assignments
        re_name_table_n = re_name_table_q;
        issue_instr_o   = issue_instr_i;

        if (issue_ack_i) begin
            // if we acknowledge the instruction tic the corresponding register
            re_name_table_n[issue_instr_i.rd] = re_name_table_q[issue_instr_i.rd] ^ 1'b1;
        end

        // re-name the source registers
        issue_instr_o.rs1 = { re_name_table_q[issue_instr_i.rs1], issue_instr_i.rs1 };
        issue_instr_o.rs2 = { re_name_table_q[issue_instr_i.rs1], issue_instr_i.rs2 };

        // we don't want to re-name register zero, it is non-writeable anyway
        re_name_table_n[0] = 1'b0;
    end

    // -------------------
    // Registers
    // -------------------
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if(~rst_ni) begin
            re_name_table_q <= '0;
        end else begin
            re_name_table_q <= re_name_table_n;
        end
    end
endmodule
