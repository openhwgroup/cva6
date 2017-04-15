/* File:   commit_stage.sv
 * Author: Florian Zaruba <zarubaf@ethz.ch>
 * Date:   15.4.2017
 *
 * Copyright (C) 2017 ETH Zurich, University of Bologna
 * All rights reserved.
 *
 * Description: Commits the architectural state resulting from the scoreboard.
 */
import ariane_pkg::*;

module commit_stage (
    input logic                 clk_i,      // Clock
    input logic                 rst_ni,     // Asynchronous reset active low

    output priv_lvl_t           priv_lvl_o,  // privilege level out
    output exception            exception_o, // take exception to controller and if

    // from scoreboard
    input  scoreboard_entry     commit_instr_i,
    output logic                commit_ack_o,

    // to register file
    output  logic[4:0]          waddr_a_o,
    output  logic[63:0]         wdata_a_o,
    output  logic               we_a_o

);

    assign waddr_a_o = commit_instr_i.rd;
    assign wdata_a_o = commit_instr_i.result;

    // commit instruction
    always_comb begin : commit
        // default assignments
        we_a_o = 1'b0;
        if (commit_instr_i.valid) begin
            we_a_o       = 1'b1;
            commit_ack_o = 1'b1;
        end
    end

    // write register file

    // CSR logic

    // privilege check

    // exception logic
endmodule