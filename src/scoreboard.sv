// Author: Florian Zaruba, ETH Zurich
// Date: 08.04.2017
// Description: Scoreboard - keeps track of all decoded, issued and committed instructions
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

module scoreboard #(
    parameter int  NR_ENTRIES  = 8,
    parameter int  NR_WB_PORTS = 1
    )
    (
    input  logic                                      clk_i,    // Clock
    input  logic                                      rst_ni,   // Asynchronous reset active low
    output logic                                      full_o,   // We can't take anymore data
    input  logic                                      flush_i,  // flush whole scoreboard
    input  logic                                      flush_unissued_instr_i,
    // list of clobbered registers to issue stage
    output fu_t [31:0]                                rd_clobber_o,

    // regfile like interface to operand read stage
    input  logic [4:0]                                rs1_i,
    output logic [63:0]                               rs1_o,
    output logic                                      rs1_valid_o,

    input  logic [4:0]                                rs2_i,
    output logic [63:0]                               rs2_o,
    output logic                                      rs2_valid_o,

    // advertise instruction to commit stage, if commit_ack_i is asserted advance the commit pointer
    output scoreboard_entry                           commit_instr_o,
    input  logic                                      commit_ack_i,

    // instruction to put on top of scoreboard e.g.   : top pointer
    // we can always put this instruction to the to   p unless we signal with asserted full_o
    input  scoreboard_entry                           decoded_instr_i,
    input  logic                                      decoded_instr_valid_i,
    output logic                                      decoded_instr_ack_o,

    // instruction to issue logic, if issue_instr_valid and issue_ready is asserted, advance the issue pointer
    output scoreboard_entry                           issue_instr_o,
    output logic                                      issue_instr_valid_o,
    input  logic                                      issue_ack_i,

    // write-back port
    input logic [NR_WB_PORTS-1:0][TRANS_ID_BITS-1:0]  trans_id_i,  // transaction ID at which to write the result back
    input logic [NR_WB_PORTS-1:0][63:0]               wdata_i,     // write data in
    input exception [NR_WB_PORTS-1:0]                 ex_i,        // exception from a functional unit (e.g.: ld/st exception, divide by zero)
    input logic [NR_WB_PORTS-1:0]                     wb_valid_i   // data in is valid
);
    localparam BITS_ENTRIES      = $clog2(NR_ENTRIES);

    // this is the FIFO struct of the issue queue
    struct packed {
        logic            issued; // this bit indicates whether we issued this instruction e.g.: if it is valid
        scoreboard_entry sbe;    // this is the score board entry we will send to ex
    } mem_q [NR_ENTRIES-1:0], mem_n [NR_ENTRIES-1:0];

    logic [$clog2(NR_ENTRIES)-1:0] issue_cnt_n,      issue_cnt_q;
    logic [$clog2(NR_ENTRIES)-1:0] issue_pointer_n,  issue_pointer_q;
    logic [$clog2(NR_ENTRIES)-1:0] commit_pointer_n, commit_pointer_q;
    logic                          issue_full;

    // the issue queue is full don't issue any new instructions
    assign issue_full = (issue_cnt_q == NR_ENTRIES);
    // output commit instruction directly
    assign commit_instr_o = mem_q[commit_pointer_q].sbe;

    // an instruction is ready for issue if we have place in the issue FIFO and it the decoder says it is valid
    always_comb begin
        issue_instr_o          = decoded_instr_i;
        // make sure we assign the correct trans ID
        issue_instr_o.trans_id = issue_pointer_q;
        issue_instr_valid_o    = ~issue_full && decoded_instr_valid_i && !flush_unissued_instr_i;
        decoded_instr_ack_o    = issue_ack_i;
    end
    // maintain a FIFO with issued instructions
    // keep track of all issued instructions
    always_comb begin : issue_fifo
        automatic logic [$clog2(NR_ENTRIES)-1:0] issue_cnt = issue_cnt_q;
        // default assignment
        mem_n            = mem_q;
        commit_pointer_n = commit_pointer_q;
        issue_pointer_n  = issue_pointer_q;

        // if we got a acknowledge from the FIFO, put this scoreboard entry in the queue
        if (issue_ack_i) begin
            // increase the issue counter
            issue_cnt++;
            // the decoded instruction we put in there is valid (1st bit)
            mem_n[issue_pointer_q] = {1'b1, decoded_instr_i};
            // advance issue pointer
            issue_pointer_n = issue_pointer_q + 1'b1;
        end

        // we've got an acknowledge from commit
        if (commit_ack_i) begin
            // decrease the issue counter
            issue_cnt--;
            // this instruction is no longer in issue e.g.: it is considered finished
            mem_n[commit_pointer_q].issued    = 1'b0;
            mem_n[commit_pointer_q].sbe.valid = 1'b0;
            // advance commit pointer
            commit_pointer_n = commit_pointer_n + 1'b1;
        end
        // ------------
        // Write Back
        // ------------
        for (int i = 0; i < NR_WB_PORTS; i++) begin
            if (wb_valid_i[i]) begin
                mem_n[trans_id_i[i]].sbe.valid  = 1'b1;
                mem_n[trans_id_i[i]].sbe.result = wdata_i[i];
                mem_n[trans_id_i[i]].sbe.ex     = ex_i[i];
            end
        end

        // ------
        // Flush
        // ------
        if (flush_i) begin
            for (int i = 0; i < NR_ENTRIES; i++) begin
                // set all valid flags for all entries to zero
                mem_n[i].issued       = 1'b0;
                mem_n[i].sbe.valid    = 1'b0;
                mem_n[i].sbe.ex.valid = 1'b0;
                // set the pointer and counter back to zero
                issue_cnt             = '0;
                issue_pointer_n       = '0;
                commit_pointer_n      = '0;
            end
        end
        // update issue counter
        issue_cnt_n      = issue_cnt;
    end

    // -------------------
    // RD clobber process
    // -------------------
    // rd_clobber output: output currently clobbered destination registers
    always_comb begin : clobber_output
        rd_clobber_o = '{default: NONE};
        // check for all valid entries and set the clobber register accordingly
        for (int i = 0; i < NR_ENTRIES; i++) begin
            if (mem_q[i].issued) begin
                // output the functional unit which is going to clobber this register
                rd_clobber_o[mem_q[i].sbe.rd] = mem_q[i].sbe.fu;
            end
        end
        // the zero register is always free
        rd_clobber_o[0] = NONE;
    end

    // ----------------------------------
    // Read Operands (a.k.a forwarding)
    // ----------------------------------
    // read operand interface: same logic as register file
    always_comb begin : read_operands
        rs1_o       = 64'b0;
        rs2_o       = 64'b0;
        rs1_valid_o = 1'b0;
        rs2_valid_o = 1'b0;

        for (int i = 0; i < NR_ENTRIES; i++) begin
            // only consider this entry if it is valid
            if (mem_q[i].issued) begin
                // look at the appropriate fields and look whether there was an
                // instruction that wrote the rd field before, first for RS1 and then for RS2
                if (mem_q[i].sbe.rd == rs1_i) begin
                    rs1_o       = mem_q[i].sbe.result;
                    rs1_valid_o = mem_q[i].sbe.valid;
                end else if (mem_q[i].sbe.rd == rs2_i) begin
                    rs2_o       = mem_q[i].sbe.result;
                    rs2_valid_o = mem_q[i].sbe.valid;
                end
            end
        end
    end

    // sequential process
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if(~rst_ni) begin
            mem_q            <= '{default: 0};
            issue_cnt_q      <= '0;
            commit_pointer_q <= '0;
            issue_pointer_q  <= '0;
        end else begin
            mem_q <= mem_n;
            issue_cnt_q      <= issue_cnt_n;
            commit_pointer_q <= commit_pointer_n;
            issue_pointer_q  <= issue_pointer_n;
        end
    end
endmodule
