// Author: Florian Zaruba, ETH Zurich
// Date: 19.04.2017
// Description: Branch Target Buffer implementation
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

module btb #(
    parameter int NR_ENTRIES = 64,
    parameter int BITS_SATURATION_COUNTER = 2
    )
    (
    input  logic            clk_i,                     // Clock
    input  logic            rst_ni,                    // Asynchronous reset active low
    input  logic            flush_i,                   // flush the btb

    input  logic [63:0]     vpc_i,                     // virtual PC from IF stage
    input  branchpredict    branchpredict_i,           // a miss-predict happened -> update data structure

    output logic            is_branch_o,               // instruction at vpc_i is a branch
    output logic            predict_taken_o,           // the branch is taken
    output logic [63:0]     branch_target_address_o    // instruction has the following target address
);
    // number of bits which are not used for indexing
    localparam OFFSET = 2;

    // typedef for all branch target entries
    // we may want to try to put a tag field that fills the rest of the PC in-order to mitigate aliasing effects
    struct packed {
        logic                                   valid;
        logic [63:0]                            target_address;
        logic [BITS_SATURATION_COUNTER-1:0]     saturation_counter;
    } btb_n [NR_ENTRIES-1:0], btb_q [NR_ENTRIES-1:0];

    logic [$clog2(NR_ENTRIES)-1:0]          index, update_pc;
    logic [BITS_SATURATION_COUNTER-1:0]     saturation_counter;

    // get actual index positions
    // we ignore the 0th bit since all instructions are aligned on
    // a half word boundary
    assign update_pc = branchpredict_i.pc[$clog2(NR_ENTRIES) + OFFSET - 1:OFFSET];
    assign index     = vpc_i[$clog2(NR_ENTRIES) + OFFSET - 1:OFFSET];

    // we combinatorially predict the branch and the target address
    assign is_branch_o             = btb_q[$unsigned(index)].valid;
    assign predict_taken_o         = btb_q[$unsigned(index)].saturation_counter[BITS_SATURATION_COUNTER-1];
    assign branch_target_address_o = btb_q[$unsigned(index)].target_address;

    // update on a mis-predict
    always_comb begin : update_branchpredict
        btb_n              = btb_q;
        saturation_counter = btb_q[$unsigned(update_pc)].saturation_counter;

        if (branchpredict_i.valid) begin
            btb_n[$unsigned(update_pc)].valid = 1'b1;
            // update saturation counter
            // first check if counter is already saturated in the positive regime e.g.: branch taken
            if (saturation_counter == {BITS_SATURATION_COUNTER{1'b1}}) begin
                // we can safely decrease it
                if (~branchpredict_i.is_taken)
                    btb_n[$unsigned(update_pc)].saturation_counter = saturation_counter - 1;
            // then check if it saturated in the negative regime e.g.: branch not taken
            end else if (saturation_counter == {BITS_SATURATION_COUNTER{1'b0}}) begin
                // we can safely increase it
                if (branchpredict_i.is_taken)
                    btb_n[$unsigned(update_pc)].saturation_counter = saturation_counter + 1;
            end else begin // otherwise we are not in any boundaries and can decrease or increase it
                if (branchpredict_i.is_taken)
                    btb_n[$unsigned(update_pc)].saturation_counter = saturation_counter + 1;
                else
                    btb_n[$unsigned(update_pc)].saturation_counter = saturation_counter - 1;
            end
            // the target address is simply updated
            btb_n[$unsigned(update_pc)].target_address = branchpredict_i.target_address;
        end
    end

    // sequential process
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if(~rst_ni) begin
            // Bias the branches to be taken upon first arrival
            for (int i = 0; i < NR_ENTRIES; i++)
                btb_q[i] <= '{1'b0, 64'b0, 2'b10};
        end else begin
            // evict all entries
            if (flush_i) begin
                for (int i = 0; i < NR_ENTRIES; i++) begin
                    btb_q[i].valid              <=  1'b0;
                    btb_q[i].saturation_counter <= '{default: 0};
                end
            end else begin
                btb_q <=  btb_n;
            end
        end
    end
endmodule