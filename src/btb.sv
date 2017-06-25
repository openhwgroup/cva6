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
    parameter int NR_ENTRIES = 1024,
    parameter int BITS_SATURATION_COUNTER = 2
    )
    (
    input  logic             clk_i,                     // Clock
    input  logic             rst_ni,                    // Asynchronous reset active low
    input  logic             flush_i,                   // flush the btb

    input  logic [63:0]      vpc_i,                     // virtual PC from IF stage
    input  branchpredict     branch_predict_i,           // a mis-predict happened -> update data structure

    output branchpredict_sbe branch_predict_o            // branch prediction for issuing to the pipeline
);
    // number of bits which are not used for indexing
    localparam OFFSET = 2;

    // typedef for all branch target entries
    // we may want to try to put a tag field that fills the rest of the PC in-order to mitigate aliasing effects
    struct packed {
        logic                                   valid;
        logic [63:0]                            target_address;
        logic [BITS_SATURATION_COUNTER-1:0]     saturation_counter;
        logic                                   is_lower_16;
    } btb_n [NR_ENTRIES-1:0], btb_q [NR_ENTRIES-1:0];

    logic [$clog2(NR_ENTRIES)-1:0]          index, update_pc;
    logic [BITS_SATURATION_COUNTER-1:0]     saturation_counter;

    // get actual index positions
    // we ignore the 0th bit since all instructions are aligned on
    // a half word boundary
    assign update_pc = branch_predict_i.pc[$clog2(NR_ENTRIES) + OFFSET - 1:OFFSET];
    assign index     = vpc_i[$clog2(NR_ENTRIES) + OFFSET - 1:OFFSET];

    // we combinatorially predict the branch and the target address
    assign branch_predict_o.valid           = btb_q[index].valid;
    assign branch_predict_o.predict_taken   = btb_q[index].saturation_counter[BITS_SATURATION_COUNTER-1];
    assign branch_predict_o.predict_address = btb_q[index].target_address;
    assign branch_predict_o.is_lower_16     = btb_q[index].is_lower_16;

    // update on a mis-predict
    always_comb begin : update_branch_predict
        btb_n              = btb_q;
        saturation_counter = btb_q[update_pc].saturation_counter;

        if (branch_predict_i.valid) begin
            btb_n[update_pc].valid = 1'b1;
            // update saturation counter
            // first check if counter is already saturated in the positive regime e.g.: branch taken
            if (saturation_counter == {BITS_SATURATION_COUNTER{1'b1}}) begin
                // we can safely decrease it
                if (~branch_predict_i.is_taken)
                    btb_n[update_pc].saturation_counter = saturation_counter - 1;
            // then check if it saturated in the negative regime e.g.: branch not taken
            end else if (saturation_counter == {BITS_SATURATION_COUNTER{1'b0}}) begin
                // we can safely increase it
                if (branch_predict_i.is_taken)
                    btb_n[update_pc].saturation_counter = saturation_counter + 1;
            end else begin // otherwise we are not in any boundaries and can decrease or increase it
                if (branch_predict_i.is_taken)
                    btb_n[update_pc].saturation_counter = saturation_counter + 1;
                else
                    btb_n[update_pc].saturation_counter = saturation_counter - 1;
            end
            // the target address is simply updated
            btb_n[update_pc].target_address = branch_predict_i.target_address;
            // as is the information whether this was a compressed branch
            btb_n[update_pc].is_lower_16    = branch_predict_i.is_lower_16;
            // check if we should invalidate this entry, this happens in case we predicted a branch
            // where actually none-is (aliasing)
            if (branch_predict_i.clear) begin
                btb_n[update_pc].valid = 1'b0;
            end
        end
    end

    // sequential process
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if(~rst_ni) begin
            // Bias the branches to be taken upon first arrival
            for (int i = 0; i < NR_ENTRIES; i++)
                btb_q[i] <= '{1'b0, 64'b0, 2'b10, 1'b0};
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