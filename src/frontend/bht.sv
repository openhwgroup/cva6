//Copyright (C) 2018 to present,
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 2.0 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-2.0. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.//
// Author: Florian Zaruba, ETH Zurich
// Date: 08.02.2018
// Migrated: Luis Vitorio Cargnini, IEEE
// Date: 09.06.2018

// branch history table - 2 bit saturation counter
module bht #(
    parameter int unsigned NR_ENTRIES = 1024
)(
    input  logic                        clk_i,
    input  logic                        rst_ni,
    input  logic                        flush_i,
    input  logic                        debug_mode_i,

    input  logic [63:0]                 vpc_i,
    input  ariane_pkg::bht_update_t     bht_update_i,
    output ariane_pkg::bht_prediction_t bht_prediction_o
);
    localparam OFFSET = 2; // we are using compressed instructions so do not use the lower 2 bits for prediction
    localparam ANTIALIAS_BITS = 8;
    // number of bits we should use for prediction
    localparam PREDICTION_BITS = $clog2(NR_ENTRIES) + OFFSET;

    struct packed {
        logic       valid;
        logic [1:0] saturation_counter;
    } bht_d[NR_ENTRIES-1:0], bht_q[NR_ENTRIES-1:0];

    logic [$clog2(NR_ENTRIES)-1:0]  index, update_pc;
    logic [1:0]                     saturation_counter;

    assign index     = vpc_i[PREDICTION_BITS - 1:OFFSET];
    assign update_pc = bht_update_i.pc[PREDICTION_BITS - 1:OFFSET];
    // prediction assignment
    assign bht_prediction_o.valid = bht_q[index].valid;
    assign bht_prediction_o.taken = bht_q[index].saturation_counter == 2'b10;
    assign bht_prediction_o.strongly_taken = (bht_q[index].saturation_counter == 2'b11);
    always_comb begin : update_bht
        bht_d = bht_q;
        saturation_counter = bht_q[update_pc].saturation_counter;

        if (bht_update_i.valid && !debug_mode_i) begin
            bht_d[update_pc].valid = 1'b1;

            if (saturation_counter == 2'b11) begin
                // we can safely decrease it
                if (~bht_update_i.taken)
                    bht_d[update_pc].saturation_counter = saturation_counter - 1;
            // then check if it saturated in the negative regime e.g.: branch not taken
            end else if (saturation_counter == 2'b00) begin
                // we can safely increase it
                if (bht_update_i.taken)
                    bht_d[update_pc].saturation_counter = saturation_counter + 1;
            end else begin // otherwise we are not in any boundaries and can decrease or increase it
                if (bht_update_i.taken)
                    bht_d[update_pc].saturation_counter = saturation_counter + 1;
                else
                    bht_d[update_pc].saturation_counter = saturation_counter - 1;
            end
        end
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (~rst_ni) begin
            for (int unsigned i = 0; i < NR_ENTRIES; i++)
                bht_q[i] <= '0;
        end else begin
            // evict all entries
            if (flush_i) begin
                for (int i = 0; i < NR_ENTRIES; i++) begin
                    bht_q[i].valid <=  1'b0;
                    bht_q[i].saturation_counter <= 2'b10;
                end
            end else begin
                bht_q <= bht_d;
            end
        end
    end
endmodule
