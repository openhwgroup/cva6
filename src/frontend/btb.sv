//Copyright (C) 2018 to present,
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 2.0 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-2.0. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Florian Zaruba, ETH Zurich
// Date: 08.02.2018
// Migrated: Luis Vitorio Cargnini, IEEE
// Date: 09.06.2018

// ------------------------------
// Branch Prediction
// ------------------------------

// branch target buffer
module btb #(
    parameter int NR_ENTRIES = 8
)(
    input  logic                        clk_i,           // Clock
    input  logic                        rst_ni,          // Asynchronous reset active low
    input  logic                        flush_i,         // flush the btb
    input  logic                        debug_mode_i,

    input  logic [63:0]                 vpc_i,           // virtual PC from IF stage
    input  ariane_pkg::btb_update_t     btb_update_i,    // update btb with this information
    output ariane_pkg::btb_prediction_t btb_prediction_o // prediction from btb
);
    // number of bits which are not used for indexing
    localparam OFFSET = 1; // we are using compressed instructions so do use the lower 2 bits for prediction
    localparam ANTIALIAS_BITS = 8;
    // number of bits we should use for prediction
    localparam PREDICTION_BITS = $clog2(NR_ENTRIES) + OFFSET;
    // typedef for all branch target entries
    // we may want to try to put a tag field that fills the rest of the PC in-order to mitigate aliasing effects
    ariane_pkg::btb_prediction_t btb_d [NR_ENTRIES-1:0], btb_q [NR_ENTRIES-1:0];
    logic [$clog2(NR_ENTRIES)-1:0]          index, update_pc;

    assign index     = vpc_i[PREDICTION_BITS - 1:OFFSET];
    assign update_pc = btb_update_i.pc[PREDICTION_BITS - 1:OFFSET];

    // output matching prediction
    assign btb_prediction_o = btb_q[index];

    // -------------------------
    // Update Branch Prediction
    // -------------------------
    // update on a mis-predict
    always_comb begin : update_branch_predict
        btb_d = btb_q;

        if (btb_update_i.valid && !debug_mode_i) begin
            btb_d[update_pc].valid = 1'b1;
            // the target address is simply updated
            btb_d[update_pc].target_address = btb_update_i.target_address;
            // check if we should invalidate this entry, this happens in case we predicted a branch
            // where actually none-is (aliasing)
            if (btb_update_i.clear) begin
                btb_d[update_pc].valid = 1'b0;
            end
        end
    end

    // sequential process
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (~rst_ni) begin
            // Bias the branches to be taken upon first arrival
            for (int i = 0; i < NR_ENTRIES; i++)
                btb_q[i] <= '{default: 0};
        end else begin
            // evict all entries
            if (flush_i) begin
                for (int i = 0; i < NR_ENTRIES; i++) begin
                    btb_q[i].valid <=  1'b0;
                end
            end else begin
                btb_q <=  btb_d;
            end
        end
    end
endmodule
