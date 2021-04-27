// Copyright 2018 - 2019 ETH Zurich and University of Bologna.
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

// branch target buffer
module btb #(
    parameter int NR_ENTRIES = 8
)(
    input  logic                        clk_i,           // Clock
    input  logic                        rst_ni,          // Asynchronous reset active low
    input  logic                        flush_i,         // flush the btb
    input  logic                        debug_mode_i,

    input  logic [riscv::VLEN-1:0]      vpc_i,           // virtual PC from IF stage
    input  ariane_pkg::btb_update_t     btb_update_i,    // update btb with this information
    output ariane_pkg::btb_prediction_t [ariane_pkg::INSTR_PER_FETCH-1:0] btb_prediction_o // prediction from btb
);
    // the last bit is always zero, we don't need it for indexing
    localparam OFFSET = 1;
    // re-shape the branch history table
    localparam NR_ROWS = NR_ENTRIES / ariane_pkg::INSTR_PER_FETCH;
    // number of bits needed to index the row
    localparam ROW_ADDR_BITS = $clog2(ariane_pkg::INSTR_PER_FETCH);
    // number of bits we should use for prediction
    localparam PREDICTION_BITS = $clog2(NR_ROWS) + OFFSET + ROW_ADDR_BITS;
    // prevent aliasing to degrade performance
    localparam ANTIALIAS_BITS = 8;
    // we are not interested in all bits of the address
    unread i_unread (.d_i(|vpc_i));

    // typedef for all branch target entries
    // we may want to try to put a tag field that fills the rest of the PC in-order to mitigate aliasing effects
    ariane_pkg::btb_prediction_t btb_d [NR_ROWS-1:0][ariane_pkg::INSTR_PER_FETCH-1:0],
                                 btb_q [NR_ROWS-1:0][ariane_pkg::INSTR_PER_FETCH-1:0];
    logic [$clog2(NR_ROWS)-1:0]  index, update_pc;
    logic [ROW_ADDR_BITS-1:0]    update_row_index;

    assign index     = vpc_i[PREDICTION_BITS - 1:ROW_ADDR_BITS + OFFSET];
    assign update_pc = btb_update_i.pc[PREDICTION_BITS - 1:ROW_ADDR_BITS + OFFSET];
    assign update_row_index = btb_update_i.pc[ROW_ADDR_BITS + OFFSET - 1:OFFSET];

    // output matching prediction
    for (genvar i = 0; i < ariane_pkg::INSTR_PER_FETCH; i++) begin : gen_btb_output
        assign btb_prediction_o[i] = btb_q[index][i]; // workaround
    end

    // -------------------------
    // Update Branch Prediction
    // -------------------------
    // update on a mis-predict
    always_comb begin : update_branch_predict
        btb_d = btb_q;

        if (btb_update_i.valid && !debug_mode_i) begin
            btb_d[update_pc][update_row_index].valid = 1'b1;
            // the target address is simply updated
            btb_d[update_pc][update_row_index].target_address = btb_update_i.target_address;
        end
    end

    // sequential process
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            // Bias the branches to be taken upon first arrival
            for (int i = 0; i < NR_ROWS; i++)
                btb_q[i] <= '{default: 0};
        end else begin
            // evict all entries
            if (flush_i) begin
                for (int i = 0; i < NR_ROWS; i++) begin
                    for (int j = 0; j < ariane_pkg::INSTR_PER_FETCH; j++) begin
                        btb_q[i][j].valid <=  1'b0;
                    end
                end
            end else begin
                btb_q <=  btb_d;
            end
        end
    end
endmodule
