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
// Author: Florian Zaruba    <zarubaf@iis.ee.ethz.ch>, ETH Zurich
//         Michael Schaffner <schaffner@iis.ee.ethz.ch>, ETH Zurich
// Date: 15.08.2018
// Description: valid/dirty regfile for caches
//

module vdregs #(
    parameter DATA_WIDTH = 64,
    parameter DATA_DEPTH = 1024
)(
    input  logic                          clk_i,
    input  logic                          rst_ni,
    input  logic                          req_i,
    input  logic                          we_i,
    input  logic [$clog2(DATA_DEPTH)-1:0] addr_i,
    input  logic [DATA_WIDTH-1:0]         wdata_i,
    input  logic [DATA_WIDTH-1:0]         biten_i, // bit enable
    output logic [DATA_WIDTH-1:0]         rdata_o
);
    localparam ADDR_WIDTH = $clog2(DATA_DEPTH);
    logic [DATA_WIDTH-1:0] regs_q [DATA_DEPTH-1:0];
    
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if(~rst_ni) begin
            regs_q <= '{default:0};
        end else if (req_i) begin
            if (we_i) begin 
                for (int i = 0; i < DATA_WIDTH; i++)
                    if (biten_i[i]) regs_q[addr_i][i] <= wdata_i[i];
            end
            rdata_o <= regs_q[addr_i];
        end
    end

endmodule : vdregs
