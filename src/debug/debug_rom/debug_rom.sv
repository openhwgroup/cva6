/* Copyright 2018 ETH Zurich and University of Bologna.
 * Copyright and related rights are licensed under the Solderpad Hardware
 * License, Version 0.51 (the “License”); you may not use this file except in
 * compliance with the License.  You may obtain a copy of the License at
 * http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
 * or agreed to in writing, software, hardware and materials distributed under
 * this License is distributed on an “AS IS” BASIS, WITHOUT WARRANTIES OR
 * CONDITIONS OF ANY KIND, either express or implied. See the License for the
 * specific language governing permissions and limitations under the License.
 *
 * File: $filename.v
 *
 * Description: Auto-generated bootrom
 */

// Auto-generated code
module debug_rom (
   input  logic         clk_i,
   input  logic         req_i,
   input  logic [63:0]  addr_i,
   output logic [63:0]  rdata_o
);
    localparam int RomSize = 12;

    const logic [RomSize-1:0][63:0] mem = {
        64'h7b200073_7b202473,
        64'h10802423_f1402473,
        64'h30000067_10002223,
        64'h7b202473_00100073,
        64'h10002623_fddff06f,
        64'hfc0418e3_00247413,
        64'h40044403_f1402473,
        64'h02041063_00147413,
        64'h40044403_10802023,
        64'hf1402473_7b241073,
        64'h0ff0000f_0340006f,
        64'h04c0006f_00c0006f
    };

    logic [$clog2(RomSize)-1:0] addr_q;

    always_ff @(posedge clk_i) begin
        if (req_i) begin
            addr_q = addr_i[$clog2(RomSize)-1+3:3];
        end
    end

    assign rdata_o = mem[addr_q];
endmodule
