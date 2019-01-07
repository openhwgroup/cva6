/* Copyright 2018 ETH Zurich and University of Bologna.
 * Copyright and related rights are licensed under the Solderpad Hardware
 * License, Version 0.51 (the "License"); you may not use this file except in
 * compliance with the License.  You may obtain a copy of the License at
 * http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
 * or agreed to in writing, software, hardware and materials distributed under
 * this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
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
    localparam int RomSize = 13;

    const logic [RomSize-1:0][63:0] mem = {
        64'h00000000_00000000,
        64'h7B200073_7B202473,
        64'h10802423_F1402473,
        64'h30000067_10002223,
        64'h7B202473_00100073,
        64'h10002623_FDDFF06F,
        64'hFC0418E3_00247413,
        64'h40044403_F1402473,
        64'h02041063_00147413,
        64'h40044403_10802023,
        64'hF1402473_7B241073,
        64'h0FF0000F_0340006F,
        64'h04C0006F_00C0006F
    };

    logic [$clog2(RomSize)-1:0] addr_q;

    always_ff @(posedge clk_i) begin
        if (req_i) begin
            addr_q <= addr_i[$clog2(RomSize)-1+3:3];
        end
    end

    // this prevents spurious Xes from propagating into 
    // the speculative fetch stage of the core
    assign rdata_o = (addr_q<RomSize) ? mem[addr_q] : '0;
endmodule
