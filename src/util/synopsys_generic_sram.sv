// Copyright 2017, 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Date: 13.10.2017
// Description: SRAM Behavioral Model

module sram #(
    parameter DATA_WIDTH = 64,
    parameter NUM_WORDS  = 1024
)(
   input  logic                          clk_i,

   input  logic                          req_i,
   input  logic                          we_i,
   input  logic [$clog2(NUM_WORDS)-1:0]  addr_i,
   input  logic [DATA_WIDTH-1:0]         wdata_i,
   input  logic [DATA_WIDTH-1:0]         be_i,
   output logic [DATA_WIDTH-1:0]         rdata_o
);
    localparam ADDR_WIDTH = $clog2(NUM_WORDS);

    logic [DATA_WIDTH-1:0] ram [NUM_WORDS-1:0];
    logic [ADDR_WIDTH-1:0] raddr_q;

generate
   if ((DATA_WIDTH==16) && (NUM_WORDS==256))
   begin
        sram_16_256 sram(
                     .ADDR(addr_i),
                     .DI(wdata_i),
                     .CLK(clk_i),
                     .WEN(~we_i),
                     .CSN(~req_i),
                     .QO(rdata_o)
                     );
   end
   else if ((DATA_WIDTH==44) && (NUM_WORDS==256))
   begin
        sram_44_256 sram(
                     .ADDR(addr_i),
                     .DI(wdata_i),
                     .CLK(clk_i),
                     .WEN(~we_i),
                     .CSN(~req_i),
                     .QO(rdata_o)
                     );
   end
   else if ((DATA_WIDTH==46) && (NUM_WORDS==256))
   begin
        sram_46_256 sram(
                     .ADDR(addr_i),
                     .DI(wdata_i),
                     .CLK(clk_i),
                     .WEN(~we_i),
                     .CSN(~req_i),
                     .QO(rdata_o)
                     );
   end
   else if ((DATA_WIDTH==64) && (NUM_WORDS==512))
     begin
        sram_64_512 sram(
                     .ADDR(addr_i),
                     .DI(wdata_i),
                     .CLK(clk_i),
                     .WEN(~we_i),
                     .CSN(~req_i),
                     .QO(rdata_o)
                     );
     end
   else if ((DATA_WIDTH==64) && (NUM_WORDS==1024))
     begin
        sram_64_1024 sram(
                     .ADDR(addr_i),
                     .DI(wdata_i),
                     .CLK(clk_i),
                     .WEN(~we_i),
                     .CSN(~req_i),
                     .QO(rdata_o)
                     );
     end
   else if ((DATA_WIDTH==128) && (NUM_WORDS==256))
     begin
        sram_128_256 sram(
                     .ADDR(addr_i),
                     .DI(wdata_i),
                     .CLK(clk_i),
                     .WEN(~we_i),
                     .CSN(~req_i),
                     .QO(rdata_o)
                     );
     end
   else
     begin
        $fatal(1, "(DATA_WIDTH==%d) && (NUM_WORDS==%d)) is not supported", DATA_WIDTH, NUM_WORDS);
     end
endgenerate
   
endmodule
