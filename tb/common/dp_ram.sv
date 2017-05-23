// Copyright 2015 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the “License”); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an “AS IS” BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

module dp_ram
  #(
    parameter ADDR_WIDTH = 8
  )(
    // Clock and Reset
    input  logic clk,

    input  logic                   en_a_i,
    input  logic [ADDR_WIDTH-1:0]  addr_a_i,
    input  logic [31:0]            wdata_a_i,
    output logic [31:0]            rdata_a_o,
    input  logic                   we_a_i,
    input  logic [3:0]             be_a_i,

    input  logic                   en_b_i,
    input  logic [ADDR_WIDTH-1:0]  addr_b_i,
    input  logic [31:0]            wdata_b_i,
    output logic [31:0]            rdata_b_o,
    input  logic                   we_b_i,
    input  logic [3:0]             be_b_i
  );

  localparam words = 2**ADDR_WIDTH;

  logic [3:0][7:0] mem[words];

  always @(posedge clk)
  begin
    if (en_a_i && we_a_i)
    begin
      if (be_a_i[0])
        mem[addr_a_i][0] <= wdata_a_i[7:0];
      if (be_a_i[1])
        mem[addr_a_i][1] <= wdata_a_i[15:8];
      if (be_a_i[2])
        mem[addr_a_i][2] <= wdata_a_i[23:16];
      if (be_a_i[3])
        mem[addr_a_i][3] <= wdata_a_i[31:24];
    end

    rdata_a_o <= mem[addr_a_i];

    if (en_b_i && we_b_i)
    begin
      if (be_b_i[0])
        mem[addr_b_i][0] <= wdata_b_i[7:0];
      if (be_b_i[1])
        mem[addr_b_i][1] <= wdata_b_i[15:8];
      if (be_b_i[2])
        mem[addr_b_i][2] <= wdata_b_i[23:16];
      if (be_b_i[3])
        mem[addr_b_i][3] <= wdata_b_i[31:24];
    end

    rdata_b_o <= mem[addr_b_i];
  end

endmodule
