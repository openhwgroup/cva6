//-----------------------------------------------------------------------------
// Title         : FPGA Bootrom for PULP
//-----------------------------------------------------------------------------
// File          : fpga_bootrom.sv
// Author        : Jie Chen  <owenchj@gmail.com>
// Created       : 23.10.2019
//-----------------------------------------------------------------------------
// Description :
// Real boot with jtag reaction.
//-----------------------------------------------------------------------------
// Copyright (C) 2013-2019 ETH Zurich, University of Bologna
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//-----------------------------------------------------------------------------


module bootrom
   (
   input  logic         clk_i,
   input  logic         req_i,
   input  logic [63:0]  addr_i,
   output logic [63:0]  rdata_o,
   input  logic         rst
    );

   logic [7:0]                    wea;
   logic [63:0]                   dina;

   assign wea  = 8'b00000000;
   assign dina = 64'h00000000_00000000;

   xilinx_rom_bank_256x64 rom_mem_i (
                                      .clka  (clk_i),
                                      .rsta  (~rst),
                                      .ena   (~req_i),
                                      .wea   (wea),
                                      .addra (addr_i[9:2]),
                                      .dina  (dina),
                                      .douta (rdata_o)
                                      );

endmodule
