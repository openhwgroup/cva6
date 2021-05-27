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
// Fabian Schuiki <fschuiki@iis.ee.ethz.ch>

/// A protocol converter from AXI4 to a register interface.
module axi_to_reg #(
  /// The width of the address.
  parameter int ADDR_WIDTH = -1,
  /// The width of the data.
  parameter int DATA_WIDTH = -1,
  /// Whether the AXI-Lite W channel should be decoupled with a register. This
  /// can help break long paths at the expense of registers.
  parameter bit DECOUPLE_W = 1
)(
  input  logic clk_i     ,
  input  logic rst_ni    ,
  input  logic testmode_i,
  AXI_BUS.in   in        ,
  REG_BUS.out  reg_o
);

  AXI_LITE_BUS #(
    .AXI_ADDR_WIDTH ( ADDR_WIDTH ),
    .AXI_DATA_WIDTH ( DATA_WIDTH )
  ) axi_lite (clk_i);

  //  convert axi to axi-lite
  axi_to_axi_lite #(
    /// Maximum number of outstanding reads.
    .NUM_PENDING_RD (1),
    /// Maximum number of outstanding writes.
    .NUM_PENDING_WR (1)
  ) i_axi_to_axi_lite (
    .clk_i,
    .rst_ni,
    .testmode_i,
    .in,
    .out ( axi_lite )
  );

  axi_lite_to_reg #(
    /// The width of the address.
    .ADDR_WIDTH ( ADDR_WIDTH ),
    /// The width of the data.
    .DATA_WIDTH ( DATA_WIDTH ),
    /// Whether the AXI-Lite W channel should be decoupled with a register. This
    /// can help break long paths at the expense of registers.
    .DECOUPLE_W ( DECOUPLE_W )
  ) i_axi_lite_to_reg (
    .clk_i,
    .rst_ni,
    .axi_i ( axi_lite ),
    .reg_o
  );

endmodule
