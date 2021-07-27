// Copyright (c) 2014-2018 ETH Zurich, University of Bologna
//
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

import axi_pkg::*;


/// Multiple AXI4 cuts.
///
/// These can be used to relax timing pressure on very long AXI busses.
module axi_multicut #(
  /// The address width.
  parameter int ADDR_WIDTH = -1,
  /// The data width.
  parameter int DATA_WIDTH = -1,
  /// The ID width.
  parameter int ID_WIDTH = -1,
  // The user data width.
  parameter int USER_WIDTH = -1,
  // The number of cuts. Must be >= 0.
  parameter int NUM_CUTS = 0
)(
  input logic     clk_i  ,
  input logic     rst_ni ,
  AXI_BUS.Slave   in     ,
  AXI_BUS.Master  out
);

  // Check the invariants.
  `ifndef SYNTHESIS
  initial begin
    assert(NUM_CUTS >= 0);
  end
  `endif

  // Handle the special case of no cuts.
  if (NUM_CUTS == 0) begin : g_cuts
    axi_join i_join (
      .in  ( in  ),
      .out ( out )
    );
  end

  // Handle the special case of one cut.
  else if (NUM_CUTS == 1) begin : g_cuts
    axi_cut #(
      .ADDR_WIDTH ( ADDR_WIDTH ),
      .DATA_WIDTH ( DATA_WIDTH ),
      .ID_WIDTH   ( ID_WIDTH   ),
      .USER_WIDTH ( USER_WIDTH )
    ) i_cut (
      .clk_i  ( clk_i  ),
      .rst_ni ( rst_ni ),
      .in     ( in     ),
      .out    ( out    )
    );
  end

  // Handle the cases of two or more cuts.
  else begin : g_cuts
    AXI_BUS #(
      .AXI_ADDR_WIDTH ( ADDR_WIDTH ),
      .AXI_DATA_WIDTH ( DATA_WIDTH ),
      .AXI_ID_WIDTH   ( ID_WIDTH   ),
      .AXI_USER_WIDTH ( USER_WIDTH )
    ) s_cut[NUM_CUTS-1:0]();

    axi_cut #(
      .ADDR_WIDTH ( ADDR_WIDTH ),
      .DATA_WIDTH ( DATA_WIDTH ),
      .ID_WIDTH   ( ID_WIDTH   ),
      .USER_WIDTH ( USER_WIDTH )
    ) i_first (
      .clk_i  ( clk_i           ),
      .rst_ni ( rst_ni          ),
      .in     ( in              ),
      .out    ( s_cut[0].Master )
    );

    for (genvar i = 1; i < NUM_CUTS-1; i++) begin
      axi_cut #(
        .ADDR_WIDTH ( ADDR_WIDTH ),
        .DATA_WIDTH ( DATA_WIDTH ),
        .ID_WIDTH   ( ID_WIDTH   ),
        .USER_WIDTH ( USER_WIDTH )
      ) i_middle (
        .clk_i  ( clk_i             ),
        .rst_ni ( rst_ni            ),
        .in     ( s_cut[i-1].Slave  ),
        .out    ( s_cut[i].Master   )
      );
    end

    axi_cut #(
      .ADDR_WIDTH ( ADDR_WIDTH ),
      .DATA_WIDTH ( DATA_WIDTH ),
      .ID_WIDTH   ( ID_WIDTH   ),
      .USER_WIDTH ( USER_WIDTH )
    ) i_last (
      .clk_i  ( clk_i                   ),
      .rst_ni ( rst_ni                  ),
      .in     ( s_cut[NUM_CUTS-2].Slave ),
      .out    ( out                     )
    );
  end

endmodule
