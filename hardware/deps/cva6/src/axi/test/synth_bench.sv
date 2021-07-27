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

/// A synthesis test bench which instantiates various adapter variants.
module synth_bench (
  input logic clk_i,
  input logic rst_ni
);

  localparam int AXI_ADDR_WIDTH[6] = {32, 64, 1, 2, 42, 129};
  localparam int AXI_ID_USER_WIDTH[3] = {0, 1, 8};
  localparam int NUM_SLAVE_MASTER[3] = {1, 2, 4};

  // AXI_DATA_WIDTH = {8, 16, 32, 64, 128, 256, 512, 1024}
  for (genvar i = 0; i < 8; i++) begin
    localparam DW = (2**i) * 8;
    synth_slice #(.AW(32), .DW(DW), .IW(8), .UW(8)) s(.*);
  end

  // AXI_ADDR_WIDTH
  for (genvar i = 0; i < 6; i++) begin
    localparam int AW = AXI_ADDR_WIDTH[i];
    synth_slice #(.AW(AW), .DW(32), .IW(8), .UW(8)) s(.*);
  end

  // AXI_ID_WIDTH and AXI_USER_WIDTH
  for (genvar i = 0; i < 3; i++) begin
    localparam int IUW = AXI_ID_USER_WIDTH[i];
    synth_slice #(.AW(32), .DW(32), .IW(IUW), .UW(IUW)) s(.*);
  end

  // Crossbar
  for (genvar i = 0; i < 3; i++) begin : xbar_master
    localparam int NM = NUM_SLAVE_MASTER[i];
    for (genvar j = 0; j < 3; j++) begin : xbar_slave
      localparam int NS = NUM_SLAVE_MASTER[j];
      axi_lite_xbar_slice #(.NUM_MASTER(NM), .NUM_SLAVE(NS)) i_xbar (.*);
    end
  end

  // ATOP Filter
  for (genvar iID = 1; iID <= 8; iID++) begin
    localparam int IW = iID;
    for (genvar iTxn = 1; iTxn <= 12; iTxn++) begin
      localparam int WT = iTxn;
      synth_axi_atop_filter #(
        .AXI_ADDR_WIDTH     (64),
        .AXI_DATA_WIDTH     (64),
        .AXI_ID_WIDTH       (IW),
        .AXI_USER_WIDTH     (4),
        .AXI_MAX_WRITE_TXNS (WT)
      ) i_filter (.*);
    end
  end

endmodule


module synth_slice #(
  parameter int AW = -1,
  parameter int DW = -1,
  parameter int IW = -1,
  parameter int UW = -1
)(
  input logic clk_i,
  input logic rst_ni
);

  AXI_BUS #(
    .AXI_ADDR_WIDTH(AW),
    .AXI_DATA_WIDTH(DW),
    .AXI_ID_WIDTH(IW),
    .AXI_USER_WIDTH(UW)
  ) a_full(), b_full();

  AXI_LITE #(
    .AXI_ADDR_WIDTH(AW),
    .AXI_DATA_WIDTH(DW)
  ) a_lite(), b_lite();

  axi_to_axi_lite a (
    .clk_i      (clk_i),
    .rst_ni     (rst_ni),
    .testmode_i (1'b0),
    .in         (a_full.Slave),
    .out        (a_lite.Master)
  );
  axi_lite_to_axi b (
    .in   (b_lite.Slave),
    .out  (b_full.Master)
  );

endmodule


module axi_lite_xbar_slice #(
  parameter int NUM_MASTER = -1,
  parameter int NUM_SLAVE = -1
)(
  input logic clk_i,
  input logic rst_ni
);

  AXI_LITE #(
    .AXI_ADDR_WIDTH(32),
    .AXI_DATA_WIDTH(32)
  ) xbar_master [0:NUM_MASTER-1]();

  AXI_LITE #(
    .AXI_ADDR_WIDTH(32),
    .AXI_DATA_WIDTH(32)
  ) xbar_slave [0:NUM_SLAVE-1]();

  AXI_ROUTING_RULES #(
    .AXI_ADDR_WIDTH(32),
    .NUM_SLAVE(NUM_SLAVE),
    .NUM_RULES(1)
  ) xbar_routing();

  for (genvar i = 0; i < NUM_SLAVE; i++) begin
    assign xbar_routing.rules[i] = {{ 32'hfffff000, 32'h00010000 * i }};
  end

  axi_lite_xbar #(
    .ADDR_WIDTH(32),
    .DATA_WIDTH(32),
    .NUM_MASTER(NUM_MASTER),
    .NUM_SLAVE(NUM_SLAVE),
    .NUM_RULES(1)
  ) xbar (
    .clk_i  ( clk_i              ),
    .rst_ni ( rst_ni             ),
    .master ( xbar_master.Slave  ),
    .slave  ( xbar_slave.Master  ),
    .rules  ( xbar_routing.xbar  )
  );

endmodule


module synth_axi_atop_filter #(
  parameter int unsigned AXI_ADDR_WIDTH = 0,
  parameter int unsigned AXI_DATA_WIDTH = 0,
  parameter int unsigned AXI_ID_WIDTH = 0,
  parameter int unsigned AXI_USER_WIDTH = 0,
  parameter int unsigned AXI_MAX_WRITE_TXNS = 0
) (
  input logic clk_i,
  input logic rst_ni
);

  AXI_BUS #(
    .AXI_ADDR_WIDTH (AXI_ADDR_WIDTH),
    .AXI_DATA_WIDTH (AXI_DATA_WIDTH),
    .AXI_ID_WIDTH   (AXI_ID_WIDTH),
    .AXI_USER_WIDTH (AXI_USER_WIDTH)
  ) upstream ();

  AXI_BUS #(
    .AXI_ADDR_WIDTH (AXI_ADDR_WIDTH),
    .AXI_DATA_WIDTH (AXI_DATA_WIDTH),
    .AXI_ID_WIDTH   (AXI_ID_WIDTH),
    .AXI_USER_WIDTH (AXI_USER_WIDTH)
  ) downstream ();

  axi_atop_filter #(
    .AXI_ID_WIDTH       (AXI_ID_WIDTH),
    .AXI_MAX_WRITE_TXNS (AXI_MAX_WRITE_TXNS)
  ) dut (
    .clk_i  (clk_i),
    .rst_ni (rst_ni),
    .slv    (upstream),
    .mst    (downstream)
  );

endmodule
