// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Fabian Schuiki <fschuiki@iis.ee.ethz.ch>

`include "axi/assign.svh"

module tb_axi_lite_to_axi;

  parameter AW = 32;
  parameter DW = 32;
  parameter IW = 8;
  parameter UW = 8;

  localparam tCK = 1ns;

  logic clk = 0;
  logic rst = 1;
  logic done = 0;

  AXI_LITE_DV #(
    .AXI_ADDR_WIDTH(AW),
    .AXI_DATA_WIDTH(DW)
  ) axi_lite_dv(clk);

  AXI_LITE #(
    .AXI_ADDR_WIDTH(AW),
    .AXI_DATA_WIDTH(DW)
  ) axi_lite();

  `AXI_LITE_ASSIGN(axi_lite, axi_lite_dv);

  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH(AW),
    .AXI_DATA_WIDTH(DW),
    .AXI_ID_WIDTH(IW),
    .AXI_USER_WIDTH(UW)
  ) axi_dv(clk);

  AXI_BUS #(
    .AXI_ADDR_WIDTH(AW),
    .AXI_DATA_WIDTH(DW),
    .AXI_ID_WIDTH(IW),
    .AXI_USER_WIDTH(UW)
  ) axi();

  `AXI_ASSIGN(axi_dv, axi);

  axi_lite_to_axi i_dut (
    .in   ( axi_lite ),
    .out  ( axi      )
  );

  axi_test::axi_lite_driver #(.AW(AW), .DW(DW)) axi_lite_drv = new(axi_lite_dv);
  axi_test::axi_driver #(.AW(AW), .DW(DW), .IW(IW), .UW(UW)) axi_drv = new(axi_dv);

  initial begin
    #tCK;
    rst <= 0;
    #tCK;
    rst <= 1;
    #tCK;
    while (!done) begin
      clk <= 1;
      #(tCK/2);
      clk <= 0;
      #(tCK/2);
    end
  end

  initial begin
    automatic axi_pkg::resp_t resp;
    axi_lite_drv.reset_master();
    @(posedge clk);
    axi_lite_drv.send_aw('hdeadbeef);
    axi_lite_drv.send_w('hdeadbeef, '1);
    axi_lite_drv.recv_b(resp);
    $info("AXI-Lite B: resp %h", resp);
    repeat (4) @(posedge clk);
    done = 1;
  end

  initial begin
    automatic axi_test::axi_ax_beat #(.AW(AW), .IW(IW), .UW(UW)) ax_beat;
    automatic axi_test::axi_w_beat #(.DW(DW), .UW(UW)) w_beat;
    automatic axi_test::axi_b_beat #(.IW(IW), .UW(UW)) b_beat = new;
    axi_drv.reset_slave();
    @(posedge clk);
    axi_drv.recv_aw(ax_beat);
    $info("AXI AW: addr %h", ax_beat.ax_addr);
    axi_drv.recv_w(w_beat);
    $info("AXI W: data %h, strb %h", w_beat.w_data, w_beat.w_strb);
    axi_drv.send_b(b_beat);
  end

endmodule
