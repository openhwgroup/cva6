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

`include "axi/assign.svh"

module tb_axi_to_axi_lite;

  parameter AW = 32;
  parameter DW = 32;
  parameter IW = 8;
  parameter UW = 8;

  localparam tCK = 1ns;
  localparam TA = tCK * 1/4;
  localparam TT = tCK * 3/4;

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

  `AXI_LITE_ASSIGN(axi_lite_dv, axi_lite);

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

  `AXI_ASSIGN(axi, axi_dv);

  axi_to_axi_lite i_dut (
    .clk_i      ( clk      ),
    .rst_ni     ( rst      ),
    .testmode_i ( 1'b0     ),
    .in         ( axi      ),
    .out        ( axi_lite )
  );

  typedef axi_test::axi_lite_driver #(.AW(AW), .DW(DW), .TA(TA), .TT(TT)) axi_lite_drv_t;
  typedef axi_test::axi_driver #(.AW(AW), .DW(DW), .IW(IW), .UW(UW), .TA(TA), .TT(TT)) axi_drv_t;
  axi_lite_drv_t axi_lite_drv = new(axi_lite_dv);
  axi_drv_t axi_drv = new(axi_dv);

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
    automatic axi_drv_t::ax_beat_t ax = new;
    automatic axi_drv_t::w_beat_t w = new;
    automatic axi_drv_t::b_beat_t b = new;
    automatic axi_drv_t::r_beat_t r = new;
    axi_drv.reset_master();
    @(posedge clk);

    ax.randomize();
    w.randomize();
    w.last = 1'b1;
    axi_drv.send_aw(ax);
    axi_drv.send_w(w);
    axi_drv.recv_b(b);

    ax.randomize();
    axi_drv.send_ar(ax);
    axi_drv.recv_r(r);

    repeat (4) @(posedge clk);
    done = 1;
  end

  initial begin
    automatic logic [AW-1:0] addr;
    automatic logic [DW-1:0] data;
    automatic logic [DW/8-1:0] strb;

    axi_lite_drv.reset_slave();
    @(posedge clk);

    axi_lite_drv.recv_aw(addr);
    axi_lite_drv.recv_w(data, strb);
    axi_lite_drv.send_b(axi_pkg::RESP_OKAY);

    axi_lite_drv.recv_ar(addr);
    axi_lite_drv.send_r('0, axi_pkg::RESP_OKAY);
  end

endmodule
