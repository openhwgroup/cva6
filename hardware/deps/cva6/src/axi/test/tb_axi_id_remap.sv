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
// Author: Florian Zaruba <zarubaf@iis.ee.ethz.ch>

`include "axi/assign.svh"

module tb_axi_id_remap;

  parameter AW = 32;
  parameter DW = 32;
  parameter IW = 8;
  parameter UW = 8;
  parameter IWO = 4;
  parameter TS = 4;

  localparam tCK = 1ns;

  logic clk = 0;
  logic rst = 1;
  logic done = 0;

  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH(AW),
    .AXI_DATA_WIDTH(DW),
    .AXI_ID_WIDTH(IWO),
    .AXI_USER_WIDTH(UW)
  ) axi_slave_dv(clk);

  AXI_BUS #(
    .AXI_ADDR_WIDTH(AW),
    .AXI_DATA_WIDTH(DW),
    .AXI_ID_WIDTH(IWO),
    .AXI_USER_WIDTH(UW)
  ) axi_slave();

  `AXI_ASSIGN(axi_slave_dv, axi_slave);

  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH(AW),
    .AXI_DATA_WIDTH(DW),
    .AXI_ID_WIDTH(IW),
    .AXI_USER_WIDTH(UW)
  ) axi_master_dv(clk);

  AXI_BUS #(
    .AXI_ADDR_WIDTH(AW),
    .AXI_DATA_WIDTH(DW),
    .AXI_ID_WIDTH(IW),
    .AXI_USER_WIDTH(UW)
  ) axi_master();

  `AXI_ASSIGN(axi_master, axi_master_dv);

  axi_id_remap #(
    .ADDR_WIDTH     (AW),
    .DATA_WIDTH     (DW),
    .USER_WIDTH     (UW),
    .ID_WIDTH_IN    (IW),
    .ID_WIDTH_OUT   (IWO),
    .TABLE_SIZE     (TS)
  ) i_dut (
    .clk_i  ( clk        ),
    .rst_ni ( rst        ),
    .in     ( axi_master ),
    .out    ( axi_slave  )
  );

  axi_test::axi_driver #(.AW(AW), .DW(DW), .IW(IWO), .UW(UW), .TA(200ps), .TT(700ps)) axi_slave_drv = new(axi_slave_dv);
  axi_test::axi_driver #(.AW(AW), .DW(DW), .IW(IW), .UW(UW), .TA(200ps), .TT(700ps)) axi_master_drv = new(axi_master_dv);

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
    automatic axi_test::axi_ax_beat #(.AW(AW), .IW(IW), .UW(UW)) ax_beat = new;
    automatic axi_test::axi_w_beat #(.DW(DW), .UW(UW)) w_beat = new;
    automatic axi_test::axi_b_beat  #(.IW(IW), .UW(UW)) b_beat;
    axi_master_drv.reset_master();
    @(posedge clk);
    repeat (4) begin
        @(posedge clk);
        void'(randomize(ax_beat));
        axi_master_drv.send_aw(ax_beat);
        w_beat.w_data = 'hcafebabe;
        axi_master_drv.send_w(w_beat);
    end

    repeat (4) axi_master_drv.recv_b(b_beat);

    done = 1;
  end

  initial begin
    automatic axi_test::axi_ax_beat #(.AW(AW), .IW(IWO), .UW(UW)) ax_beat;
    automatic axi_test::axi_w_beat #(.DW(DW), .UW(UW)) w_beat;
    automatic axi_test::axi_b_beat #(.IW(IWO), .UW(UW)) b_beat = new;
    axi_slave_drv.reset_slave();
    @(posedge clk);
    repeat (4) begin
        axi_slave_drv.recv_aw(ax_beat);
        $info("AXI AW: addr %h", ax_beat.ax_addr);
        axi_slave_drv.recv_w(w_beat);
        $info("AXI W: data %h, strb %h", w_beat.w_data, w_beat.w_strb);
    end
    b_beat.b_id = 2;
    axi_slave_drv.send_b(b_beat);
    b_beat.b_id = 0;
    axi_slave_drv.send_b(b_beat);
    b_beat.b_id = 1;
    axi_slave_drv.send_b(b_beat);
    b_beat.b_id = 3;
    axi_slave_drv.send_b(b_beat);
  end
// vsim -voptargs=+acc work.tb_axi_id_remap
endmodule
