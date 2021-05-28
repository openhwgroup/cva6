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

module tb_axi_delayer;

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
  ) axi_slave(clk);

  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH(AW),
    .AXI_DATA_WIDTH(DW),
    .AXI_ID_WIDTH(IW),
    .AXI_USER_WIDTH(UW)
  ) axi_master(clk);

  axi_pkg::aw_chan_t aw_chan_i;
  axi_pkg::w_chan_t  w_chan_i;
  axi_pkg::b_chan_t  b_chan_o;
  axi_pkg::ar_chan_t ar_chan_i;
  axi_pkg::r_chan_t  r_chan_o;

  axi_pkg::aw_chan_t aw_chan_o;
  axi_pkg::w_chan_t  w_chan_o;
  axi_pkg::b_chan_t  b_chan_i;
  axi_pkg::ar_chan_t ar_chan_o;
  axi_pkg::r_chan_t  r_chan_i;

  axi_delayer #(
    .aw_t ( axi_pkg::aw_chan_t ),
    .w_t  ( axi_pkg::w_chan_t  ),
    .b_t  ( axi_pkg::b_chan_t  ),
    .ar_t ( axi_pkg::ar_chan_t ),
    .r_t  ( axi_pkg::r_chan_t  ),
    .FixedDelayInput  ( 0 ),
    .StallRandomInput ( 1 )
  ) i_axi_delayer (
    .clk_i      ( clk                 ),
    .rst_ni     ( rst                 ),
    .aw_valid_i ( axi_master.aw_valid ),
    .aw_chan_i  ( aw_chan_i           ),
    .aw_ready_o ( axi_master.aw_ready ),
    .w_valid_i  ( axi_master.w_valid  ),
    .w_chan_i   ( w_chan_i            ),
    .w_ready_o  ( axi_master.w_ready  ),
    .b_valid_o  ( axi_master.b_valid  ),
    .b_chan_o   ( b_chan_o            ),
    .b_ready_i  ( axi_master.b_ready  ),
    .ar_valid_i ( axi_master.ar_valid ),
    .ar_chan_i  ( ar_chan_i           ),
    .ar_ready_o ( axi_master.ar_ready ),
    .r_valid_o  ( axi_master.r_valid  ),
    .r_chan_o   ( r_chan_o            ),
    .r_ready_i  ( axi_master.r_ready  ),
    .aw_valid_o ( axi_slave.aw_valid  ),
    .aw_chan_o  ( aw_chan_o           ),
    .aw_ready_i ( axi_slave.aw_ready  ),
    .w_valid_o  ( axi_slave.w_valid   ),
    .w_chan_o   ( w_chan_o            ),
    .w_ready_i  ( axi_slave.w_ready   ),
    .b_valid_i  ( axi_slave.b_valid   ),
    .b_chan_i   ( b_chan_i            ),
    .b_ready_o  ( axi_slave.b_ready   ),
    .ar_valid_o ( axi_slave.ar_valid  ),
    .ar_chan_o  ( ar_chan_o           ),
    .ar_ready_i ( axi_slave.ar_ready  ),
    .r_valid_i  ( axi_slave.r_valid   ),
    .r_chan_i   ( r_chan_i            ),
    .r_ready_o  ( axi_slave.r_ready   )
  );

  assign aw_chan_i.id = axi_master.aw_id;
  assign aw_chan_i.addr = axi_master.aw_addr;
  assign aw_chan_i.len = axi_master.aw_len;
  assign aw_chan_i.size = axi_master.aw_size;
  assign aw_chan_i.burst = axi_master.aw_burst;
  assign aw_chan_i.lock = axi_master.aw_lock;
  assign aw_chan_i.cache = axi_master.aw_cache;
  assign aw_chan_i.prot = axi_master.aw_prot;
  assign aw_chan_i.qos = axi_master.aw_qos;
  assign aw_chan_i.region = axi_master.aw_region;
  assign aw_chan_i.atop = axi_master.aw_atop;

  assign ar_chan_i.id = axi_master.ar_id;
  assign ar_chan_i.addr = axi_master.ar_addr;
  assign ar_chan_i.len = axi_master.ar_len;
  assign ar_chan_i.size = axi_master.ar_size;
  assign ar_chan_i.burst = axi_master.ar_burst;
  assign ar_chan_i.lock = axi_master.ar_lock;
  assign ar_chan_i.cache = axi_master.ar_cache;
  assign ar_chan_i.prot = axi_master.ar_prot;
  assign ar_chan_i.qos = axi_master.ar_qos;
  assign ar_chan_i.region = axi_master.ar_region;

  assign w_chan_i.data = axi_master.w_data;
  assign w_chan_i.strb = axi_master.w_strb;
  assign w_chan_i.last = axi_master.w_last;

  assign axi_master.r_id = r_chan_o.id;
  assign axi_master.r_data = r_chan_o.data;
  assign axi_master.r_resp = r_chan_o.resp;
  assign axi_master.r_last = r_chan_o.last;

  assign axi_master.b_id = b_chan_o.id;
  assign axi_master.b_resp = b_chan_o.resp;


  assign axi_slave.aw_id = aw_chan_o.id;
  assign axi_slave.aw_addr = aw_chan_o.addr;
  assign axi_slave.aw_len = aw_chan_o.len;
  assign axi_slave.aw_size = aw_chan_o.size;
  assign axi_slave.aw_burst = aw_chan_o.burst;
  assign axi_slave.aw_lock = aw_chan_o.lock;
  assign axi_slave.aw_cache = aw_chan_o.cache;
  assign axi_slave.aw_prot = aw_chan_o.prot;
  assign axi_slave.aw_qos = aw_chan_o.qos;
  assign axi_slave.aw_region = aw_chan_o.region;
  assign axi_slave.aw_atop = aw_chan_o.atop;

  assign axi_slave.ar_id = ar_chan_o.id;
  assign axi_slave.ar_addr = ar_chan_o.addr;
  assign axi_slave.ar_len = ar_chan_o.len;
  assign axi_slave.ar_size = ar_chan_o.size;
  assign axi_slave.ar_burst = ar_chan_o.burst;
  assign axi_slave.ar_lock = ar_chan_o.lock;
  assign axi_slave.ar_cache = ar_chan_o.cache;
  assign axi_slave.ar_prot = ar_chan_o.prot;
  assign axi_slave.ar_qos = ar_chan_o.qos;
  assign axi_slave.ar_region = ar_chan_o.region;

  assign axi_slave.w_data = w_chan_o.data;
  assign axi_slave.w_strb = w_chan_o.strb;
  assign axi_slave.w_last = w_chan_o.last;

  assign r_chan_i.id = axi_slave.r_id;
  assign r_chan_i.data = axi_slave.r_data;
  assign r_chan_i.resp = axi_slave.r_resp;
  assign r_chan_i.last = axi_slave.r_last;

  assign b_chan_i.id = axi_slave.b_id;
  assign b_chan_i.resp = axi_slave.b_resp;


  axi_test::axi_driver #(.AW(AW), .DW(DW), .IW(IWO), .UW(UW), .TA(200ps), .TT(700ps)) axi_slave_drv = new(axi_slave);
  axi_test::axi_driver #(.AW(AW), .DW(DW), .IW(IW), .UW(UW), .TA(200ps), .TT(700ps)) axi_master_drv = new(axi_master);

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
    repeat (200) begin
        @(posedge clk);
        void'(randomize(ax_beat));
        axi_master_drv.send_aw(ax_beat);
        w_beat.w_data = 'hcafebabe;
        axi_master_drv.send_w(w_beat);
    end

    repeat (200) axi_master_drv.recv_b(b_beat);

    done = 1;
  end

  initial begin
    automatic axi_test::axi_ax_beat #(.AW(AW), .IW(IWO), .UW(UW)) ax_beat;
    automatic axi_test::axi_w_beat #(.DW(DW), .UW(UW)) w_beat;
    automatic axi_test::axi_b_beat #(.IW(IWO), .UW(UW)) b_beat = new;
    automatic int b_id_queue[$];
    axi_slave_drv.reset_slave();
    @(posedge clk);
    repeat (200) begin
        axi_slave_drv.recv_aw(ax_beat);
        $info("AXI AW: addr %h", ax_beat.ax_addr);
        axi_slave_drv.recv_w(w_beat);
        $info("AXI W: data %h, strb %h", w_beat.w_data, w_beat.w_strb);
        b_id_queue.push_back(ax_beat.ax_id);
    end
    while (b_id_queue.size() != 0) begin
      b_beat.b_id = b_id_queue.pop_front();
      axi_slave_drv.send_b(b_beat);
    end
  end
// vsim -voptargs=+acc work.tb_axi_delayer
endmodule
