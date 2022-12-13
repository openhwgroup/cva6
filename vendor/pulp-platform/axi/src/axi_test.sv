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
// Authors:
// - Wolfgang Roenninger <wroennin@iis.ee.ethz.ch>
// - Andreas Kurth <akurth@iis.ee.ethz.ch>
// - Fabian Schuiki <fschuiki@iis.ee.ethz.ch>
// - Florian Zaruba <zarubaf@iis.ee.ethz.ch>
// - Matheus Cavalcante <matheusd@iis.ee.ethz.ch>


/// A set of testbench utilities for AXI interfaces.
package axi_test;

  import axi_pkg::*;

  /// A driver for AXI4-Lite interface.
  class axi_lite_driver #(
    parameter int  AW = 32  ,
    parameter int  DW = 32  ,
    parameter time TA = 0ns , // stimuli application time
    parameter time TT = 0ns   // stimuli test time
  );
    virtual AXI_LITE_DV #(
      .AXI_ADDR_WIDTH(AW),
      .AXI_DATA_WIDTH(DW)
    ) axi;

    function new(
      virtual AXI_LITE_DV #(
        .AXI_ADDR_WIDTH(AW),
        .AXI_DATA_WIDTH(DW)
      ) axi
    );
      this.axi = axi;
    endfunction

    function void reset_master();
      axi.aw_addr  <= '0;
      axi.aw_prot  <= '0;
      axi.aw_valid <= '0;
      axi.w_valid  <= '0;
      axi.w_data   <= '0;
      axi.w_strb   <= '0;
      axi.b_ready  <= '0;
      axi.ar_valid <= '0;
      axi.ar_prot  <= '0;
      axi.ar_addr  <= '0;
      axi.r_ready  <= '0;
    endfunction

    function void reset_slave();
      axi.aw_ready <= '0;
      axi.w_ready  <= '0;
      axi.b_resp   <= '0;
      axi.b_valid  <= '0;
      axi.ar_ready <= '0;
      axi.r_data   <= '0;
      axi.r_resp   <= '0;
      axi.r_valid  <= '0;
    endfunction

    task cycle_start;
      #TT;
    endtask

    task cycle_end;
      @(posedge axi.clk_i);
    endtask

    /// Issue a beat on the AW channel.
    task send_aw (
      input logic [AW-1:0] addr,
      input prot_t         prot
    );
      axi.aw_addr  <= #TA addr;
      axi.aw_prot  <= #TA prot;
      axi.aw_valid <= #TA 1;
      cycle_start();
      while (axi.aw_ready != 1) begin cycle_end(); cycle_start(); end
      cycle_end();
      axi.aw_addr  <= #TA '0;
      axi.aw_prot  <= #TA '0;
      axi.aw_valid <= #TA 0;
    endtask

    /// Issue a beat on the W channel.
    task send_w (
      input logic [DW-1:0] data,
      input logic [DW/8-1:0] strb
    );
      axi.w_data  <= #TA data;
      axi.w_strb  <= #TA strb;
      axi.w_valid <= #TA 1;
      cycle_start();
      while (axi.w_ready != 1) begin cycle_end(); cycle_start(); end
      cycle_end();
      axi.w_data  <= #TA '0;
      axi.w_strb  <= #TA '0;
      axi.w_valid <= #TA 0;
    endtask

    /// Issue a beat on the B channel.
    task send_b (
      input axi_pkg::resp_t resp
    );
      axi.b_resp  <= #TA resp;
      axi.b_valid <= #TA 1;
      cycle_start();
      while (axi.b_ready != 1) begin cycle_end(); cycle_start(); end
      cycle_end();
      axi.b_resp  <= #TA '0;
      axi.b_valid <= #TA 0;
    endtask

    /// Issue a beat on the AR channel.
    task send_ar (
      input logic [AW-1:0] addr,
      input prot_t         prot
    );
      axi.ar_addr  <= #TA addr;
      axi.ar_prot  <= #TA prot;
      axi.ar_valid <= #TA 1;
      cycle_start();
      while (axi.ar_ready != 1) begin cycle_end(); cycle_start(); end
      cycle_end();
      axi.ar_addr  <= #TA '0;
      axi.ar_prot  <= #TA '0;
      axi.ar_valid <= #TA 0;
    endtask

    /// Issue a beat on the R channel.
    task send_r (
      input logic [DW-1:0] data,
      input axi_pkg::resp_t resp
    );
      axi.r_data  <= #TA data;
      axi.r_resp  <= #TA resp;
      axi.r_valid <= #TA 1;
      cycle_start();
      while (axi.r_ready != 1) begin cycle_end(); cycle_start(); end
      cycle_end();
      axi.r_data  <= #TA '0;
      axi.r_resp  <= #TA '0;
      axi.r_valid <= #TA 0;
    endtask

    /// Wait for a beat on the AW channel.
    task recv_aw (
      output [AW-1:0] addr,
      output prot_t   prot
    );
      axi.aw_ready <= #TA 1;
      cycle_start();
      while (axi.aw_valid != 1) begin cycle_end(); cycle_start(); end
      addr = axi.aw_addr;
      prot = axi.aw_prot;
      cycle_end();
      axi.aw_ready <= #TA 0;
    endtask

    /// Wait for a beat on the W channel.
    task recv_w (
      output [DW-1:0] data,
      output [DW/8-1:0] strb
    );
      axi.w_ready <= #TA 1;
      cycle_start();
      while (axi.w_valid != 1) begin cycle_end(); cycle_start(); end
      data = axi.w_data;
      strb = axi.w_strb;
      cycle_end();
      axi.w_ready <= #TA 0;
    endtask

    /// Wait for a beat on the B channel.
    task recv_b (
      output axi_pkg::resp_t resp
    );
      axi.b_ready <= #TA 1;
      cycle_start();
      while (axi.b_valid != 1) begin cycle_end(); cycle_start(); end
      resp = axi.b_resp;
      cycle_end();
      axi.b_ready <= #TA 0;
    endtask

    /// Wait for a beat on the AR channel.
    task recv_ar (
      output [AW-1:0] addr,
      output prot_t   prot
    );
      axi.ar_ready <= #TA 1;
      cycle_start();
      while (axi.ar_valid != 1) begin cycle_end(); cycle_start(); end
      addr = axi.ar_addr;
      prot = axi.ar_prot;
      cycle_end();
      axi.ar_ready <= #TA 0;
    endtask

    /// Wait for a beat on the R channel.
    task recv_r (
      output [DW-1:0] data,
      output axi_pkg::resp_t resp
    );
      axi.r_ready <= #TA 1;
      cycle_start();
      while (axi.r_valid != 1) begin cycle_end(); cycle_start(); end
      data = axi.r_data;
      resp = axi.r_resp;
      cycle_end();
      axi.r_ready <= #TA 0;
    endtask

  endclass


  /// The data transferred on a beat on the AW/AR channels.
  class axi_ax_beat #(
    parameter AW = 32,
    parameter IW = 8 ,
    parameter UW = 1
  );
    rand logic [IW-1:0] ax_id     = '0;
    rand logic [AW-1:0] ax_addr   = '0;
    logic [7:0]         ax_len    = '0;
    logic [2:0]         ax_size   = '0;
    logic [1:0]         ax_burst  = '0;
    logic               ax_lock   = '0;
    logic [3:0]         ax_cache  = '0;
    logic [2:0]         ax_prot   = '0;
    rand logic [3:0]    ax_qos    = '0;
    logic [3:0]         ax_region = '0;
    logic [5:0]         ax_atop   = '0; // Only defined on the AW channel.
    rand logic [UW-1:0] ax_user   = '0;
  endclass

  /// The data transferred on a beat on the W channel.
  class axi_w_beat #(
    parameter DW = 32,
    parameter UW = 1
  );
    rand logic [DW-1:0]   w_data = '0;
    rand logic [DW/8-1:0] w_strb = '0;
    logic                 w_last = '0;
    rand logic [UW-1:0]   w_user = '0;
  endclass

  /// The data transferred on a beat on the B channel.
  class axi_b_beat #(
    parameter IW = 8,
    parameter UW = 1
  );
    rand logic [IW-1:0] b_id   = '0;
    axi_pkg::resp_t     b_resp = '0;
    rand logic [UW-1:0] b_user = '0;
  endclass

  /// The data transferred on a beat on the R channel.
  class axi_r_beat #(
    parameter DW = 32,
    parameter IW = 8 ,
    parameter UW = 1
  );
    rand logic [IW-1:0] r_id   = '0;
    rand logic [DW-1:0] r_data = '0;
    axi_pkg::resp_t     r_resp = '0;
    logic               r_last = '0;
    rand logic [UW-1:0] r_user = '0;
  endclass


  /// A driver for AXI4 interface.
  class axi_driver #(
    parameter int  AW = 32  ,
    parameter int  DW = 32  ,
    parameter int  IW = 8   ,
    parameter int  UW = 1   ,
    parameter time TA = 0ns , // stimuli application time
    parameter time TT = 0ns   // stimuli test time
  );
    virtual AXI_BUS_DV #(
      .AXI_ADDR_WIDTH(AW),
      .AXI_DATA_WIDTH(DW),
      .AXI_ID_WIDTH(IW),
      .AXI_USER_WIDTH(UW)
    ) axi;

    typedef axi_ax_beat #(.AW(AW), .IW(IW), .UW(UW)) ax_beat_t;
    typedef axi_w_beat  #(.DW(DW), .UW(UW))          w_beat_t;
    typedef axi_b_beat  #(.IW(IW), .UW(UW))          b_beat_t;
    typedef axi_r_beat  #(.DW(DW), .IW(IW), .UW(UW)) r_beat_t;

    function new(
      virtual AXI_BUS_DV #(
        .AXI_ADDR_WIDTH(AW),
        .AXI_DATA_WIDTH(DW),
        .AXI_ID_WIDTH(IW),
        .AXI_USER_WIDTH(UW)
      ) axi
    );
      this.axi = axi;
    endfunction

    function void reset_master();
      axi.aw_id     <= '0;
      axi.aw_addr   <= '0;
      axi.aw_len    <= '0;
      axi.aw_size   <= '0;
      axi.aw_burst  <= '0;
      axi.aw_lock   <= '0;
      axi.aw_cache  <= '0;
      axi.aw_prot   <= '0;
      axi.aw_qos    <= '0;
      axi.aw_region <= '0;
      axi.aw_atop   <= '0;
      axi.aw_user   <= '0;
      axi.aw_valid  <= '0;
      axi.w_data    <= '0;
      axi.w_strb    <= '0;
      axi.w_last    <= '0;
      axi.w_user    <= '0;
      axi.w_valid   <= '0;
      axi.b_ready   <= '0;
      axi.ar_id     <= '0;
      axi.ar_addr   <= '0;
      axi.ar_len    <= '0;
      axi.ar_size   <= '0;
      axi.ar_burst  <= '0;
      axi.ar_lock   <= '0;
      axi.ar_cache  <= '0;
      axi.ar_prot   <= '0;
      axi.ar_qos    <= '0;
      axi.ar_region <= '0;
      axi.ar_user   <= '0;
      axi.ar_valid  <= '0;
      axi.r_ready   <= '0;
    endfunction

    function void reset_slave();
      axi.aw_ready  <= '0;
      axi.w_ready   <= '0;
      axi.b_id      <= '0;
      axi.b_resp    <= '0;
      axi.b_user    <= '0;
      axi.b_valid   <= '0;
      axi.ar_ready  <= '0;
      axi.r_id      <= '0;
      axi.r_data    <= '0;
      axi.r_resp    <= '0;
      axi.r_last    <= '0;
      axi.r_user    <= '0;
      axi.r_valid   <= '0;
    endfunction

    task cycle_start;
      #TT;
    endtask

    task cycle_end;
      @(posedge axi.clk_i);
    endtask

    /// Issue a beat on the AW channel.
    task send_aw (
      input ax_beat_t beat
    );
      axi.aw_id     <= #TA beat.ax_id;
      axi.aw_addr   <= #TA beat.ax_addr;
      axi.aw_len    <= #TA beat.ax_len;
      axi.aw_size   <= #TA beat.ax_size;
      axi.aw_burst  <= #TA beat.ax_burst;
      axi.aw_lock   <= #TA beat.ax_lock;
      axi.aw_cache  <= #TA beat.ax_cache;
      axi.aw_prot   <= #TA beat.ax_prot;
      axi.aw_qos    <= #TA beat.ax_qos;
      axi.aw_region <= #TA beat.ax_region;
      axi.aw_atop   <= #TA beat.ax_atop;
      axi.aw_user   <= #TA beat.ax_user;
      axi.aw_valid  <= #TA 1;
      cycle_start();
      while (axi.aw_ready != 1) begin cycle_end(); cycle_start(); end
      cycle_end();
      axi.aw_id     <= #TA '0;
      axi.aw_addr   <= #TA '0;
      axi.aw_len    <= #TA '0;
      axi.aw_size   <= #TA '0;
      axi.aw_burst  <= #TA '0;
      axi.aw_lock   <= #TA '0;
      axi.aw_cache  <= #TA '0;
      axi.aw_prot   <= #TA '0;
      axi.aw_qos    <= #TA '0;
      axi.aw_region <= #TA '0;
      axi.aw_atop   <= #TA '0;
      axi.aw_user   <= #TA '0;
      axi.aw_valid  <= #TA 0;
    endtask

    /// Issue a beat on the W channel.
    task send_w (
      input w_beat_t beat
    );
      axi.w_data  <= #TA beat.w_data;
      axi.w_strb  <= #TA beat.w_strb;
      axi.w_last  <= #TA beat.w_last;
      axi.w_user  <= #TA beat.w_user;
      axi.w_valid <= #TA 1;
      cycle_start();
      while (axi.w_ready != 1) begin cycle_end(); cycle_start(); end
      cycle_end();
      axi.w_data  <= #TA '0;
      axi.w_strb  <= #TA '0;
      axi.w_last  <= #TA '0;
      axi.w_user  <= #TA '0;
      axi.w_valid <= #TA 0;
    endtask

    /// Issue a beat on the B channel.
    task send_b (
      input b_beat_t beat
    );
      axi.b_id    <= #TA beat.b_id;
      axi.b_resp  <= #TA beat.b_resp;
      axi.b_user  <= #TA beat.b_user;
      axi.b_valid <= #TA 1;
      cycle_start();
      while (axi.b_ready != 1) begin cycle_end(); cycle_start(); end
      cycle_end();
      axi.b_id    <= #TA '0;
      axi.b_resp  <= #TA '0;
      axi.b_user  <= #TA '0;
      axi.b_valid <= #TA 0;
    endtask

    /// Issue a beat on the AR channel.
    task send_ar (
      input ax_beat_t beat
    );
      axi.ar_id     <= #TA beat.ax_id;
      axi.ar_addr   <= #TA beat.ax_addr;
      axi.ar_len    <= #TA beat.ax_len;
      axi.ar_size   <= #TA beat.ax_size;
      axi.ar_burst  <= #TA beat.ax_burst;
      axi.ar_lock   <= #TA beat.ax_lock;
      axi.ar_cache  <= #TA beat.ax_cache;
      axi.ar_prot   <= #TA beat.ax_prot;
      axi.ar_qos    <= #TA beat.ax_qos;
      axi.ar_region <= #TA beat.ax_region;
      axi.ar_user   <= #TA beat.ax_user;
      axi.ar_valid  <= #TA 1;
      cycle_start();
      while (axi.ar_ready != 1) begin cycle_end(); cycle_start(); end
      cycle_end();
      axi.ar_id     <= #TA '0;
      axi.ar_addr   <= #TA '0;
      axi.ar_len    <= #TA '0;
      axi.ar_size   <= #TA '0;
      axi.ar_burst  <= #TA '0;
      axi.ar_lock   <= #TA '0;
      axi.ar_cache  <= #TA '0;
      axi.ar_prot   <= #TA '0;
      axi.ar_qos    <= #TA '0;
      axi.ar_region <= #TA '0;
      axi.ar_user   <= #TA '0;
      axi.ar_valid  <= #TA 0;
    endtask

    /// Issue a beat on the R channel.
    task send_r (
      input r_beat_t beat
    );
      axi.r_id    <= #TA beat.r_id;
      axi.r_data  <= #TA beat.r_data;
      axi.r_resp  <= #TA beat.r_resp;
      axi.r_last  <= #TA beat.r_last;
      axi.r_user  <= #TA beat.r_user;
      axi.r_valid <= #TA 1;
      cycle_start();
      while (axi.r_ready != 1) begin cycle_end(); cycle_start(); end
      cycle_end();
      axi.r_id    <= #TA '0;
      axi.r_data  <= #TA '0;
      axi.r_resp  <= #TA '0;
      axi.r_last  <= #TA '0;
      axi.r_user  <= #TA '0;
      axi.r_valid <= #TA 0;
    endtask

    /// Wait for a beat on the AW channel.
    task recv_aw (
      output ax_beat_t beat
    );
      axi.aw_ready <= #TA 1;
      cycle_start();
      while (axi.aw_valid != 1) begin cycle_end(); cycle_start(); end
      beat = new;
      beat.ax_id     = axi.aw_id;
      beat.ax_addr   = axi.aw_addr;
      beat.ax_len    = axi.aw_len;
      beat.ax_size   = axi.aw_size;
      beat.ax_burst  = axi.aw_burst;
      beat.ax_lock   = axi.aw_lock;
      beat.ax_cache  = axi.aw_cache;
      beat.ax_prot   = axi.aw_prot;
      beat.ax_qos    = axi.aw_qos;
      beat.ax_region = axi.aw_region;
      beat.ax_atop   = axi.aw_atop;
      beat.ax_user   = axi.aw_user;
      cycle_end();
      axi.aw_ready <= #TA 0;
    endtask

    /// Wait for a beat on the W channel.
    task recv_w (
      output w_beat_t beat
    );
      axi.w_ready <= #TA 1;
      cycle_start();
      while (axi.w_valid != 1) begin cycle_end(); cycle_start(); end
      beat = new;
      beat.w_data = axi.w_data;
      beat.w_strb = axi.w_strb;
      beat.w_last = axi.w_last;
      beat.w_user = axi.w_user;
      cycle_end();
      axi.w_ready <= #TA 0;
    endtask

    /// Wait for a beat on the B channel.
    task recv_b (
      output b_beat_t beat
    );
      axi.b_ready <= #TA 1;
      cycle_start();
      while (axi.b_valid != 1) begin cycle_end(); cycle_start(); end
      beat = new;
      beat.b_id   = axi.b_id;
      beat.b_resp = axi.b_resp;
      beat.b_user = axi.b_user;
      cycle_end();
      axi.b_ready <= #TA 0;
    endtask

    /// Wait for a beat on the AR channel.
    task recv_ar (
      output ax_beat_t beat
    );
      axi.ar_ready  <= #TA 1;
      cycle_start();
      while (axi.ar_valid != 1) begin cycle_end(); cycle_start(); end
      beat = new;
      beat.ax_id     = axi.ar_id;
      beat.ax_addr   = axi.ar_addr;
      beat.ax_len    = axi.ar_len;
      beat.ax_size   = axi.ar_size;
      beat.ax_burst  = axi.ar_burst;
      beat.ax_lock   = axi.ar_lock;
      beat.ax_cache  = axi.ar_cache;
      beat.ax_prot   = axi.ar_prot;
      beat.ax_qos    = axi.ar_qos;
      beat.ax_region = axi.ar_region;
      beat.ax_atop   = 'X;  // Not defined on the AR channel.
      beat.ax_user   = axi.ar_user;
      cycle_end();
      axi.ar_ready  <= #TA 0;
    endtask

    /// Wait for a beat on the R channel.
    task recv_r (
      output r_beat_t beat
    );
      axi.r_ready <= #TA 1;
      cycle_start();
      while (axi.r_valid != 1) begin cycle_end(); cycle_start(); end
      beat = new;
      beat.r_id   = axi.r_id;
      beat.r_data = axi.r_data;
      beat.r_resp = axi.r_resp;
      beat.r_last = axi.r_last;
      beat.r_user = axi.r_user;
      cycle_end();
      axi.r_ready <= #TA 0;
    endtask

  endclass

  class axi_rand_master #(
    // AXI interface parameters
    parameter int   AW = 32,
    parameter int   DW = 32,
    parameter int   IW = 8,
    parameter int   UW = 1,
    // Stimuli application and test time
    parameter time  TA = 0ps,
    parameter time  TT = 0ps,
    // Maximum number of read and write transactions in flight
    parameter int   MAX_READ_TXNS = 1,
    parameter int   MAX_WRITE_TXNS = 1,
    // Upper and lower bounds on wait cycles on Ax, W, and resp (R and B) channels
    parameter int   AX_MIN_WAIT_CYCLES = 0,
    parameter int   AX_MAX_WAIT_CYCLES = 100,
    parameter int   W_MIN_WAIT_CYCLES = 0,
    parameter int   W_MAX_WAIT_CYCLES = 5,
    parameter int   RESP_MIN_WAIT_CYCLES = 0,
    parameter int   RESP_MAX_WAIT_CYCLES = 20,
    // AXI feature usage
    parameter int   AXI_MAX_BURST_LEN = 0, // maximum number of beats in burst; 0 = AXI max (256)
    parameter int   TRAFFIC_SHAPING   = 0,
    parameter bit   AXI_EXCLS         = 1'b0,
    parameter bit   AXI_ATOPS         = 1'b0,
    parameter bit   AXI_BURST_FIXED   = 1'b1,
    parameter bit   AXI_BURST_INCR    = 1'b1,
    parameter bit   AXI_BURST_WRAP    = 1'b0,
    parameter bit   UNIQUE_IDS        = 1'b0, // guarantee that the ID of each transaction is
                                              // unique among all in-flight transactions in the
                                              // same direction
    // Dependent parameters, do not override.
    parameter int   AXI_STRB_WIDTH = DW/8,
    parameter int   N_AXI_IDS = 2**IW
  );
    typedef axi_test::axi_driver #(
      .AW(AW), .DW(DW), .IW(IW), .UW(UW), .TA(TA), .TT(TT)
    ) axi_driver_t;
    typedef logic [AW-1:0]      addr_t;
    typedef axi_pkg::burst_t    burst_t;
    typedef axi_pkg::cache_t    cache_t;
    typedef logic [DW-1:0]      data_t;
    typedef logic [IW-1:0]      id_t;
    typedef axi_pkg::len_t      len_t;
    typedef axi_pkg::size_t     size_t;
    typedef logic [UW-1:0]      user_t;
    typedef axi_pkg::mem_type_t mem_type_t;

    typedef axi_driver_t::ax_beat_t ax_beat_t;
    typedef axi_driver_t::b_beat_t  b_beat_t;
    typedef axi_driver_t::r_beat_t  r_beat_t;
    typedef axi_driver_t::w_beat_t  w_beat_t;

    static addr_t PFN_MASK = '{11: 1'b0, 10: 1'b0, 9: 1'b0, 8: 1'b0, 7: 1'b0, 6: 1'b0, 5: 1'b0,
        4: 1'b0, 3: 1'b0, 2: 1'b0, 1: 1'b0, 0: 1'b0, default: '1};

    axi_driver_t drv;

    int unsigned          r_flight_cnt[N_AXI_IDS-1:0],
                          w_flight_cnt[N_AXI_IDS-1:0],
                          tot_r_flight_cnt,
                          tot_w_flight_cnt;
    logic [N_AXI_IDS-1:0] atop_resp_b,
                          atop_resp_r;

    len_t                 max_len;
    burst_t               allowed_bursts[$];

    semaphore cnt_sem;

    ax_beat_t aw_queue[$],
              w_queue[$],
              excl_queue[$];

    typedef struct packed {
      addr_t     addr_begin;
      addr_t     addr_end;
      mem_type_t mem_type;
    } mem_region_t;
    mem_region_t mem_map[$];

    struct packed {
      int unsigned len  ;
      int unsigned cprob;
    } traffic_shape[$];
    int unsigned max_cprob;

    function new(
      virtual AXI_BUS_DV #(
        .AXI_ADDR_WIDTH(AW),
        .AXI_DATA_WIDTH(DW),
        .AXI_ID_WIDTH(IW),
        .AXI_USER_WIDTH(UW)
      ) axi
    );
      if (AXI_MAX_BURST_LEN <= 0 || AXI_MAX_BURST_LEN > 256) begin
        this.max_len = 255;
      end else begin
        this.max_len = AXI_MAX_BURST_LEN - 1;
      end
      this.drv = new(axi);
      this.cnt_sem = new(1);
      this.reset();
      if (AXI_BURST_FIXED) begin
        this.allowed_bursts.push_back(BURST_FIXED);
      end
      if (AXI_BURST_INCR) begin
        this.allowed_bursts.push_back(BURST_INCR);
      end
      if (AXI_BURST_WRAP) begin
        this.allowed_bursts.push_back(BURST_WRAP);
      end
      assert(allowed_bursts.size()) else $fatal(1, "At least one burst type has to be specified!");
    endfunction

    function void reset();
      drv.reset_master();
      r_flight_cnt = '{default: 0};
      w_flight_cnt = '{default: 0};
      tot_r_flight_cnt = 0;
      tot_w_flight_cnt = 0;
      atop_resp_b = '0;
      atop_resp_r = '0;
    endfunction

    function void add_memory_region(input addr_t addr_begin, input addr_t addr_end, input mem_type_t mem_type);
      mem_map.push_back({addr_begin, addr_end, mem_type});
    endfunction

    function void add_traffic_shaping(input int unsigned len, input int unsigned freq);
      if (traffic_shape.size() == 0)
        traffic_shape.push_back({len, freq});
      else
        traffic_shape.push_back({len, traffic_shape[$].cprob + freq});

      max_cprob = traffic_shape[$].cprob;
    endfunction : add_traffic_shaping

    function ax_beat_t new_rand_burst(input logic is_read);
      automatic logic rand_success;
      automatic ax_beat_t ax_beat = new;
      automatic addr_t addr;
      automatic burst_t burst;
      automatic cache_t cache;
      automatic id_t id;
      automatic qos_t qos;
      automatic len_t len;
      automatic size_t size;
      automatic int unsigned mem_region_idx;
      automatic mem_region_t mem_region;
      automatic int cprob;

      // No memory regions defined
      if (mem_map.size() == 0) begin
        // Return a dummy region
        mem_region = '{
          addr_begin: '0,
          addr_end:   '1,
          mem_type:   axi_pkg::NORMAL_NONCACHEABLE_BUFFERABLE
        };
      end else begin
        // Randomly pick a memory region
        rand_success = std::randomize(mem_region_idx) with {
          mem_region_idx < mem_map.size();
        }; assert(rand_success);
        mem_region = mem_map[mem_region_idx];
      end

      // Randomly pick burst type.
      rand_success = std::randomize(burst) with {
        burst inside {this.allowed_bursts};
      }; assert(rand_success);
      ax_beat.ax_burst = burst;
      // Determine memory type.
      ax_beat.ax_cache = is_read ? axi_pkg::get_arcache(mem_region.mem_type) : axi_pkg::get_awcache(mem_region.mem_type);
      // Randomize beat size.
      if (TRAFFIC_SHAPING) begin
        rand_success = std::randomize(cprob) with {
          cprob >= 0; cprob < max_cprob;
        }; assert(rand_success);

        for (int i = 0; i < traffic_shape.size(); i++)
          if (traffic_shape[i].cprob > cprob) begin
            len = traffic_shape[i].len;
            assert (ax_beat.ax_burst == BURST_WRAP -> len inside {len_t'(1), len_t'(3), len_t'(7), len_t'(15)});
            break;
          end

        // Randomize address.  Make sure that the burst does not cross a 4KiB boundary.
        forever begin
          rand_success = std::randomize(size) with {
            2**size <= AXI_STRB_WIDTH;
            2**size <= len;
          }; assert(rand_success);
          ax_beat.ax_size = size;
          ax_beat.ax_len = ((len + (1 << size) - 1) >> size) - 1;

          rand_success = std::randomize(addr) with {
            addr >= mem_region.addr_begin;
            addr <= mem_region.addr_end;
            addr + len <= mem_region.addr_end;
          }; assert(rand_success);

          if (ax_beat.ax_burst == axi_pkg::BURST_FIXED) begin
            if (((addr + 2**ax_beat.ax_size) & PFN_MASK) == (addr & PFN_MASK)) begin
              break;
            end
          end else begin // BURST_INCR
            if (((addr + 2**ax_beat.ax_size * (ax_beat.ax_len + 1)) & PFN_MASK) == (addr & PFN_MASK)) begin
              break;
            end
          end
        end
      end else begin
        // Randomize address.  Make sure that the burst does not cross a 4KiB boundary.
        forever begin
          // Randomize burst length.
          rand_success = std::randomize(len) with {
            len <= this.max_len;
            (ax_beat.ax_burst == BURST_WRAP) ->
                len inside {len_t'(1), len_t'(3), len_t'(7), len_t'(15)};
          }; assert(rand_success);
          rand_success = std::randomize(size) with {
            2**size <= AXI_STRB_WIDTH;
          }; assert(rand_success);
          ax_beat.ax_size = size;
          ax_beat.ax_len = len;

          // Randomize address
          rand_success = std::randomize(addr) with {
            addr >= mem_region.addr_begin;
            addr <= mem_region.addr_end;
            addr + ((len + 1) << size) <= mem_region.addr_end;
          }; assert(rand_success);

          if (ax_beat.ax_burst == axi_pkg::BURST_FIXED) begin
            if (((addr + 2**ax_beat.ax_size) & PFN_MASK) == (addr & PFN_MASK)) begin
              break;
            end
          end else begin // BURST_INCR, BURST_WRAP
            if (((addr + 2**ax_beat.ax_size * (ax_beat.ax_len + 1)) & PFN_MASK) == (addr & PFN_MASK)) begin
              break;
            end
          end
        end
      end

      ax_beat.ax_addr = addr;
      rand_success = std::randomize(id); assert(rand_success);
      rand_success = std::randomize(qos); assert(rand_success);
      // The random ID *must* be legalized with `legalize_id()` before the beat is sent!  This is
      // currently done in the functions `create_aws()` and `send_ars()`.
      ax_beat.ax_id = id;
      ax_beat.ax_qos = qos;
      return ax_beat;
    endfunction

    task rand_atop_burst(inout ax_beat_t beat);
      automatic logic rand_success;
      beat.ax_atop[5:4] = $random();
      if (beat.ax_atop[5:4] != 2'b00 && !AXI_BURST_INCR) begin
        // We can emit ATOPs only if INCR bursts are allowed.
        $warning("ATOP suppressed because INCR bursts are disabled!");
        beat.ax_atop[5:4] = 2'b00;
      end
      if (beat.ax_atop[5:4] != 2'b00) begin // ATOP
        // Determine `ax_atop`.
        if (beat.ax_atop[5:4] == axi_pkg::ATOP_ATOMICSTORE ||
            beat.ax_atop[5:4] == axi_pkg::ATOP_ATOMICLOAD) begin
          // Endianness
          beat.ax_atop[3] = $random();
          // Atomic operation
          beat.ax_atop[2:0] = $random();
        end else begin // Atomic{Swap,Compare}
          beat.ax_atop[3:1] = '0;
          beat.ax_atop[0] = $random();
        end
        // Determine `ax_size` and `ax_len`.
        if (2**beat.ax_size < AXI_STRB_WIDTH) begin
          // Transaction does *not* occupy full data bus, so we must send just one beat. [E2.1.3]
          beat.ax_len = '0;
        end else begin
          automatic int unsigned bytes;
          if (beat.ax_atop == axi_pkg::ATOP_ATOMICCMP) begin
            // Total data transferred in burst can be 2, 4, 8, 16, or 32 B.
            automatic int unsigned log_bytes;
            rand_success = std::randomize(log_bytes) with {
              log_bytes > 0; 2**log_bytes <= 32;
            }; assert(rand_success);
            bytes = 2**log_bytes;
          end else begin
            // Total data transferred in burst can be 1, 2, 4, or 8 B.
            if (AXI_STRB_WIDTH >= 8) begin
              bytes = AXI_STRB_WIDTH;
            end else begin
              automatic int unsigned log_bytes;
              rand_success = std::randomize(log_bytes); assert(rand_success);
              log_bytes = log_bytes % (4 - $clog2(AXI_STRB_WIDTH)) - $clog2(AXI_STRB_WIDTH);
              bytes = 2**log_bytes;
            end
          end
          beat.ax_len = bytes / AXI_STRB_WIDTH - 1;
        end
        // Determine `ax_addr` and `ax_burst`.
        if (beat.ax_atop == axi_pkg::ATOP_ATOMICCMP) begin
          // The address must be aligned to half the outbound data size. [E2-337]
          beat.ax_addr = beat.ax_addr & ~((1'b1 << beat.ax_size) - 1);
          // If the address is aligned to the total size of outgoing data, the burst type must be
          // INCR. Otherwise, it must be WRAP. [E2-338]
          beat.ax_burst = (beat.ax_addr % ((beat.ax_len+1) * 2**beat.ax_size) == 0) ?
              axi_pkg::BURST_INCR : axi_pkg::BURST_WRAP;
          // If we are not allowed to emit WRAP bursts, align the address to the total size of
          // outgoing data and fall back to INCR.
          if (beat.ax_burst == axi_pkg::BURST_WRAP && !AXI_BURST_WRAP) begin
            beat.ax_addr -= (beat.ax_addr % ((beat.ax_len+1) * 2**beat.ax_size));
            beat.ax_burst = axi_pkg::BURST_INCR;
          end
        end else begin
          // The address must be aligned to the data size. [E2-337]
          beat.ax_addr = beat.ax_addr & ~((1'b1 << (beat.ax_size+1)) - 1);
          // Only INCR allowed.
          beat.ax_burst = axi_pkg::BURST_INCR;
        end
      end
    endtask

    function void rand_excl_ar(inout ax_beat_t ar_beat);
      ar_beat.ax_lock = $random();
      if (ar_beat.ax_lock) begin
        automatic logic rand_success;
        automatic int unsigned n_bytes;
        automatic size_t size;
        automatic addr_t addr_mask;
        // In an exclusive burst, the number of bytes to be transferred must be a power of 2, i.e.,
        // 1, 2, 4, 8, 16, 32, 64, or 128 bytes, and the burst length must not exceed 16 transfers.
        static int unsigned ul = (AXI_STRB_WIDTH < 8) ? 4 + $clog2(AXI_STRB_WIDTH) : 7;
        rand_success = std::randomize(n_bytes) with {
          n_bytes >= 1;
          n_bytes <= ul;
        }; assert(rand_success);
        n_bytes = 2**n_bytes;
        rand_success = std::randomize(size) with {
          size >= 0;
          2**size <= n_bytes;
          2**size <= AXI_STRB_WIDTH;
          n_bytes / 2**size <= 16;
        }; assert(rand_success);
        ar_beat.ax_size = size;
        ar_beat.ax_len = n_bytes / 2**size;
        // The address must be aligned to the total number of bytes in the burst.
        ar_beat.ax_addr = ar_beat.ax_addr & ~(n_bytes-1);
      end
    endfunction

    // TODO: The `rand_wait` task exists in `rand_verif_pkg`, but that task cannot be called with
    // `this.drv.axi.clk_i` as `clk` argument. What is the syntax for getting an assignable
    // reference?
    task automatic rand_wait(input int unsigned min, max);
      int unsigned rand_success, cycles;
      rand_success = std::randomize(cycles) with {
        cycles >= min;
        cycles <= max;
      };
      assert (rand_success) else $error("Failed to randomize wait cycles!");
      repeat (cycles) @(posedge this.drv.axi.clk_i);
    endtask

    // Determine if the ID of an AXI Ax beat is currently legal.  This function may only be called
    // while holding the `cnt_sem` semaphore.
    function bit id_is_legal(input bit is_read, input ax_beat_t beat);
      if (AXI_ATOPS) begin
        // The ID must not be the same as that of any in-flight ATOP.
        if (atop_resp_b[beat.ax_id] || atop_resp_r[beat.ax_id]) return 1'b0;
        // If this beat starts an ATOP, its ID must not be the same as that of any other in-flight
        // AXI transaction.
        if (!is_read && beat.ax_atop[5:4] != 2'b00 && (
          r_flight_cnt[beat.ax_id] != 0 || w_flight_cnt[beat.ax_id] !=0
        )) return 1'b0;
      end
      if (UNIQUE_IDS) begin
        // This master may only emit transactions with an ID that is unique among all in-flight
        // transactions in the same direction.
        if (is_read && r_flight_cnt[beat.ax_id] != 0) return 1'b0;
        if (!is_read && w_flight_cnt[beat.ax_id] != 0) return 1'b0;
      end
      // There is no reason why this ID would be illegal, so it is legal.
      return 1'b1;
    endfunction

    // Legalize the ID of an AXI Ax beat (drawing a new ID at random if the existing ID is currently
    // not legal) and add it to the in-flight transactions.
    task legalize_id(input bit is_read, inout ax_beat_t beat);
      automatic logic rand_success;
      automatic id_t id = beat.ax_id;
      // Loop until a legal ID is found.
      forever begin
        // Acquire semaphore on in-flight counters.
        cnt_sem.get();
        // Exit loop if the current ID is legal.
        if (id_is_legal(is_read, beat)) begin
          break;
        end else begin
          // The current ID is currently not legal, so try another ID in the next cycle and
          // release the semaphore until then.
          cnt_sem.put();
          rand_wait(1, 1);
          if (!beat.ax_lock) begin // The ID of an exclusive transfer must not be changed.
            rand_success = std::randomize(id); assert(rand_success);
            beat.ax_id = id;
          end
        end
      end
      // Mark transfer for decided ID as in flight.
      if (!is_read) begin
        w_flight_cnt[beat.ax_id]++;
        tot_w_flight_cnt++;
        if (beat.ax_atop != 2'b00) begin
          // This is an ATOP, so it gives rise to a write response.
          atop_resp_b[beat.ax_id] = 1'b1;
          if (beat.ax_atop[5]) begin
            // This ATOP type additionally gives rise to a read response.
            atop_resp_r[beat.ax_id] = 1'b1;
          end
        end
      end else begin
        r_flight_cnt[beat.ax_id]++;
        tot_r_flight_cnt++;
      end
      // Release semaphore on in-flight counters.
      cnt_sem.put();
    endtask

    task send_ars(input int n_reads);
      automatic logic rand_success;
      repeat (n_reads) begin
        automatic id_t id;
        automatic ax_beat_t ar_beat = new_rand_burst(1'b1);
        while (tot_r_flight_cnt >= MAX_READ_TXNS) begin
          rand_wait(1, 1);
        end
        if (AXI_EXCLS) begin
          rand_excl_ar(ar_beat);
        end
        legalize_id(1'b1, ar_beat);
        rand_wait(AX_MIN_WAIT_CYCLES, AX_MAX_WAIT_CYCLES);
        drv.send_ar(ar_beat);
        if (ar_beat.ax_lock) excl_queue.push_back(ar_beat);
      end
    endtask

    task recv_rs(ref logic ar_done, aw_done);
      while (!(ar_done && tot_r_flight_cnt == 0 &&
          (!AXI_ATOPS || (AXI_ATOPS && aw_done && atop_resp_r == '0))
      )) begin
        automatic r_beat_t r_beat;
        rand_wait(RESP_MIN_WAIT_CYCLES, RESP_MAX_WAIT_CYCLES);
        if (tot_r_flight_cnt > 0 || atop_resp_r > 0) begin
          drv.recv_r(r_beat);
          if (r_beat.r_last) begin
            cnt_sem.get();
            if (atop_resp_r[r_beat.r_id]) begin
              atop_resp_r[r_beat.r_id] = 1'b0;
            end else begin
              r_flight_cnt[r_beat.r_id]--;
              tot_r_flight_cnt--;
            end
            cnt_sem.put();
          end
        end
      end
    endtask

    task create_aws(input int n_writes);
      automatic logic rand_success;
      repeat (n_writes) begin
        automatic bit excl = 1'b0;
        automatic ax_beat_t aw_beat;
        if (AXI_EXCLS && excl_queue.size() > 0) excl = $random();
        if (excl) begin
          aw_beat = excl_queue.pop_front();
        end else begin
          aw_beat = new_rand_burst(1'b0);
          if (AXI_ATOPS) rand_atop_burst(aw_beat);
        end
        while (tot_w_flight_cnt >= MAX_WRITE_TXNS) begin
          rand_wait(1, 1);
        end
        legalize_id(1'b0, aw_beat);
        aw_queue.push_back(aw_beat);
        w_queue.push_back(aw_beat);
      end
    endtask

    task send_aws(ref logic aw_done);
      while (!(aw_done && aw_queue.size() == 0)) begin
        automatic ax_beat_t aw_beat;
        wait (aw_queue.size() > 0 || (aw_done && aw_queue.size() == 0));
        aw_beat = aw_queue.pop_front();
        rand_wait(AX_MIN_WAIT_CYCLES, AX_MAX_WAIT_CYCLES);
        drv.send_aw(aw_beat);
      end
    endtask

    task send_ws(ref logic aw_done);
      while (!(aw_done && w_queue.size() == 0)) begin
        automatic ax_beat_t aw_beat;
        automatic addr_t addr;
        static logic rand_success;
        wait (w_queue.size() > 0 || (aw_done && w_queue.size() == 0));
        aw_beat = w_queue.pop_front();
        addr = aw_beat.ax_addr;
        for (int unsigned i = 0; i < aw_beat.ax_len + 1; i++) begin
          automatic w_beat_t w_beat = new;
          automatic int unsigned begin_byte, end_byte, n_bytes;
          automatic logic [AXI_STRB_WIDTH-1:0] rand_strb, strb_mask;
          rand_success = w_beat.randomize(); assert (rand_success);
          // Determine strobe.
          w_beat.w_strb = '0;
          n_bytes = 2**aw_beat.ax_size;
          begin_byte = addr % AXI_STRB_WIDTH;
          end_byte = ((begin_byte + n_bytes) >> aw_beat.ax_size) << aw_beat.ax_size;
          strb_mask = '0;
          for (int unsigned b = begin_byte; b < end_byte; b++)
            strb_mask[b] = 1'b1;
          rand_success = std::randomize(rand_strb); assert (rand_success);
          w_beat.w_strb |= (rand_strb & strb_mask);
          // Determine last.
          w_beat.w_last = (i == aw_beat.ax_len);
          rand_wait(W_MIN_WAIT_CYCLES, W_MAX_WAIT_CYCLES);
          drv.send_w(w_beat);
          if (aw_beat.ax_burst == axi_pkg::BURST_INCR)
            addr += n_bytes;
        end
      end
    endtask

    task recv_bs(ref logic aw_done);
      while (!(aw_done && tot_w_flight_cnt == 0)) begin
        automatic b_beat_t b_beat;
        rand_wait(RESP_MIN_WAIT_CYCLES, RESP_MAX_WAIT_CYCLES);
        drv.recv_b(b_beat);
        cnt_sem.get();
        if (atop_resp_b[b_beat.b_id]) begin
          atop_resp_b[b_beat.b_id] = 1'b0;
        end
        w_flight_cnt[b_beat.b_id]--;
        tot_w_flight_cnt--;
        cnt_sem.put();
      end
    endtask

    // Issue n_reads random read and n_writes random write transactions to an address range.
    task run(input int n_reads, input int n_writes);
      automatic logic  ar_done = 1'b0,
                       aw_done = 1'b0;
      fork
        begin
          send_ars(n_reads);
          ar_done = 1'b1;
        end
        recv_rs(ar_done, aw_done);
        begin
          create_aws(n_writes);
          aw_done = 1'b1;
        end
        send_aws(aw_done);
        send_ws(aw_done);
        recv_bs(aw_done);
      join
    endtask

  endclass

  class axi_rand_slave #(
    // AXI interface parameters
    parameter int   AW = 32,
    parameter int   DW = 32,
    parameter int   IW = 8,
    parameter int   UW = 1,
    // Stimuli application and test time
    parameter time  TA = 0ps,
    parameter time  TT = 0ps,
    parameter bit   RAND_RESP = 0,
    // Upper and lower bounds on wait cycles on Ax, W, and resp (R and B) channels
    parameter int   AX_MIN_WAIT_CYCLES = 0,
    parameter int   AX_MAX_WAIT_CYCLES = 100,
    parameter int   R_MIN_WAIT_CYCLES = 0,
    parameter int   R_MAX_WAIT_CYCLES = 5,
    parameter int   RESP_MIN_WAIT_CYCLES = 0,
    parameter int   RESP_MAX_WAIT_CYCLES = 20
  );
    typedef axi_test::axi_driver #(
      .AW(AW), .DW(DW), .IW(IW), .UW(UW), .TA(TA), .TT(TT)
    ) axi_driver_t;
    typedef rand_id_queue_pkg::rand_id_queue #(
      .data_t   (axi_driver_t::ax_beat_t),
      .ID_WIDTH (IW)
    ) rand_ax_beat_queue_t;
    typedef axi_driver_t::ax_beat_t ax_beat_t;
    typedef axi_driver_t::b_beat_t b_beat_t;
    typedef axi_driver_t::r_beat_t r_beat_t;
    typedef axi_driver_t::w_beat_t w_beat_t;

    axi_driver_t          drv;
    rand_ax_beat_queue_t  ar_queue;
    ax_beat_t             aw_queue[$];
    int unsigned          b_wait_cnt;

    function new(
      virtual AXI_BUS_DV #(
        .AXI_ADDR_WIDTH(AW),
        .AXI_DATA_WIDTH(DW),
        .AXI_ID_WIDTH(IW),
        .AXI_USER_WIDTH(UW)
      ) axi
    );
      this.drv = new(axi);
      this.ar_queue = new;
      this.b_wait_cnt = 0;
      this.reset();
    endfunction

    function void reset();
      drv.reset_slave();
    endfunction

    // TODO: The `rand_wait` task exists in `rand_verif_pkg`, but that task cannot be called with
    // `this.drv.axi.clk_i` as `clk` argument.  What is the syntax getting an assignable reference?
    task automatic rand_wait(input int unsigned min, max);
      int unsigned rand_success, cycles;
      rand_success = std::randomize(cycles) with {
        cycles >= min;
        cycles <= max;
      };
      assert (rand_success) else $error("Failed to randomize wait cycles!");
      repeat (cycles) @(posedge this.drv.axi.clk_i);
    endtask

    task recv_ars();
      forever begin
        automatic ax_beat_t ar_beat;
        rand_wait(AX_MIN_WAIT_CYCLES, AX_MAX_WAIT_CYCLES);
        drv.recv_ar(ar_beat);
        ar_queue.push(ar_beat.ax_id, ar_beat);
      end
    endtask

    task send_rs();
      forever begin
        automatic logic rand_success;
        automatic ax_beat_t ar_beat;
        automatic r_beat_t r_beat = new;
        wait (ar_queue.size > 0);
        ar_beat = ar_queue.peek();
        rand_success = r_beat.randomize(); assert(rand_success);
        r_beat.r_id = ar_beat.ax_id;
        if (RAND_RESP && !ar_beat.ax_atop[axi_pkg::ATOP_R_RESP])
          r_beat.r_resp[1] = $random();
        if (ar_beat.ax_lock)
          r_beat.r_resp[0]= $random();
        rand_wait(R_MIN_WAIT_CYCLES, R_MAX_WAIT_CYCLES);
        if (ar_beat.ax_len == '0) begin
          r_beat.r_last = 1'b1;
          void'(ar_queue.pop_id(ar_beat.ax_id));
        end else begin
          ar_beat.ax_len--;
          ar_queue.set(ar_beat.ax_id, ar_beat);
        end
        drv.send_r(r_beat);
      end
    endtask

    task recv_aws();
      forever begin
        automatic ax_beat_t aw_beat;
        rand_wait(AX_MIN_WAIT_CYCLES, AX_MAX_WAIT_CYCLES);
        drv.recv_aw(aw_beat);
        aw_queue.push_back(aw_beat);
        // Atomic{Load,Swap,Compare}s require an R response.
        if (aw_beat.ax_atop[5]) begin
          ar_queue.push(aw_beat.ax_id, aw_beat);
        end
      end
    endtask

    task recv_ws();
      forever begin
        automatic ax_beat_t aw_beat;
        forever begin
          automatic w_beat_t w_beat;
          rand_wait(RESP_MIN_WAIT_CYCLES, RESP_MAX_WAIT_CYCLES);
          drv.recv_w(w_beat);
          if (w_beat.w_last)
            break;
        end
        b_wait_cnt++;
      end
    endtask

    task send_bs();
      forever begin
        automatic ax_beat_t aw_beat;
        automatic b_beat_t b_beat = new;
        automatic logic rand_success;
        wait (b_wait_cnt > 0 && (aw_queue.size() != 0));
        aw_beat = aw_queue.pop_front();
        rand_success = b_beat.randomize(); assert(rand_success);
        b_beat.b_id = aw_beat.ax_id;
        if (RAND_RESP && !aw_beat.ax_atop[axi_pkg::ATOP_R_RESP])
          b_beat.b_resp[1] = $random();
        if (aw_beat.ax_lock) begin
          b_beat.b_resp[0]= $random();
        end
        rand_wait(RESP_MIN_WAIT_CYCLES, RESP_MAX_WAIT_CYCLES);
        drv.send_b(b_beat);
        b_wait_cnt--;
      end
    endtask

    task run();
      fork
        recv_ars();
        send_rs();
        recv_aws();
        recv_ws();
        send_bs();
      join
    endtask

  endclass

  // AXI4-Lite random master and slave
  class axi_lite_rand_master #(
    // AXI interface parameters
    parameter int unsigned AW = 0,
    parameter int unsigned DW = 0,
    // Stimuli application and test time
    parameter time  TA = 2ns,
    parameter time  TT = 8ns,
    parameter int unsigned MIN_ADDR = 32'h0000_0000,
    parameter int unsigned MAX_ADDR = 32'h1000_0000,
    // Maximum number of open transactions
    parameter int   MAX_READ_TXNS = 1,
    parameter int   MAX_WRITE_TXNS = 1,
    // Upper and lower bounds on wait cycles on Ax, W, and resp (R and B) channels
    parameter int   AX_MIN_WAIT_CYCLES = 0,
    parameter int   AX_MAX_WAIT_CYCLES = 100,
    parameter int   W_MIN_WAIT_CYCLES = 0,
    parameter int   W_MAX_WAIT_CYCLES = 5,
    parameter int   RESP_MIN_WAIT_CYCLES = 0,
    parameter int   RESP_MAX_WAIT_CYCLES = 20
  );
    typedef axi_test::axi_lite_driver #(
      .AW(AW), .DW(DW), .TA(TA), .TT(TT)
    ) axi_driver_t;

    typedef logic [AW-1:0]   addr_t;
    typedef logic [DW-1:0]   data_t;
    typedef logic [DW/8-1:0] strb_t;

    string         name;
    axi_driver_t   drv;
    addr_t         aw_queue[$],
                   ar_queue[$];
    logic          b_queue[$];
    logic          w_queue[$];

    function new(
      virtual AXI_LITE_DV #(
        .AXI_ADDR_WIDTH(AW),
        .AXI_DATA_WIDTH(DW)
      ) axi,
      input string name
    );
      this.drv  = new(axi);
      this.name = name;
      assert(AW != 0) else $fatal(1, "Address width must be non-zero!");
      assert(DW != 0) else $fatal(1, "Data width must be non-zero!");
    endfunction

    function void reset();
      drv.reset_master();
    endfunction

    task automatic rand_wait(input int unsigned min, max);
      int unsigned rand_success, cycles;
      rand_success = std::randomize(cycles) with {
        cycles >= min;
        cycles <= max;
      };
      assert (rand_success) else $error("Failed to randomize wait cycles!");
      repeat (cycles) @(posedge this.drv.axi.clk_i);
    endtask

    task automatic send_ars(input int unsigned n_reads);
      automatic addr_t ar_addr;
      automatic prot_t ar_prot;
      repeat (n_reads) begin
        rand_wait(AX_MIN_WAIT_CYCLES, AX_MAX_WAIT_CYCLES);
        ar_addr = addr_t'($urandom_range(MIN_ADDR, MAX_ADDR));
        ar_prot = prot_t'($urandom());
        this.ar_queue.push_back(ar_addr);
        $display("%0t %s> Send AR with ADDR: %h PROT: %b", $time(), this.name, ar_addr, ar_prot);
        drv.send_ar(ar_addr, ar_prot);
      end
    endtask : send_ars

    task automatic recv_rs(input int unsigned n_reads);
      automatic addr_t          ar_addr;
      automatic data_t           r_data;
      automatic axi_pkg::resp_t  r_resp;
      repeat (n_reads) begin
        wait (ar_queue.size() > 0);
        ar_addr = this.ar_queue.pop_front();
        rand_wait(RESP_MIN_WAIT_CYCLES, RESP_MAX_WAIT_CYCLES);
        drv.recv_r(r_data, r_resp);
        $display("%0t %s> Recv  R with DATA: %h RESP: %0h", $time(), this.name, r_data, r_resp);
      end
    endtask : recv_rs

    task automatic send_aws(input int unsigned n_writes);
      automatic addr_t aw_addr;
      automatic prot_t aw_prot;
      repeat (n_writes) begin
        rand_wait(AX_MIN_WAIT_CYCLES, AX_MAX_WAIT_CYCLES);
        aw_addr = addr_t'($urandom_range(MIN_ADDR, MAX_ADDR));
        aw_prot = prot_t'($urandom());
        this.aw_queue.push_back(aw_addr);
        $display("%0t %s> Send AW with ADDR: %h PROT: %b", $time(), this.name, aw_addr, aw_prot);
        this.drv.send_aw(aw_addr, aw_prot);
        this.b_queue.push_back(1'b1);
      end
    endtask : send_aws

    task automatic send_ws(input int unsigned n_writes);
      automatic logic  rand_success;
      automatic addr_t aw_addr;
      automatic data_t w_data;
      automatic strb_t w_strb;
      repeat (n_writes) begin
        wait (aw_queue.size() > 0);
        rand_wait(RESP_MIN_WAIT_CYCLES, RESP_MAX_WAIT_CYCLES);
        aw_addr = aw_queue.pop_front();
        rand_success = std::randomize(w_data); assert(rand_success);
        rand_success = std::randomize(w_strb); assert(rand_success);
        $display("%0t %s> Send  W with DATA: %h STRB: %h", $time(), this.name, w_data, w_strb);
        this.drv.send_w(w_data, w_strb);
        w_queue.push_back(1'b1);
      end
    endtask : send_ws

    task automatic recv_bs(input int unsigned n_writes);
      automatic logic           go_b;
      automatic axi_pkg::resp_t b_resp;
      repeat (n_writes) begin
        wait (b_queue.size() > 0 && w_queue.size() > 0);
        go_b = this.b_queue.pop_front();
        go_b = this.w_queue.pop_front();
        rand_wait(RESP_MIN_WAIT_CYCLES, RESP_MAX_WAIT_CYCLES);
        this.drv.recv_b(b_resp);
        $display("%0t %s> Recv  B with RESP: %h", $time(), this.name, b_resp);
      end
    endtask : recv_bs

    task automatic run(input int unsigned n_reads, input int unsigned n_writes);
      $display("Run for Reads %0d, Writes %0d", n_reads, n_writes);
      fork
        send_ars(n_reads);
        recv_rs(n_reads);
        send_aws(n_writes);
        send_ws(n_writes);
        recv_bs(n_writes);
      join
    endtask

    // write data to a specific address
    task automatic write(input addr_t w_addr, input prot_t w_prot = prot_t'(0), input data_t w_data,
                         input strb_t w_strb, output axi_pkg::resp_t b_resp);
      $display("%0t %s> Write to ADDR: %h, PROT: %b DATA: %h, STRB: %h",
          $time(), this.name, w_addr, w_prot, w_data, w_strb);
      fork
        this.drv.send_aw(w_addr, w_prot);
        this.drv.send_w(w_data, w_strb);
      join
      this.drv.recv_b(b_resp);
      $display("%0t %s> Received write response from ADDR: %h RESP: %h",
          $time(), this.name, w_addr, b_resp);
    endtask : write

    // read data from a specific location
    task automatic read(input addr_t r_addr, input prot_t r_prot = prot_t'(0),
                        output data_t r_data, output axi_pkg::resp_t r_resp);
      $display("%0t %s> Read from ADDR: %h PROT: %b",
          $time(), this.name, r_addr, r_prot);
      this.drv.send_ar(r_addr, r_prot);
      this.drv.recv_r(r_data, r_resp);
      $display("%0t %s> Recieved read response from ADDR: %h DATA: %h RESP: %h",
          $time(), this.name, r_addr, r_data, r_resp);
    endtask : read
  endclass

  class axi_lite_rand_slave #(
    // AXI interface parameters
    parameter int unsigned AW = 0,
    parameter int unsigned DW = 0,
    // Stimuli application and test time
    parameter time  TA = 2ns,
    parameter time  TT = 8ns,
    // Upper and lower bounds on wait cycles on Ax, W, and resp (R and B) channels
    parameter int   AX_MIN_WAIT_CYCLES = 0,
    parameter int   AX_MAX_WAIT_CYCLES = 100,
    parameter int   R_MIN_WAIT_CYCLES = 0,
    parameter int   R_MAX_WAIT_CYCLES = 5,
    parameter int   RESP_MIN_WAIT_CYCLES = 0,
    parameter int   RESP_MAX_WAIT_CYCLES = 20
  );
    typedef axi_test::axi_lite_driver #(
      .AW(AW), .DW(DW), .TA(TA), .TT(TT)
    ) axi_driver_t;

    typedef logic [AW-1:0]   addr_t;
    typedef logic [DW-1:0]   data_t;
    typedef logic [DW/8-1:0] strb_t;

    string         name;
    axi_driver_t   drv;
    addr_t         aw_queue[$],
                   ar_queue[$];
    logic          b_queue[$];

    function new(
      virtual AXI_LITE_DV #(
        .AXI_ADDR_WIDTH(AW),
        .AXI_DATA_WIDTH(DW)
      ) axi,
      input string name
    );
      this.drv = new(axi);
      this.name = name;
      assert(AW != 0) else $fatal(1, "Address width must be non-zero!");
      assert(DW != 0) else $fatal(1, "Data width must be non-zero!");
    endfunction

    function void reset();
      this.drv.reset_slave();
    endfunction

    task automatic rand_wait(input int unsigned min, max);
      int unsigned rand_success, cycles;
      rand_success = std::randomize(cycles) with {
        cycles >= min;
        cycles <= max;
      };
      assert (rand_success) else $error("Failed to randomize wait cycles!");
      repeat (cycles) @(posedge this.drv.axi.clk_i);
    endtask

    task automatic recv_ars();
      forever begin
        automatic addr_t ar_addr;
        automatic prot_t ar_prot;
        rand_wait(AX_MIN_WAIT_CYCLES, AX_MAX_WAIT_CYCLES);
        this.drv.recv_ar(ar_addr, ar_prot);
        $display("%0t %s> Recv AR with ADDR: %h PROT: %b", $time(), this.name, ar_addr, ar_prot);
        this.ar_queue.push_back(ar_addr);
      end
    endtask : recv_ars

    task automatic send_rs();
      forever begin
        automatic logic rand_success;
        automatic addr_t ar_addr;
        automatic data_t r_data;
        wait (ar_queue.size() > 0);
        ar_addr = this.ar_queue.pop_front();
        rand_success = std::randomize(r_data); assert(rand_success);
        rand_wait(R_MIN_WAIT_CYCLES, R_MAX_WAIT_CYCLES);
        $display("%0t %s> Send  R with DATA: %h", $time(), this.name, r_data);
        this.drv.send_r(r_data, axi_pkg::RESP_OKAY);
      end
    endtask : send_rs

    task automatic recv_aws();
      forever begin
        automatic addr_t aw_addr;
        automatic prot_t aw_prot;
        rand_wait(AX_MIN_WAIT_CYCLES, AX_MAX_WAIT_CYCLES);
        this.drv.recv_aw(aw_addr, aw_prot);
        $display("%0t %s> Recv AW with ADDR: %h PROT: %b", $time(), this.name, aw_addr, aw_prot);
        this.aw_queue.push_back(aw_addr);
      end
    endtask : recv_aws

    task automatic recv_ws();
      forever begin
        automatic data_t w_data;
        automatic strb_t w_strb;
        rand_wait(RESP_MIN_WAIT_CYCLES, RESP_MAX_WAIT_CYCLES);
        this.drv.recv_w(w_data, w_strb);
        $display("%0t %s> Recv  W with DATA: %h SRTB: %h", $time(), this.name, w_data, w_strb);
        this.b_queue.push_back(1'b1);
      end
    endtask : recv_ws

    task automatic send_bs();
      forever begin
        automatic logic           rand_success;
        automatic addr_t          go_aw;
        automatic logic           go_b;
        automatic axi_pkg::resp_t b_resp;
        wait (aw_queue.size() > 0 && b_queue.size() > 0);
        go_aw = this.aw_queue.pop_front();
        go_b  = this.b_queue.pop_front();
        rand_wait(RESP_MIN_WAIT_CYCLES, RESP_MAX_WAIT_CYCLES);
        rand_success = std::randomize(b_resp); assert(rand_success);
        $display("%0t %s> Send  B with RESP: %h", $time(), this.name, b_resp);
        this.drv.send_b(b_resp);
      end
    endtask : send_bs

    task automatic run();
      fork
        recv_ars();
        send_rs();
        recv_aws();
        recv_ws();
        send_bs();
      join
    endtask
  endclass

  /// `axi_scoreboard` models a memory that only gets changed by the monitored AXI4+ATOP bus.
  ///
  /// This class is only capable of modeling `INCR` burst type, and cannot handle atomic operations.
  /// The internal memory representation is updated by W beats.  This class does not support
  /// reordering of two B responses to one memory location.  That is, if two write transactions on
  /// the observed bus target the same address, the B responses must be observed in the order of the
  /// AW beats; otherwise, the internal memory representation of this class gets corrupted.
  ///
  /// Example usage:
  ///   typedef axi_test::axi_scoreboard #(
  ///   .IW ( AxiIdWidth   ),
  ///   .AW ( AxiAddrWidth ),
  ///   .DW ( AxiDataWidth ),
  ///   .UW ( AxiUserWidth ),
  ///   .TT ( TestTime     )
  /// ) axi_scoreboard_t;
  /// axi_scoreboard_t axi_scoreboard = new(monitor_dv);
  /// initial begin
  ///   axi_scoreboard.enable_all_checks();
  ///   wait (rst_n);
  ///   axi_scoreboard.monitor();
  /// end
  class axi_scoreboard #(
    /// AXI4+ATOP ID width
    parameter int unsigned IW = 0,
    /// AXI4+ATOP address width
    parameter int unsigned AW = 0,
    /// AXI4+ATOP data width
    parameter int unsigned DW = 0,
    /// AXI4+ATOP user width
    parameter int unsigned UW = 0,
    /// Stimuli test time
    parameter time TT = 0ns
  );
    // Number of checks
    localparam int unsigned NUM_CHECKS  = 32'd3;
    // Size of the AXI4+ATOP bus, used for alignment of the beat address
    localparam axi_pkg::size_t BUS_SIZE = $clog2(DW/8);

    // Typedefs
    typedef enum logic [1:0] {
      ReadCheck  = 2'd0,
      BRespCheck = 2'd1,
      RRespCheck = 2'd2
    } check_e;
    typedef logic [7:0]      byte_t;
    typedef logic [IW-1:0]   axi_id_t;
    typedef logic [AW-1:0]   axi_addr_t;
    typedef axi_ax_beat #(.AW(AW), .IW(IW), .UW(UW)) ax_beat_t;
    typedef axi_w_beat  #(.DW(DW), .UW(UW))          w_beat_t;
    typedef axi_b_beat  #(.IW(IW), .UW(UW))          b_beat_t;
    typedef axi_r_beat  #(.DW(DW), .IW(IW), .UW(UW)) r_beat_t;

    // Monitor interface
    virtual AXI_BUS_DV #(
      .AXI_ADDR_WIDTH ( AW ),
      .AXI_DATA_WIDTH ( DW ),
      .AXI_ID_WIDTH   ( IW ),
      .AXI_USER_WIDTH ( UW )
    ) axi;
    // Memory model
    protected byte_t memory_q [axi_addr_t][$];
    // Which checks are enabled
    protected bit [NUM_CHECKS-1:0] check_en;
    // Sampling queues
    protected ax_beat_t aw_sample [$];
    protected w_beat_t   w_sample [$];
    protected b_beat_t   b_sample [2**IW][$];
    protected ax_beat_t ar_sample [2**IW][$];
    protected r_beat_t   r_sample [2**IW][$];

    // Write queues
    protected ax_beat_t  b_queue  [2**IW][$];

    /// New constructor
    function new(
      virtual AXI_BUS_DV #(
        .AXI_ADDR_WIDTH ( AW ),
        .AXI_DATA_WIDTH ( DW ),
        .AXI_ID_WIDTH   ( IW ),
        .AXI_USER_WIDTH ( UW )
      ) axi
    );
      this.axi      = axi;
      this.check_en = '0;
    endfunction

    /// Start the test for this cycle
    protected task automatic cycle_start;
      #TT;
    endtask

    /// End this cycle
    protected task automatic cycle_end;
      @(posedge this.axi.clk_i);
    endtask

    /// Handle update of the golden model with W beats.
    protected task automatic handle_write();
      axi_addr_t beat_addresses [];
      axi_addr_t bus_address;
      ax_beat_t  aw_beat;
      w_beat_t   w_beat;
      byte_t     write_data;
      forever begin
        wait (this.aw_sample.size() > 0);
        aw_beat        = this.aw_sample.pop_front();
        // This scoreborad only supports this type of burst:
        assert (aw_beat.ax_burst == axi_pkg::BURST_INCR || aw_beat.ax_len == '0) else
            $warning("Not supported AW burst: BURST: %0h.", aw_beat.ax_burst);
        assert (aw_beat.ax_atop == '0) else
            $warning("Atomic transfers not supported: ATOP: %0h.", aw_beat.ax_atop);

        beat_addresses = new[aw_beat.ax_len + 1];
        for (int unsigned i = 0; i <= aw_beat.ax_len; i++) begin
          beat_addresses[i] = axi_pkg::beat_addr(aw_beat.ax_addr, aw_beat.ax_size, aw_beat.ax_len,
              aw_beat.ax_burst, i);
          bus_address       = axi_pkg::aligned_addr(beat_addresses[i], BUS_SIZE);
          // Check if the memory array is initialyzed at this beat address (aligned on the bus)
          if (!this.memory_q.exists(bus_address)) begin
            for (int unsigned j = 0; j < axi_pkg::num_bytes(BUS_SIZE); j++) begin
              this.memory_q[bus_address+j].push_back(8'bxxxxxxxx);
            end
          end
        end
        // handle all write beats for this write access
        for (int unsigned i = 0; i <= aw_beat.ax_len; i++) begin
          wait (this.w_sample.size() > 0);
          w_beat      = this.w_sample.pop_front();
          bus_address = axi_pkg::aligned_addr(beat_addresses[i], BUS_SIZE);
          for (int unsigned j = 0; j < axi_pkg::num_bytes(BUS_SIZE); j++) begin
            write_data = this.memory_q[bus_address+j][$];
            write_data = (w_beat.w_strb[j]) ? w_beat.w_data[8*j+:8] : write_data;
            this.memory_q[bus_address+j].push_back(write_data);
          end
        end
        assert (w_beat.w_last) else $warning("Unexpected W last not set.");
        this.b_queue[aw_beat.ax_id].push_back(aw_beat);
      end
    endtask : handle_write

    /// Handle Write response checking, update golden model
    protected task automatic handle_write_resp(input axi_id_t id);
      ax_beat_t  aw_beat;
      b_beat_t   b_beat;
      axi_addr_t bus_address;
      forever begin
        wait (this.b_sample[id].size() > 0);
        assert (this.b_queue[id].size() > 0) else
            wait (this.b_queue[id].size() > 0);
        aw_beat = b_queue[id].pop_front();
        b_beat  = b_sample[id].pop_front();
        if (check_en[BRespCheck]) begin
          assert (b_beat.b_id   == id);
          assert (b_beat.b_resp == axi_pkg::RESP_OKAY) else
              $warning("Behavior for b_resp != axi_pkg::RESP_OKAY not modeled.");
        end
        // pop all accessed memory locations by this beat
        for (int unsigned i = 0; i <= aw_beat.ax_len; i++) begin
          bus_address = axi_pkg::aligned_addr(
              axi_pkg::beat_addr(aw_beat.ax_addr, aw_beat.ax_size, aw_beat.ax_len, aw_beat.ax_burst,
                  i), BUS_SIZE);
          for (int j = 0; j < axi_pkg::num_bytes(BUS_SIZE); j++) begin
            memory_q[bus_address+j].delete(0);
          end
        end
      end
    endtask : handle_write_resp

    /// Handle read checking against the golden model
    protected task automatic handle_read(input axi_id_t id);
      ax_beat_t  ar_beat;
      r_beat_t   r_beat;
      axi_addr_t bus_address, beat_address, idx_data;
      byte_t     act_data;
      byte_t     exp_data[$];
      byte_t     tst_data[$];
      forever begin
        wait (this.ar_sample[id].size() > 0);
        ar_beat = this.ar_sample[id].pop_front();
        // This scoreborad only supports this type of burst:
        assert (ar_beat.ax_burst == axi_pkg::BURST_INCR || ar_beat.ax_len == '0) else
            $warning("Not supported AR burst: BURST: %0h.", ar_beat.ax_burst);

        for (int unsigned i = 0; i <= ar_beat.ax_len; i++) begin
          wait (this.r_sample[id].size() > 0);
          r_beat = this.r_sample[id].pop_front();
          beat_address = axi_pkg::beat_addr(ar_beat.ax_addr, ar_beat.ax_size, ar_beat.ax_len,
              ar_beat.ax_burst, i);
          beat_address = axi_pkg::aligned_addr(beat_address, ar_beat.ax_size);
          bus_address  = axi_pkg::aligned_addr(beat_address, BUS_SIZE);
          if (!this.memory_q.exists(bus_address)) begin
            for (int unsigned j = 0; j < axi_pkg::num_bytes(BUS_SIZE); j++) begin
              this.memory_q[bus_address+j].push_back(8'bxxxxxxxx);
            end
          end
          // Assert that the correct data is read.
          if (this.check_en[ReadCheck]) begin
            for (int unsigned j = 0; j < axi_pkg::num_bytes(ar_beat.ax_size); j++) begin
              idx_data  = 8*BUS_SIZE'(beat_address+j);
              act_data  = r_beat.r_data[idx_data+:8];
              exp_data  = this.memory_q[beat_address+j];
              tst_data  = exp_data.find with (item === 8'hxx || item === act_data);
              assert (tst_data.size() > 0) else begin
                $warning("Unexpected RData ID: %0h Addr: %0h Byte Idx: %0h Exp Data : %0h Data: %h",
                r_beat.r_id, beat_address+j, idx_data, exp_data, act_data);
              end
            end
          end
        end
        if (this.check_en[RRespCheck]) begin
          assert (r_beat.r_id   == id);
          assert (r_beat.r_resp == axi_pkg::RESP_OKAY);
          assert (r_beat.r_last);
        end
      end
    endtask : handle_read

    /// Monitor AW channel
    protected task automatic mon_aw();
      ax_beat_t aw_beat;
      forever begin
        cycle_start();
        if (this.axi.aw_valid && this.axi.aw_ready) begin
          aw_beat           = new;
          aw_beat.ax_id     = this.axi.aw_id;
          aw_beat.ax_addr   = this.axi.aw_addr;
          aw_beat.ax_len    = this.axi.aw_len;
          aw_beat.ax_size   = this.axi.aw_size;
          aw_beat.ax_burst  = this.axi.aw_burst;
          aw_beat.ax_lock   = this.axi.aw_lock;
          aw_beat.ax_cache  = this.axi.aw_cache;
          aw_beat.ax_prot   = this.axi.aw_prot;
          aw_beat.ax_qos    = this.axi.aw_qos;
          aw_beat.ax_region = this.axi.aw_region;
          aw_beat.ax_atop   = this.axi.aw_atop;
          aw_beat.ax_user   = this.axi.aw_user;
          this.aw_sample.push_back(aw_beat);
        end
        cycle_end();
      end
    endtask : mon_aw

    /// Monitor W channel
    protected task automatic mon_w();
      w_beat_t w_beat;
      forever begin
        cycle_start();
        if (this.axi.w_valid && this.axi.w_ready) begin
          w_beat        = new;
          w_beat.w_data = this.axi.w_data;
          w_beat.w_strb = this.axi.w_strb;
          w_beat.w_last = this.axi.w_last;
          w_beat.w_user = this.axi.w_user;
          this.w_sample.push_back(w_beat);
        end
        cycle_end();
      end
    endtask : mon_w

    /// Monitor B channel
    protected task automatic mon_b();
      b_beat_t b_beat;
      forever begin
        cycle_start();
        if (this.axi.b_valid && this.axi.b_ready) begin
          b_beat        = new;
          b_beat.b_id   = this.axi.b_id;
          b_beat.b_resp = this.axi.b_resp;
          b_beat.b_user = this.axi.b_user;
          this.b_sample[this.axi.b_id].push_back(b_beat);
        end
        cycle_end();
      end
    endtask : mon_b

    /// Monitor AR channel
    protected task automatic mon_ar();
      ax_beat_t ar_beat;
      forever begin
        cycle_start();
        if (this.axi.ar_valid && this.axi.ar_ready) begin
          ar_beat           = new;
          ar_beat.ax_id     = this.axi.ar_id;
          ar_beat.ax_addr   = this.axi.ar_addr;
          ar_beat.ax_len    = this.axi.ar_len;
          ar_beat.ax_size   = this.axi.ar_size;
          ar_beat.ax_burst  = this.axi.ar_burst;
          ar_beat.ax_lock   = this.axi.ar_lock;
          ar_beat.ax_cache  = this.axi.ar_cache;
          ar_beat.ax_prot   = this.axi.ar_prot;
          ar_beat.ax_qos    = this.axi.ar_qos;
          ar_beat.ax_region = this.axi.ar_region;
          ar_beat.ax_atop   = 6'bxxxxxx;
          ar_beat.ax_user   = this.axi.ar_user;
          this.ar_sample[this.axi.ar_id].push_back(ar_beat);
        end
        cycle_end();
      end
    endtask : mon_ar

    /// Monitor R channel
    protected task automatic mon_r();
      r_beat_t r_beat;
      forever begin
        cycle_start();
        if (this.axi.r_valid && this.axi.r_ready) begin
          r_beat        = new;
          r_beat.r_id   = this.axi.r_id;
          r_beat.r_data = this.axi.r_data;
          r_beat.r_resp = this.axi.r_resp;
          r_beat.r_last = this.axi.r_last;
          r_beat.r_user = this.axi.r_user;
          this.r_sample[this.axi.r_id].push_back(r_beat);
        end
        cycle_end();
      end
    endtask : mon_r

    /// Monitor the channel, forks a number of processes, calling initial does not get stalled.
    /// This task should only be called once after bus reset.
    task automatic monitor();
      fork
        mon_aw();
        mon_w();
        mon_b();
        handle_write();
        mon_ar();
        mon_r();
      join_none
      for (int unsigned i = 0; i < 2**IW; i++) begin
        int unsigned j = i;
        fork
          handle_write_resp(axi_id_t'(j));
          handle_read(axi_id_t'(j));
        join_none
      end
    endtask : monitor

    /// Enable checking of the read data
    /// Asserts that the data on the R channel matches the expected response modeled by th class.
    task enable_read_check();
      this.check_en[ReadCheck] = 1'b1;
    endtask : enable_read_check

    /// Disable checking of the read data
    task disable_read_check();
      this.check_en[ReadCheck] = 1'b0;
    endtask : disable_read_check

    /// Enable checking of the write resp
    /// Asserts that the B channel response is `axi_pkg::RESP_OKAY`.
    task enable_b_resp_check();
      this.check_en[BRespCheck] = 1'b1;
    endtask : enable_b_resp_check

    /// Disable checking of the write resp
    task disable_b_resp_check();
      this.check_en[BRespCheck] = 1'b0;
    endtask : disable_b_resp_check

    /// Enable checking of the read resp
    /// Asserts that the R channel response is `axi_pkg::RESP_OKAY`.
    /// Asserts that the R channel last flag is correctly set.
    task enable_r_resp_check();
      this.check_en[RRespCheck] = 1'b1;
    endtask : enable_r_resp_check

    /// Disable checking of the read resp
    task disable_r_resp_check();
      this.check_en[RRespCheck] = 1'b0;
    endtask : disable_r_resp_check

    /// Enable all checks
    task enable_all_checks();
      this.check_en = '1;
    endtask : enable_all_checks

    /// Disable all checks
    task disable_all_checks();
      this.check_en = '0;
    endtask : disable_all_checks

    /// Reset the monitor, clear internal memory and all queues, only call if there are no
    /// transactions in flight.
    task automatic reset();
      this.check_en = '0;
      this.memory_q.delete();
      assert(this.aw_sample.size() == 0);
      assert(this.w_sample.size()  == 0);
      for (int unsigned i = 0; i < 2**IW; i++) begin
        assert(this.b_sample[i].size()  == 0);
        assert(this.ar_sample[i].size() == 0);
        assert(this.r_sample[i].size()  == 0);
        assert(this.b_queue[i].size()   == 0);
      end
    endtask : reset
  endclass : axi_scoreboard

endpackage

// non synthesisable axi logger module
// this module logs the activity of the input axi channel
// the log files will be found in "./axi_log/<LoggerName>/"
// one log file for all writes
// a log file per id for the reads
// atomic transactions with read response are injected into the corresponding log file of the read
module axi_chan_logger #(
  parameter time TestTime     = 8ns,          // Time after clock, where sampling happens
  parameter string LoggerName = "axi_logger", // name of the logger
  parameter type aw_chan_t    = logic,        // axi AW type
  parameter type  w_chan_t    = logic,        // axi  W type
  parameter type  b_chan_t    = logic,        // axi  B type
  parameter type ar_chan_t    = logic,        // axi AR type
  parameter type  r_chan_t    = logic         // axi  R type
) (
  input logic     clk_i,     // Clock
  input logic     rst_ni,    // Asynchronous reset active low, when `1'b0` no sampling
  input logic     end_sim_i, // end of simulation
  // AW channel
  input aw_chan_t aw_chan_i,
  input logic     aw_valid_i,
  input logic     aw_ready_i,
  //  W channel
  input w_chan_t  w_chan_i,
  input logic     w_valid_i,
  input logic     w_ready_i,
  //  B channel
  input b_chan_t  b_chan_i,
  input logic     b_valid_i,
  input logic     b_ready_i,
  // AR channel
  input ar_chan_t ar_chan_i,
  input logic     ar_valid_i,
  input logic     ar_ready_i,
  //  R channel
  input r_chan_t  r_chan_i,
  input logic     r_valid_i,
  input logic     r_ready_i
);
  // id width from channel
  localparam int unsigned IdWidth = $bits(aw_chan_i.id);
  localparam int unsigned NoIds   = 2**IdWidth;

  // queues for writes and reads
  aw_chan_t aw_queue[$];
  w_chan_t  w_queue[$];
  b_chan_t  b_queue[$];
  aw_chan_t ar_queues[NoIds-1:0][$];
  r_chan_t  r_queues[NoIds-1:0][$];

  // channel sampling into queues
  always @(posedge clk_i) #TestTime begin : proc_channel_sample
    automatic aw_chan_t ar_beat;
    automatic int       fd;
    automatic string    log_file;
    automatic string    log_str;
    // only execute when reset is high
    if (rst_ni) begin
      // AW channel
      if (aw_valid_i && aw_ready_i) begin
        aw_queue.push_back(aw_chan_i);
        log_file = $sformatf("./axi_log/%s/write.log", LoggerName);
        fd = $fopen(log_file, "a");
        if (fd) begin
          log_str = $sformatf("%0t> ID: %h AW on channel: LEN: %d, ATOP: %b",
                        $time, aw_chan_i.id, aw_chan_i.len, aw_chan_i.atop);
          $fdisplay(fd, log_str);
          $fclose(fd);
        end

        // inject AR into queue, if there is an atomic
        if (aw_chan_i.atop[5]) begin
          $display("Atomic detected with response");
          ar_beat.id     = aw_chan_i.id;
          ar_beat.addr   = aw_chan_i.addr;
          if (aw_chan_i.len > 1) begin
            ar_beat.len    = aw_chan_i.len / 2;
          end else begin
            ar_beat.len    = aw_chan_i.len;
          end
          ar_beat.size   = aw_chan_i.size;
          ar_beat.burst  = aw_chan_i.burst;
          ar_beat.lock   = aw_chan_i.lock;
          ar_beat.cache  = aw_chan_i.cache;
          ar_beat.prot   = aw_chan_i.prot;
          ar_beat.qos    = aw_chan_i.qos;
          ar_beat.region = aw_chan_i.region;
          ar_beat.atop   = aw_chan_i.atop;
          ar_beat.user   = aw_chan_i.user;
          ar_queues[aw_chan_i.id].push_back(ar_beat);
          log_file = $sformatf("./axi_log/%s/read_%0h.log", LoggerName, aw_chan_i.id);
          fd = $fopen(log_file, "a");
          if (fd) begin
            log_str = $sformatf("%0t> ID: %h AR on channel: LEN: %d injected ATOP: %b",
                          $time, ar_beat.id, ar_beat.len, ar_beat.atop);
            $fdisplay(fd, log_str);
            $fclose(fd);
          end
        end
      end
      // W channel
      if (w_valid_i && w_ready_i) begin
        w_queue.push_back(w_chan_i);
      end
      // B channel
      if (b_valid_i && b_ready_i) begin
        b_queue.push_back(b_chan_i);
      end
      // AR channel
      if (ar_valid_i && ar_ready_i) begin
        log_file = $sformatf("./axi_log/%s/read_%0h.log", LoggerName, ar_chan_i.id);
        fd = $fopen(log_file, "a");
        if (fd) begin
          log_str = $sformatf("%0t> ID: %h AR on channel: LEN: %d",
                          $time, ar_chan_i.id, ar_chan_i.len);
          $fdisplay(fd, log_str);
          $fclose(fd);
        end
        ar_beat.id     = ar_chan_i.id;
        ar_beat.addr   = ar_chan_i.addr;
        ar_beat.len    = ar_chan_i.len;
        ar_beat.size   = ar_chan_i.size;
        ar_beat.burst  = ar_chan_i.burst;
        ar_beat.lock   = ar_chan_i.lock;
        ar_beat.cache  = ar_chan_i.cache;
        ar_beat.prot   = ar_chan_i.prot;
        ar_beat.qos    = ar_chan_i.qos;
        ar_beat.region = ar_chan_i.region;
        ar_beat.atop   = '0;
        ar_beat.user   = ar_chan_i.user;
        ar_queues[ar_chan_i.id].push_back(ar_beat);
      end
      // R channel
      if (r_valid_i && r_ready_i) begin
        r_queues[r_chan_i.id].push_back(r_chan_i);
      end
    end
  end

  initial begin : proc_log
    automatic string       log_name;
    automatic string       log_string;
    automatic aw_chan_t    aw_beat;
    automatic w_chan_t     w_beat;
    automatic int unsigned no_w_beat = 0;
    automatic b_chan_t     b_beat;
    automatic aw_chan_t    ar_beat;
    automatic r_chan_t     r_beat;
    automatic int unsigned no_r_beat[NoIds];
    automatic int          fd;

    // init r counter
    for (int unsigned i = 0; i < NoIds; i++) begin
      no_r_beat[i] = 0;
    end

    // make the log dirs
    log_name = $sformatf("mkdir -p ./axi_log/%s/", LoggerName);
    $system(log_name);

    // open log files
    log_name = $sformatf("./axi_log/%s/write.log", LoggerName);
    fd = $fopen(log_name, "w");
    if (fd) begin
      $display("File was opened successfully : %0d", fd);
      $fdisplay(fd, "This is the write log file");
      $fclose(fd);
    end else
      $display("File was NOT opened successfully : %0d", fd);
    for (int unsigned i = 0; i < NoIds; i++) begin
      log_name = $sformatf("./axi_log/%s/read_%0h.log", LoggerName, i);
      fd = $fopen(log_name, "w");
      if (fd) begin
        $display("File was opened successfully : %0d", fd);
        $fdisplay(fd, "This is the read log file for ID: %0h", i);
        $fclose(fd);
      end else
        $display("File was NOT opened successfully : %0d", fd);
    end

    // on each clock cycle update the logs if there is something in the queues
    wait (rst_ni);
    while (!end_sim_i) begin
      @(posedge clk_i);

      // update the write log file
      while (aw_queue.size() != 0 && w_queue.size() != 0) begin
        aw_beat = aw_queue[0];
        w_beat  = w_queue.pop_front();

        log_string = $sformatf("%0t> ID: %h W %d of %d, LAST: %b ATOP: %b",
                        $time, aw_beat.id, no_w_beat, aw_beat.len, w_beat.last, aw_beat.atop);

        log_name = $sformatf("./axi_log/%s/write.log", LoggerName);
        fd = $fopen(log_name, "a");
        if (fd) begin
          $fdisplay(fd, log_string);
          // write out error if last beat does not match!
          if (w_beat.last && !(aw_beat.len == no_w_beat)) begin
            $fdisplay(fd, "ERROR> Last flag was not expected!!!!!!!!!!!!!");
          end
          $fclose(fd);
        end
        // pop the AW if the last flag is set
        no_w_beat++;
        if (w_beat.last) begin
          aw_beat = aw_queue.pop_front();
          no_w_beat = 0;
        end
      end

      // check b queue
      if (b_queue.size() != 0) begin
        b_beat = b_queue.pop_front();
        log_string = $sformatf("%0t> ID: %h B recieved",
                        $time, b_beat.id);
        log_name = $sformatf("./axi_log/%s/write.log", LoggerName);
        fd = $fopen(log_name, "a");
        if (fd) begin
          $fdisplay(fd, log_string);
          $fclose(fd);
        end
      end

      // update the read log files
      for (int unsigned i = 0; i < NoIds; i++) begin
        while (ar_queues[i].size() != 0 && r_queues[i].size() != 0) begin
          ar_beat = ar_queues[i][0];
          r_beat  = r_queues[i].pop_front();

          log_name = $sformatf("./axi_log/%s/read_%0h.log", LoggerName, i);
          fd = $fopen(log_name, "a");
          if (fd) begin
            log_string = $sformatf("%0t> ID: %h R %d of %d, LAST: %b ATOP: %b",
                          $time, r_beat.id, no_r_beat[i], ar_beat.len, r_beat.last, ar_beat.atop);
            $fdisplay(fd, log_string);
            // write out error if last beat does not match!
            if (r_beat.last && !(ar_beat.len == no_r_beat[i])) begin
              $fdisplay(fd, "ERROR> Last flag was not expected!!!!!!!!!!!!!");
            end
            $fclose(fd);
          end
          no_r_beat[i]++;
          // pop the queue if it is the last flag
          if (r_beat.last) begin
            ar_beat = ar_queues[i].pop_front();
            no_r_beat[i] = 0;
          end
        end
      end
    end
    $fclose(fd);
  end
endmodule
