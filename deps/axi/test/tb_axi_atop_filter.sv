// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Author:
// Andreas Kurth  <akurth@iis.ee.ethz.ch>

// Testbench for axi_atop_filter

`include "axi/assign.svh"

import axi_pkg::ATOP_ATOMICCMP;
import axi_pkg::ATOP_ATOMICLOAD;
import axi_pkg::ATOP_ATOMICSTORE;
import axi_pkg::BURST_FIXED;
import axi_pkg::BURST_INCR;
import axi_pkg::BURST_WRAP;
import axi_pkg::RESP_OKAY;
import axi_pkg::RESP_SLVERR;
import rand_id_queue_pkg::rand_id_queue;
import rand_verif_pkg::rand_wait;

module tb_axi_atop_filter #(
  // AXI Parameters
  parameter int unsigned AXI_ADDR_WIDTH = 32,
  parameter int unsigned AXI_DATA_WIDTH = 64,
  parameter int unsigned AXI_ID_WIDTH = 4,
  parameter int unsigned AXI_USER_WIDTH = 2,
  parameter int unsigned AXI_MAX_READ_TXNS = 10,
  parameter int unsigned AXI_MAX_WRITE_TXNS = 12,
  // TB Parameters
  parameter time TCLK = 10ns,
  parameter time TA = TCLK * 1/4,
  parameter time TT = TCLK * 3/4,
  parameter int unsigned REQ_MIN_WAIT_CYCLES = 0,
  parameter int unsigned REQ_MAX_WAIT_CYCLES = 10,
  parameter int unsigned RESP_MIN_WAIT_CYCLES = 0,
  parameter int unsigned RESP_MAX_WAIT_CYCLES = REQ_MAX_WAIT_CYCLES/2,
  parameter int unsigned N_TXNS = 1000
);

  timeunit 1ns;
  timeprecision 10ps;

  localparam int unsigned AXI_STRB_WIDTH  = AXI_DATA_WIDTH / 8;
  localparam int unsigned NUM_AXI_IDS     = 2**AXI_ID_WIDTH;

  logic clk,
        rst_n;

  clk_rst_gen #(
    .CLK_PERIOD     (TCLK),
    .RST_CLK_CYCLES (5)
  ) i_clk_rst_gen (
    .clk_o  (clk),
    .rst_no (rst_n)
  );

  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH (AXI_ADDR_WIDTH),
    .AXI_DATA_WIDTH (AXI_DATA_WIDTH),
    .AXI_ID_WIDTH   (AXI_ID_WIDTH),
    .AXI_USER_WIDTH (AXI_USER_WIDTH)
  ) upstream_dv (
    .clk_i  (clk)
  );

  AXI_BUS #(
    .AXI_ADDR_WIDTH (AXI_ADDR_WIDTH),
    .AXI_DATA_WIDTH (AXI_DATA_WIDTH),
    .AXI_ID_WIDTH   (AXI_ID_WIDTH),
    .AXI_USER_WIDTH (AXI_USER_WIDTH)
  ) upstream ();

  `AXI_ASSIGN(upstream, upstream_dv);

  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH (AXI_ADDR_WIDTH),
    .AXI_DATA_WIDTH (AXI_DATA_WIDTH),
    .AXI_ID_WIDTH   (AXI_ID_WIDTH),
    .AXI_USER_WIDTH (AXI_USER_WIDTH)
  ) downstream_dv (
    .clk_i  (clk)
  );

  AXI_BUS #(
    .AXI_ADDR_WIDTH (AXI_ADDR_WIDTH),
    .AXI_DATA_WIDTH (AXI_DATA_WIDTH),
    .AXI_ID_WIDTH   (AXI_ID_WIDTH),
    .AXI_USER_WIDTH (AXI_USER_WIDTH)
  ) downstream ();

  `AXI_ASSIGN(downstream_dv, downstream);

  axi_atop_filter_intf #(
    .AXI_ID_WIDTH       (AXI_ID_WIDTH),
    .AXI_MAX_WRITE_TXNS (AXI_MAX_WRITE_TXNS),
    .AXI_ADDR_WIDTH     (AXI_ADDR_WIDTH),
    .AXI_DATA_WIDTH     (AXI_DATA_WIDTH),
    .AXI_USER_WIDTH     (AXI_USER_WIDTH)
  ) dut (
    .clk_i  (clk),
    .rst_ni (rst_n),
    .slv    (upstream),
    .mst    (downstream)
  );

  typedef logic [AXI_ID_WIDTH-1:0]  axi_id_t;

  // AXI Master
  logic mst_done = 1'b0;
  axi_test::rand_axi_master #(
    .AW(AXI_ADDR_WIDTH), .DW(AXI_DATA_WIDTH), .IW(AXI_ID_WIDTH), .UW(AXI_USER_WIDTH),
    .TA(TA), .TT(TT),
    .MAX_READ_TXNS        (AXI_MAX_READ_TXNS),
    .MAX_WRITE_TXNS       (AXI_MAX_WRITE_TXNS),
    .AX_MIN_WAIT_CYCLES   (REQ_MIN_WAIT_CYCLES),
    .AX_MAX_WAIT_CYCLES   (REQ_MAX_WAIT_CYCLES),
    .W_MIN_WAIT_CYCLES    (REQ_MIN_WAIT_CYCLES),
    .W_MAX_WAIT_CYCLES    (REQ_MAX_WAIT_CYCLES),
    .RESP_MIN_WAIT_CYCLES (RESP_MIN_WAIT_CYCLES),
    .RESP_MAX_WAIT_CYCLES (RESP_MAX_WAIT_CYCLES),
    .AXI_ATOPS            (1'b1)
  ) axi_master = new(upstream_dv);
  initial begin
    axi_master.reset();
    wait(rst_n);
    axi_master.add_memory_region({AXI_ADDR_WIDTH{1'b0}}, {AXI_ADDR_WIDTH{1'b1}}, axi_pkg::WTHRU_NOALLOCATE);
    axi_master.run(N_TXNS, N_TXNS);
    mst_done = 1'b1;
  end

  initial begin
    wait (mst_done);
    $finish();
  end

  // AXI Slave
  axi_test::rand_axi_slave #(
    .AW(AXI_ADDR_WIDTH), .DW(AXI_DATA_WIDTH), .IW(AXI_ID_WIDTH), .UW(AXI_USER_WIDTH),
    .TA(TA), .TT(TT),
    .AX_MIN_WAIT_CYCLES   (RESP_MIN_WAIT_CYCLES),
    .AX_MAX_WAIT_CYCLES   (RESP_MAX_WAIT_CYCLES),
    .R_MIN_WAIT_CYCLES    (RESP_MIN_WAIT_CYCLES),
    .R_MAX_WAIT_CYCLES    (RESP_MAX_WAIT_CYCLES),
    .RESP_MIN_WAIT_CYCLES (RESP_MIN_WAIT_CYCLES),
    .RESP_MAX_WAIT_CYCLES (RESP_MAX_WAIT_CYCLES)
  ) axi_slave = new(downstream_dv);
  initial begin
    axi_slave.reset();
    wait (rst_n);
    axi_slave.run();
  end

  typedef struct packed {
    axi_id_t  id;
    logic     thru;
  } w_cmd_t;

  typedef axi_test::axi_ax_beat #(
    .AW(AXI_ADDR_WIDTH), .IW(AXI_ID_WIDTH), .UW(AXI_USER_WIDTH)
  ) ax_beat_t;
  typedef axi_test::axi_b_beat #(
    .IW(AXI_ID_WIDTH), .UW(AXI_USER_WIDTH)
  ) b_beat_t;
  typedef axi_test::axi_r_beat #(
    .DW(AXI_DATA_WIDTH), .IW(AXI_ID_WIDTH), .UW(AXI_USER_WIDTH)
  ) r_beat_t;
  typedef axi_test::axi_w_beat #(
    .DW(AXI_DATA_WIDTH), .UW(AXI_USER_WIDTH)
  ) w_beat_t;

  // Put W beats into transfer queue or drop them and inject B responses based on W command.
  function automatic void process_w_beat(w_beat_t w_beat, ref w_cmd_t w_cmd_queue[$],
      ref w_beat_t w_xfer_queue[$], ref b_beat_t b_inject_queue[$]
  );
    w_cmd_t w_cmd = w_cmd_queue[0];
    if (w_cmd.thru) begin
      w_xfer_queue.push_back(w_beat);
    end
    if (w_beat.w_last) begin
      if (!w_cmd.thru) begin
        automatic b_beat_t b_beat = new;
        b_beat.b_id = w_cmd.id;
        b_beat.b_resp = RESP_SLVERR;
        b_inject_queue.push_back(b_beat);
      end
      void'(w_cmd_queue.pop_front());
    end
  endfunction

  // Monitor and check responses of filter.
  initial begin
    static ax_beat_t  ar_xfer_queue[$],
                      aw_xfer_queue[$];
    static b_beat_t   b_inject_queue[$],
                      b_xfer_queue[$];
    static r_beat_t   r_inject_queue[$],
                      r_xfer_queue[$];
    static w_cmd_t    w_cmd_queue[$];
    static w_beat_t   w_act_queue[$],
                      w_undecided_queue[$],
                      w_xfer_queue[$];
    forever begin
      @(posedge clk);
      #(TT);
      // Ensure that downstream never sees an `aw_atop`.
      if (downstream.aw_valid) begin
        assert (downstream.aw_atop == '0);
      end
      // Push upstream ARs into transfer queues.
      if (upstream.ar_valid && upstream.ar_ready) begin
        automatic ax_beat_t ar_beat = new;
        ar_beat.ax_id     = upstream.ar_id;
        ar_beat.ax_addr   = upstream.ar_addr;
        ar_beat.ax_len    = upstream.ar_len;
        ar_beat.ax_size   = upstream.ar_size;
        ar_beat.ax_burst  = upstream.ar_burst;
        ar_beat.ax_lock   = upstream.ar_lock;
        ar_beat.ax_cache  = upstream.ar_cache;
        ar_beat.ax_prot   = upstream.ar_prot;
        ar_beat.ax_qos    = upstream.ar_qos;
        ar_beat.ax_region = upstream.ar_region;
        ar_beat.ax_user   = upstream.ar_user;
        ar_xfer_queue.push_back(ar_beat);
      end
      // Push upstream AWs that must go through into transfer queues, and push to W command queue.
      if (upstream.aw_valid && upstream.aw_ready) begin
        automatic ax_beat_t aw_beat = new;
        automatic w_cmd_t w_cmd;
        aw_beat.ax_id     = upstream.aw_id;
        aw_beat.ax_addr   = upstream.aw_addr;
        aw_beat.ax_len    = upstream.aw_len;
        aw_beat.ax_size   = upstream.aw_size;
        aw_beat.ax_burst  = upstream.aw_burst;
        aw_beat.ax_lock   = upstream.aw_lock;
        aw_beat.ax_cache  = upstream.aw_cache;
        aw_beat.ax_prot   = upstream.aw_prot;
        aw_beat.ax_qos    = upstream.aw_qos;
        aw_beat.ax_region = upstream.aw_region;
        aw_beat.ax_atop   = upstream.aw_atop;
        aw_beat.ax_user   = upstream.aw_user;
        w_cmd.id = aw_beat.ax_id;
        w_cmd.thru = (aw_beat.ax_atop == '0);
        w_cmd_queue.push_back(w_cmd);
        if (w_cmd.thru) begin
          aw_xfer_queue.push_back(aw_beat);
        end else if (aw_beat.ax_atop[5:4] != ATOP_ATOMICSTORE) begin
          for (int unsigned i = 0; i < aw_beat.ax_len + 1; i++) begin
            automatic r_beat_t r_beat = new;
            r_beat.r_id = aw_beat.ax_id;
            r_beat.r_resp = RESP_SLVERR;
            r_beat.r_data = '0;
            r_beat.r_user = '0;
            r_beat.r_last = (i == aw_beat.ax_len);
            r_inject_queue.push_back(r_beat);
          end
        end
      end
      // Handle undecided upstream W beats if possible.
      while (w_undecided_queue.size() > 0 && w_cmd_queue.size() > 0) begin
        automatic w_beat_t w_beat = w_undecided_queue.pop_front();
        process_w_beat(w_beat, w_cmd_queue, w_xfer_queue, b_inject_queue);
      end
      // Process upstream W beats or put them into queue of undecided W beats.
      if (upstream.w_valid && upstream.w_ready) begin
        automatic w_beat_t w_beat = new;
        w_beat.w_data = upstream.w_data;
        w_beat.w_strb = upstream.w_strb;
        w_beat.w_last = upstream.w_last;
        w_beat.w_user = upstream.w_user;
        if (w_cmd_queue.size() > 0) begin
          process_w_beat(w_beat, w_cmd_queue, w_xfer_queue, b_inject_queue);
        end else begin
          w_undecided_queue.push_back(w_beat);
        end
      end
      // Push downstream Rs into transfer queue.
      if (downstream.r_valid && downstream.r_ready) begin
        automatic r_beat_t r_beat = new;
        r_beat.r_id   = downstream.r_id;
        r_beat.r_data = downstream.r_data;
        r_beat.r_resp = downstream.r_resp;
        r_beat.r_last = downstream.r_last;
        r_beat.r_user = downstream.r_user;
        r_xfer_queue.push_back(r_beat);
      end
      // Push downstream Bs into transfer queue.
      if (downstream.b_valid && downstream.b_ready) begin
        automatic b_beat_t b_beat = new;
        b_beat.b_id   = downstream.b_id;
        b_beat.b_resp = downstream.b_resp;
        b_beat.b_user = downstream.b_user;
        b_xfer_queue.push_back(b_beat);
      end
      // Ensure downstream ARs match beats from transfer queue.
      if (downstream.ar_valid && downstream.ar_ready) begin
        automatic ax_beat_t exp_beat;
        assert (ar_xfer_queue.size() > 0) else $fatal(1, "downstream.AR: Unknown beat!");
        exp_beat = ar_xfer_queue.pop_front();
        assert (downstream.ar_id      == exp_beat.ax_id);
        assert (downstream.ar_addr    == exp_beat.ax_addr);
        assert (downstream.ar_len     == exp_beat.ax_len);
        assert (downstream.ar_size    == exp_beat.ax_size);
        assert (downstream.ar_burst   == exp_beat.ax_burst);
        assert (downstream.ar_cache   == exp_beat.ax_cache);
        assert (downstream.ar_prot    == exp_beat.ax_prot);
        assert (downstream.ar_qos     == exp_beat.ax_qos);
        assert (downstream.ar_region  == exp_beat.ax_region);
        assert (downstream.ar_user    == exp_beat.ax_user);
      end
      // Ensure downstream AWs match beats from transfer queue.
      if (downstream.aw_valid && downstream.aw_ready) begin
        automatic ax_beat_t exp_beat;
        assert (aw_xfer_queue.size() > 0) else $fatal(1, "downstream.AW: Unknown beat!");
        exp_beat = aw_xfer_queue.pop_front();
        assert (downstream.aw_id      == exp_beat.ax_id);
        assert (downstream.aw_addr    == exp_beat.ax_addr);
        assert (downstream.aw_len     == exp_beat.ax_len);
        assert (downstream.aw_size    == exp_beat.ax_size);
        assert (downstream.aw_burst   == exp_beat.ax_burst);
        assert (downstream.aw_cache   == exp_beat.ax_cache);
        assert (downstream.aw_prot    == exp_beat.ax_prot);
        assert (downstream.aw_qos     == exp_beat.ax_qos);
        assert (downstream.aw_region  == exp_beat.ax_region);
        assert (downstream.aw_user    == exp_beat.ax_user);
      end
      // Ensure downstream Ws match beats from transfer queue.
      while (w_act_queue.size() > 0 && w_xfer_queue.size() > 0) begin
        automatic w_beat_t exp_beat = w_xfer_queue.pop_front();
        automatic w_beat_t act_beat = w_act_queue.pop_front();
        assert (act_beat.w_data == exp_beat.w_data);
        assert (act_beat.w_strb == exp_beat.w_strb);
        assert (act_beat.w_last == exp_beat.w_last);
        assert (act_beat.w_user == exp_beat.w_user);
      end
      if (downstream.w_valid && downstream.w_ready) begin
        if (w_xfer_queue.size() > 0) begin
          automatic w_beat_t exp_beat = w_xfer_queue.pop_front();
          assert (downstream.w_data == exp_beat.w_data);
          assert (downstream.w_strb == exp_beat.w_strb);
          assert (downstream.w_last == exp_beat.w_last);
          assert (downstream.w_user == exp_beat.w_user);
        end else begin
          automatic w_beat_t act_beat = new;
          act_beat.w_data = downstream.w_data;
          act_beat.w_strb = downstream.w_strb;
          act_beat.w_last = downstream.w_last;
          act_beat.w_user = downstream.w_user;
          w_act_queue.push_back(act_beat);
        end
      end
      // Ensure upstream Rs match beats from transfer or inject queue.
      if (upstream.r_valid && upstream.r_ready) begin
        automatic r_beat_t exp_beat;
        if (r_inject_queue.size() > 0 && r_inject_queue[0].r_id == upstream.r_id) begin
          exp_beat = r_inject_queue.pop_front();
        end else if (r_xfer_queue.size() > 0 && r_xfer_queue[0].r_id == upstream.r_id) begin
          exp_beat = r_xfer_queue.pop_front();
        end else begin
          $fatal(1, "upstream.R: Unknown beat!");
        end
        assert (upstream.r_id   == exp_beat.r_id);
        assert (upstream.r_data == exp_beat.r_data);
        assert (upstream.r_resp == exp_beat.r_resp);
        assert (upstream.r_last == exp_beat.r_last);
        assert (upstream.r_user == exp_beat.r_user);
      end
      // Ensure upstream Bs match beats from transfer or inject queue.
      if (upstream.b_valid && upstream.b_ready) begin
        automatic b_beat_t exp_beat;
        if (b_inject_queue.size() > 0 && b_inject_queue[0].b_id == upstream.b_id) begin
          exp_beat = b_inject_queue.pop_front();
        end else if (b_xfer_queue.size() > 0 && b_xfer_queue[0].b_id == upstream.b_id) begin
          exp_beat = b_xfer_queue.pop_front();
        end else begin
          $fatal(1, "upstream.B: Unknown beat!");
        end
        assert (upstream.b_id   == exp_beat.b_id);
        assert (upstream.b_resp == exp_beat.b_resp);
        assert (upstream.b_user == exp_beat.b_user);
      end
    end
  end

endmodule
