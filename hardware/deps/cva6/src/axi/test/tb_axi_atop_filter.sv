// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

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
  parameter int unsigned N_TXNS = 10000
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

  axi_atop_filter #(
    .AXI_ID_WIDTH       (AXI_ID_WIDTH),
    .AXI_MAX_WRITE_TXNS (AXI_MAX_WRITE_TXNS)
  ) dut (
    .clk_i  (clk),
    .rst_ni (rst_n),
    .slv    (upstream),
    .mst    (downstream)
  );

  typedef axi_test::axi_driver #(
    .AW (AXI_ADDR_WIDTH),
    .DW (AXI_DATA_WIDTH),
    .IW (AXI_ID_WIDTH),
    .UW (AXI_USER_WIDTH),
    .TA (TA),
    .TT (TT)
  ) axi_driver_t;

  typedef rand_id_queue #(
    .data_t   (axi_driver_t::ax_beat_t),
    .ID_WIDTH (AXI_ID_WIDTH)
  ) rand_ax_beat_queue;

  typedef logic [AXI_ADDR_WIDTH-1:0]  axi_addr_t;
  typedef logic [AXI_ID_WIDTH-1:0]    axi_id_t;

  localparam axi_addr_t PFN_MASK = '{11: 1'b0, 10: 1'b0, 9: 1'b0, 8: 1'b0, 7: 1'b0, 6: 1'b0,
      5: 1'b0, 4: 1'b0, 3: 1'b0, 2: 1'b0, 1: 1'b0, 0: 1'b0, default: '1};

  task rand_req_wait();
    rand_wait(REQ_MIN_WAIT_CYCLES, REQ_MAX_WAIT_CYCLES, clk);
  endtask

  task rand_resp_wait();
    rand_wait(RESP_MIN_WAIT_CYCLES, RESP_MAX_WAIT_CYCLES, clk);
  endtask

  function axi_driver_t::ax_beat_t new_rand_burst();
    automatic int unsigned rand_success = 0;
    automatic axi_driver_t::ax_beat_t ax_beat = new;
    automatic axi_addr_t addr;
    automatic axi_pkg::burst_t burst;
    automatic axi_pkg::size_t size;
    // Randomly pick FIXED or INCR burst.  WRAP is currently not supported.
    rand_success = std::randomize(burst) with {
      burst <= axi_pkg::BURST_INCR;
    }; assert(rand_success);
    ax_beat.ax_burst = burst;
    // Randomize burst length.
    ax_beat.ax_len = $random();
    // Randomize beat size.
    rand_success = std::randomize(size) with {
      2**size <= AXI_STRB_WIDTH;
    }; assert(rand_success);
    ax_beat.ax_size = size;
    // Randomize address.  Make sure that the burst does not cross a 4KiB boundary.
    if (ax_beat.ax_burst == BURST_FIXED) begin
      forever begin
        rand_success = std::randomize(addr); assert(rand_success);
        if (((addr + 2**ax_beat.ax_size) & PFN_MASK) == (addr & PFN_MASK))
          break;
      end
      ax_beat.ax_addr = addr;
    end else begin // BURST_INCR
      forever begin
        rand_success = std::randomize(addr); assert(rand_success);
        if (((addr + 2**ax_beat.ax_size * (ax_beat.ax_len + 1)) & PFN_MASK) == (addr & PFN_MASK))
          break;
      end
      ax_beat.ax_addr = addr;
    end
    return ax_beat;
  endfunction

  // AXI Master
  logic mst_done = 1'b0;
  axi_driver_t axi_master = new(upstream_dv);
  // TODO: Is it possible to move such a master driver as class to `axi_test`?
  initial begin
    static axi_driver_t::ax_beat_t aw_queue[$];
    static int unsigned atop_flight_cnt[NUM_AXI_IDS-1:0],
                        r_flight_cnt[NUM_AXI_IDS-1:0],
                        w_flight_cnt[NUM_AXI_IDS-1:0],
                        tot_atop_flight_cnt = 0,
                        tot_r_flight_cnt = 0,
                        tot_w_flight_cnt = 0;
    static logic  ar_done = 1'b0,
                  aw_done = 1'b0;
    static semaphore cnt_sem = new(1);
    axi_master.reset_master();
    for (int unsigned i = 0; i < NUM_AXI_IDS; i++) begin
      atop_flight_cnt[i] = 0;
      r_flight_cnt[i] = 0;
      w_flight_cnt[i] = 0;
    end
    wait (rst_n);
    fork
      // AR
      begin
        repeat (N_TXNS) begin
          automatic axi_driver_t::ax_beat_t ar_beat = new_rand_burst();
          static int unsigned rand_success;
          automatic axi_id_t id;
          while (tot_r_flight_cnt >= AXI_MAX_READ_TXNS) begin
            @(posedge clk);
          end
          // The ID must not be the same as that of any in-flight ATOP.
          cnt_sem.get();
          do begin
            rand_success = std::randomize(id); assert(rand_success);
          end while (atop_flight_cnt[id] != 0);
          ar_beat.ax_id = id;
          r_flight_cnt[ar_beat.ax_id]++;
          tot_r_flight_cnt++;
          cnt_sem.put();
          rand_req_wait();
          axi_master.send_ar(ar_beat);
        end
        ar_done = 1'b1;
      end
      // R
      while (!(ar_done && tot_r_flight_cnt == 0 && aw_done && tot_atop_flight_cnt == 0)) begin
        automatic axi_driver_t::r_beat_t r_beat;
        rand_resp_wait();
        axi_master.recv_r(r_beat);
        if (r_beat.r_last) begin
          cnt_sem.get();
          if (r_beat.r_resp == RESP_OKAY) begin
            r_flight_cnt[r_beat.r_id]--;
            tot_r_flight_cnt--;
          end
          cnt_sem.put();
        end
      end
      // AW
      begin
        repeat (N_TXNS) begin
          automatic axi_driver_t::ax_beat_t aw_beat = new_rand_burst();
          static int unsigned rand_success = 0;
          automatic axi_id_t id;
          while (tot_w_flight_cnt >= AXI_MAX_WRITE_TXNS
              || tot_atop_flight_cnt >= AXI_MAX_WRITE_TXNS) begin
            @(posedge clk);
          end
          aw_beat.ax_atop[5:4] = $random();
          if (aw_beat.ax_atop[5:4] != 2'b00) begin // ATOP
            // Determine `ax_atop`.
            if (aw_beat.ax_atop[5:4] == ATOP_ATOMICSTORE ||
                aw_beat.ax_atop[5:4] == ATOP_ATOMICLOAD) begin
              // Endianness
              aw_beat.ax_atop[3] = $random();
              // Atomic operation
              aw_beat.ax_atop[2:0] = $random();
            end else begin // Atomic{Swap,Compare}
              aw_beat.ax_atop[3:1] = '0;
              aw_beat.ax_atop[0] = $random();
            end
            // Determine `ax_size` and `ax_len`.
            if (2**aw_beat.ax_size < AXI_STRB_WIDTH) begin
              // Transaction does *not* occupy full data bus, so we must send just one beat. [E2.1.3]
              aw_beat.ax_len = '0;
            end else begin
              automatic int unsigned bytes;
              if (aw_beat.ax_atop == ATOP_ATOMICCMP) begin
                // Total data transferred in burst can be 2, 4, 8, 16, or 32 B.
                automatic int unsigned log_bytes;
                rand_success = std::randomize(log_bytes) with {
                  log_bytes > 0; 2**log_bytes >= AXI_STRB_WIDTH; 2**log_bytes <= 32;
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
              aw_beat.ax_len = bytes / AXI_STRB_WIDTH - 1;
            end
            // Determine `ax_addr`.
            if (aw_beat.ax_atop == ATOP_ATOMICCMP) begin
              // The address must be aligned to half the outbound data size. [E2-337]
              aw_beat.ax_addr = aw_beat.ax_addr & ~(1<<aw_beat.ax_size - 1);
            end else begin
              // The address must be aligned to the data size. [E2-337]
              aw_beat.ax_addr = aw_beat.ax_addr & ~(1<<(aw_beat.ax_size+1) - 1);
            end
            // Determine `ax_burst`.
            if (aw_beat.ax_atop == ATOP_ATOMICCMP) begin
              // If the address is aligned to the total size of outgoing data, the burst type must be
              // INCR. Otherwise, it must be WRAP. [E2-338]
              aw_beat.ax_burst = (aw_beat.ax_addr % ((aw_beat.ax_len+1) * 2**aw_beat.ax_size) == 0) ?
                  BURST_INCR : BURST_WRAP;
            end else begin
              // Only INCR allowed.
              aw_beat.ax_burst = BURST_INCR;
            end
            // Determine `ax_id`, which must not be the same as that of any other in-flight AXI
            // transaction.
            cnt_sem.get();
            do begin
              rand_success = std::randomize(id); assert(rand_success);
            end while (atop_flight_cnt[id] != 0 || r_flight_cnt[id] != 0 || w_flight_cnt[id] != 0);
          end else begin
            // Determine `ax_id`, which must not be the same as that of any in-flight ATOP.
            cnt_sem.get();
            do begin
              rand_success = std::randomize(id); assert(rand_success);
            end while (atop_flight_cnt[id] != 0);
          end
          aw_beat.ax_id = id;
          // Add AW to queue and put it in flight.
          aw_queue.push_back(aw_beat);
          if (aw_beat.ax_atop == '0) begin
            w_flight_cnt[aw_beat.ax_id]++;
            tot_w_flight_cnt++;
          end else begin
            atop_flight_cnt[aw_beat.ax_id]++;
            tot_atop_flight_cnt++;
          end
          cnt_sem.put();
          rand_req_wait();
          axi_master.send_aw(aw_beat);
        end
        aw_done = 1'b1;
      end
      // W
      while (!(aw_done && aw_queue.size() == 0)) begin
        automatic axi_driver_t::ax_beat_t aw_beat;
        automatic axi_addr_t addr;
        static int unsigned rand_success = 0;
        wait (aw_queue.size() > 0);
        aw_beat = aw_queue.pop_front();
        addr = aw_beat.ax_addr;
        for (int unsigned i = 0; i < aw_beat.ax_len + 1; i++) begin
          automatic axi_driver_t::w_beat_t w_beat = new;
          int unsigned begin_byte, n_bytes;
          logic [AXI_STRB_WIDTH-1:0] rand_strb, strb_mask;
          rand_success = std::randomize(w_beat); assert (rand_success);
          // Determine strobe.
          w_beat.w_strb = '0;
          n_bytes = 2**aw_beat.ax_size;
          begin_byte = addr % AXI_STRB_WIDTH;
          strb_mask = ((1'b1 << n_bytes) - 1) << begin_byte;
          rand_strb = $random();
          w_beat.w_strb |= (rand_strb & strb_mask);
          // Determine last.
          w_beat.w_last = (i == aw_beat.ax_len);
          rand_req_wait();
          axi_master.send_w(w_beat);
          if (aw_beat.ax_burst == BURST_INCR)
            addr += n_bytes;
        end
      end
      // B
      while (!(aw_done && tot_atop_flight_cnt == 0 && tot_w_flight_cnt == 0)) begin
        automatic axi_driver_t::b_beat_t b_beat;
        rand_resp_wait();
        axi_master.recv_b(b_beat);
        cnt_sem.get();
        if (b_beat.b_resp == RESP_SLVERR) begin
          atop_flight_cnt[b_beat.b_id]--;
          tot_atop_flight_cnt--;
        end else begin
          w_flight_cnt[b_beat.b_id]--;
          tot_w_flight_cnt--;
        end
        cnt_sem.put();
      end
    join
    mst_done = 1'b1;
  end

  initial begin
    wait (mst_done);
    $finish();
  end

  // AXI Slave
  axi_driver_t axi_slave = new(downstream_dv);
  // TODO: Is it possible to move such a slave driver as class to `axi_test`?
  initial begin
    static rand_ax_beat_queue       ar_queue = new;
    static axi_driver_t::ax_beat_t  aw_queue[$];
    static rand_ax_beat_queue       b_queue = new;
    axi_slave.reset_slave();
    wait (rst_n);
    fork
      // AR
      forever begin
        automatic axi_driver_t::ax_beat_t ar_beat;
        rand_resp_wait();
        axi_slave.recv_ar(ar_beat);
        ar_queue.push(ar_beat.ax_id, ar_beat);
      end
      // R
      forever begin
        automatic axi_driver_t::ax_beat_t ar_beat;
        automatic axi_driver_t::r_beat_t r_beat = new;
        wait (!ar_queue.empty());
        ar_beat = ar_queue.peek();
        void'(std::randomize(r_beat));
        r_beat.r_id = ar_beat.ax_id;
        rand_resp_wait();
        if (ar_beat.ax_len == '0) begin
          r_beat.r_last = 1'b1;
          void'(ar_queue.pop_id(ar_beat.ax_id));
        end else begin
          ar_beat.ax_len--;
          ar_queue.set(ar_beat.ax_id, ar_beat);
        end
        axi_slave.send_r(r_beat);
      end
      // AW
      forever begin
        automatic axi_driver_t::ax_beat_t aw_beat;
        rand_resp_wait();
        axi_slave.recv_aw(aw_beat);
        aw_queue.push_back(aw_beat);
      end
      // W
      forever begin
        automatic axi_driver_t::ax_beat_t aw_beat;
        forever begin
          automatic axi_driver_t::w_beat_t w_beat;
          rand_resp_wait();
          axi_slave.recv_w(w_beat);
          if (w_beat.w_last)
            break;
        end
        wait (aw_queue.size() > 0);
        aw_beat = aw_queue.pop_front();
        b_queue.push(aw_beat.ax_id, aw_beat);
      end
      // B
      forever begin
        automatic axi_driver_t::ax_beat_t aw_beat;
        automatic axi_driver_t::b_beat_t b_beat = new;
        wait (!b_queue.empty());
        aw_beat = b_queue.pop();
        void'(std::randomize(b_beat));
        b_beat.b_id = aw_beat.ax_id;
        rand_resp_wait();
        axi_slave.send_b(b_beat);
      end
    join
  end

  typedef struct packed {
    axi_id_t  id;
    logic     thru;
  } w_cmd_t;

  // Monitor and check responses of filter.
  initial begin
    static axi_driver_t::ax_beat_t  ar_xfer_queue[$],
                                    aw_xfer_queue[$];
    static axi_driver_t::b_beat_t   b_inject_queue[$],
                                    b_xfer_queue[$];
    static axi_driver_t::r_beat_t   r_inject_queue[$],
                                    r_xfer_queue[$];
    static w_cmd_t                  w_cmd_queue[$];
    static axi_driver_t::w_beat_t   w_xfer_queue[$];
    forever begin
      @(posedge clk);
      #(TT);
      // Ensure that downstream never sees an `aw_atop`.
      if (downstream.aw_valid) begin
        assert (downstream.aw_atop == '0);
      end
      // Push upstream ARs into transfer queues.
      if (upstream.ar_valid && upstream.ar_ready) begin
        automatic axi_driver_t::ax_beat_t ar_beat = new;
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
        automatic axi_driver_t::ax_beat_t aw_beat = new;
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
            automatic axi_driver_t::r_beat_t r_beat = new;
            r_beat.r_id = aw_beat.ax_id;
            r_beat.r_resp = RESP_SLVERR;
            r_beat.r_data = '0;
            r_beat.r_user = '0;
            r_beat.r_last = (i == aw_beat.ax_len);
            r_inject_queue.push_back(r_beat);
          end
        end
      end
      // Push upstream Ws that must go through into transfer queue; push to B and R inject queue for
      // completed W bursts that must not go through.
      if (upstream.w_valid && upstream.w_ready) begin
        automatic axi_driver_t::w_beat_t w_beat = new;
        automatic w_cmd_t w_cmd;
        w_beat.w_data = upstream.w_data;
        w_beat.w_strb = upstream.w_strb;
        w_beat.w_last = upstream.w_last;
        w_beat.w_user = upstream.w_user;
        assert (w_cmd_queue.size() > 0) else $fatal("upstream.W: Undecided beat!");
        w_cmd = w_cmd_queue[0];
        if (w_cmd.thru) begin
          w_xfer_queue.push_back(w_beat);
        end
        if (w_beat.w_last) begin
          if (!w_cmd.thru) begin
            automatic axi_driver_t::b_beat_t b_beat = new;
            b_beat.b_id = w_cmd.id;
            b_beat.b_resp = RESP_SLVERR;
            b_inject_queue.push_back(b_beat);
          end
          void'(w_cmd_queue.pop_front());
        end
      end
      // Push downstream Rs into transfer queue.
      if (downstream.r_valid && downstream.r_ready) begin
        automatic axi_driver_t::r_beat_t r_beat = new;
        r_beat.r_id   = downstream.r_id;
        r_beat.r_data = downstream.r_data;
        r_beat.r_resp = downstream.r_resp;
        r_beat.r_last = downstream.r_last;
        r_beat.r_user = downstream.r_user;
        r_xfer_queue.push_back(r_beat);
      end
      // Push downstream Bs into transfer queue.
      if (downstream.b_valid && downstream.b_ready) begin
        automatic axi_driver_t::b_beat_t b_beat = new;
        b_beat.b_id   = downstream.b_id;
        b_beat.b_resp = downstream.b_resp;
        b_beat.b_user = downstream.b_user;
        b_xfer_queue.push_back(b_beat);
      end
      // Ensure downstream ARs match beats from transfer queue.
      if (downstream.ar_valid && downstream.ar_ready) begin
        automatic axi_driver_t::ax_beat_t exp_beat;
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
        automatic axi_driver_t::ax_beat_t exp_beat;
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
      if (downstream.w_valid && downstream.w_ready) begin
        automatic axi_driver_t::w_beat_t exp_beat;
        assert (w_xfer_queue.size() > 0) else $fatal(1, "downstream.W: Unknown beat!");
        exp_beat = w_xfer_queue.pop_front();
        assert (downstream.w_data == exp_beat.w_data);
        assert (downstream.w_strb == exp_beat.w_strb);
        assert (downstream.w_last == exp_beat.w_last);
        assert (downstream.w_user == exp_beat.w_user);
      end
      // Ensure upstream Rs match beats from transfer or inject queue.
      if (upstream.r_valid && upstream.r_ready) begin
        automatic axi_driver_t::r_beat_t exp_beat;
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
        automatic axi_driver_t::b_beat_t exp_beat;
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
