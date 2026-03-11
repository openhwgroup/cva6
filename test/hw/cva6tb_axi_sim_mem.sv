// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Simulated AXI4 memory, cycle-equivalent to axi_sim_mem but clocked
//
// axi_sim_mem drives its outputs ApplDelay after each rising edge and samples
// its inputs AcqDelay after it, with one timed process per channel. With
// --timing in Verilator, that costs several scheduler passes and coroutine
// wake-ups per cycle, even when the memory is idle. Here each rising edge first
// applies what axi_sim_mem would have sampled during the cycle that just ended
// (the handshakes, the master's values in that cycle), then registers what it
// would have driven in the cycle that starts. Since axi_sim_mem's outputs never
// depend combinationally on its inputs, the two are cycle-equivalent, with the
// same response timing:
//   - AW and AR are always ready and queued in order
//   - W is ready while a write address is queued; a burst's last beat queues
//     the B response, which is valid from the next cycle on
//   - an R beat is presented from the cycle after its AR handshake, read from
//     memory when presented, and held until accepted
// Monitor outputs and error injection are left out: the testbench uses neither.
// The memory is the same byte-addressed associative array, `mem`, so it is
// preloaded the same way.

`include "axi/typedef.svh"

module cva6tb_axi_sim_mem #(
  parameter int unsigned AddrWidth = 32'd0,
  parameter int unsigned DataWidth = 32'd0,
  parameter int unsigned IdWidth   = 32'd0,
  parameter int unsigned UserWidth = 32'd0,
  parameter type         axi_req_t = logic,
  parameter type         axi_rsp_t = logic,
  // Value read from bytes never written: "random", "zeros", "ones" or "undefined"
  parameter              UninitializedData = "undefined"
) (
  input  logic     clk_i,
  input  logic     rst_ni,
  input  axi_req_t axi_req_i,
  output axi_rsp_t axi_rsp_o
);

  localparam int unsigned StrbWidth = DataWidth / 8;
  typedef logic [AddrWidth-1:0] addr_t;
  typedef logic [DataWidth-1:0] data_t;
  typedef logic [IdWidth-1:0]   id_t;
  typedef logic [StrbWidth-1:0] strb_t;
  typedef logic [UserWidth-1:0] user_t;
  `AXI_TYPEDEF_AW_CHAN_T(aw_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(b_t, id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(ar_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(r_t, data_t, id_t, user_t)

  logic [7:0] mem[addr_t];

  aw_t aw_queue[$];
  ar_t ar_queue[$];
  b_t  b_queue[$];
  int unsigned w_cnt = 0;
  int unsigned r_cnt = 0;

  axi_rsp_t rsp_q = '0;
  assign axi_rsp_o = rsp_q;

  // Store one W beat of the burst at the head of the AW queue.
  function automatic void write_beat(w_t w);
    axi_pkg::burst_t burst = aw_queue[0].burst;
    axi_pkg::len_t   len   = aw_queue[0].len;
    axi_pkg::size_t  size  = aw_queue[0].size;
    addr_t addr = axi_pkg::beat_addr(aw_queue[0].addr, size, len, burst, w_cnt);
    for (int unsigned i_byte = axi_pkg::beat_lower_byte(aw_queue[0].addr, size, len, burst,
                                                        StrbWidth, w_cnt);
         i_byte <= axi_pkg::beat_upper_byte(aw_queue[0].addr, size, len, burst, StrbWidth, w_cnt);
         i_byte++) begin
      if (w.strb[i_byte]) mem[(addr / StrbWidth) * StrbWidth + i_byte] = w.data[i_byte*8+:8];
    end
  endfunction

  // The next R beat of the burst at the head of the AR queue.
  function automatic r_t read_beat();
    axi_pkg::burst_t burst = ar_queue[0].burst;
    axi_pkg::len_t   len   = ar_queue[0].len;
    axi_pkg::size_t  size  = ar_queue[0].size;
    addr_t addr = axi_pkg::beat_addr(ar_queue[0].addr, size, len, burst, r_cnt);
    r_t r = '0;
    r.data = 'x;
    r.id   = ar_queue[0].id;
    r.user = ar_queue[0].user;
    r.resp = axi_pkg::RESP_OKAY;
    r.last = (r_cnt == ar_queue[0].len);
    for (int unsigned i_byte = axi_pkg::beat_lower_byte(ar_queue[0].addr, size, len, burst,
                                                        StrbWidth, r_cnt);
         i_byte <= axi_pkg::beat_upper_byte(ar_queue[0].addr, size, len, burst, StrbWidth, r_cnt);
         i_byte++) begin
      addr_t byte_addr = (addr / StrbWidth) * StrbWidth + i_byte;
      if (mem.exists(byte_addr)) begin
        r.data[i_byte*8+:8] = mem[byte_addr];
      end else begin
        case (UninitializedData)
          "random": r.data[i_byte*8+:8] = 8'($urandom);
          "ones":   r.data[i_byte*8+:8] = '1;
          "zeros":  r.data[i_byte*8+:8] = '0;
          default:  r.data[i_byte*8+:8] = 'x;
        endcase
      end
    end
    return r;
  endfunction

  always @(posedge clk_i) begin
    if (rst_ni) begin
      automatic axi_rsp_t rsp    = rsp_q;
      automatic logic     r_hold = rsp_q.r_valid && !axi_req_i.r_ready;

      // The cycle that just ended: act on its handshakes.
      if (rsp_q.aw_ready && axi_req_i.aw_valid) aw_queue.push_back(axi_req_i.aw);
      if (rsp_q.w_ready && axi_req_i.w_valid) begin
        write_beat(axi_req_i.w);
        if (w_cnt == aw_queue[0].len) begin
          automatic b_t b = '0;
          assert (axi_req_i.w.last) else $error("Expected last beat of W burst!");
          b.id   = aw_queue[0].id;
          b.user = aw_queue[0].user;
          b.resp = axi_pkg::RESP_OKAY;
          b_queue.push_back(b);
          w_cnt = 0;
          void'(aw_queue.pop_front());
        end else begin
          assert (!axi_req_i.w.last) else $error("Did not expect last beat of W burst!");
          w_cnt++;
        end
      end
      if (rsp_q.b_valid && axi_req_i.b_ready) void'(b_queue.pop_front());
      if (rsp_q.ar_ready && axi_req_i.ar_valid) ar_queue.push_back(axi_req_i.ar);
      if (rsp_q.r_valid && axi_req_i.r_ready) begin
        if (rsp_q.r.last) begin
          r_cnt = 0;
          void'(ar_queue.pop_front());
        end else begin
          r_cnt++;
        end
      end

      // The cycle that starts: what to drive in it.
      rsp.aw_ready = 1'b1;
      rsp.ar_ready = 1'b1;
      rsp.w_ready  = (aw_queue.size() != 0);
      rsp.b_valid  = (b_queue.size() != 0);
      if (rsp.b_valid) rsp.b = b_queue[0];
      if (!r_hold) begin
        rsp.r_valid = (ar_queue.size() != 0);
        if (rsp.r_valid) rsp.r = read_beat();
      end
      rsp_q <= rsp;
    end
  end

endmodule
