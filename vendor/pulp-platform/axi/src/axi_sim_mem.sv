// Copyright (c) 2020 ETH Zurich and University of Bologna
// SPDX-License-Identifier: SHL-0.51
//
// Authors:
// - Andreas Kurth <akurth@iis.ee.ethz.ch>

`include "axi/typedef.svh"

/// Infinite (Simulation-Only) Memory with AXI Slave Port
///
/// The memory array is named `mem`, and it is *not* initialized or reset.  This makes it possible to
/// load the memory of this module in simulation with an external `$readmem*` command, e.g.,
/// ```sv
/// axi_sim_mem #( ... ) i_sim_mem ( ... );
/// initial begin
///   $readmemh("file_with_memory_addrs_and_data.mem", i_sim_mem.mem);
/// end
/// ```
/// `mem` is addressed (or indexed) byte-wise with `AddrWidth`-wide addresses.
///
/// This module does not support atomic operations (ATOPs).
module axi_sim_mem #(
  /// AXI Address Width
  parameter int unsigned AddrWidth = 32'd0,
  /// AXI Data Width
  parameter int unsigned DataWidth = 32'd0,
  /// AXI ID Width
  parameter int unsigned IdWidth = 32'd0,
  /// AXI User Width.
  parameter int unsigned UserWidth = 32'd0,
  /// AXI4 request struct definition
  parameter type req_t = logic,
  /// AXI4 response struct definition
  parameter type rsp_t = logic,
  /// Warn on accesses to uninitialized bytes
  parameter bit WarnUninitialized = 1'b0,
  /// Application delay (measured after rising clock edge)
  parameter time ApplDelay = 0ps,
  /// Acquisition delay (measured after rising clock edge)
  parameter time AcqDelay = 0ps
) (
  /// Rising-edge clock
  input  logic clk_i,
  /// Active-low reset
  input  logic rst_ni,
  /// AXI4 request struct
  input  req_t axi_req_i,
  /// AXI4 response struct
  output rsp_t axi_rsp_o
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

  initial begin
    automatic ar_t ar_queue[$];
    automatic aw_t aw_queue[$];
    automatic b_t b_queue[$];
    automatic shortint unsigned r_cnt = 0, w_cnt = 0;
    axi_rsp_o = '0;
    wait (rst_ni);
    fork
      // AW
      forever begin
        @(posedge clk_i);
        #(ApplDelay);
        axi_rsp_o.aw_ready = 1'b1;
        #(AcqDelay - ApplDelay);
        if (axi_req_i.aw_valid) begin
          automatic aw_t aw = axi_req_i.aw;
          aw_queue.push_back(aw);
        end
      end
      // W
      forever begin
        @(posedge clk_i);
        #(ApplDelay);
        axi_rsp_o.w_ready = 1'b0;
        if (aw_queue.size() != 0) begin
          axi_rsp_o.w_ready = 1'b1;
          #(AcqDelay - ApplDelay);
          if (axi_req_i.w_valid) begin
            automatic axi_pkg::burst_t burst = aw_queue[0].burst;
            automatic axi_pkg::len_t len = aw_queue[0].len;
            automatic axi_pkg::size_t size = aw_queue[0].size;
            automatic addr_t addr = axi_pkg::beat_addr(aw_queue[0].addr, size, len, burst,
                w_cnt);
            for (shortint unsigned
                i_byte = axi_pkg::beat_lower_byte(addr, size, len, burst, StrbWidth, w_cnt);
                i_byte <= axi_pkg::beat_upper_byte(addr, size, len, burst, StrbWidth, w_cnt);
                i_byte++) begin
              if (axi_req_i.w.strb[i_byte]) begin
                automatic addr_t byte_addr = (addr / StrbWidth) * StrbWidth + i_byte;
                mem[byte_addr] = axi_req_i.w.data[i_byte*8+:8];
              end
            end
            if (w_cnt == aw_queue[0].len) begin
              automatic b_t b_beat = '0;
              assert (axi_req_i.w.last) else $error("Expected last beat of W burst!");
              b_beat.id = aw_queue[0].id;
              b_beat.resp = axi_pkg::RESP_OKAY;
              b_queue.push_back(b_beat);
              w_cnt = 0;
              void'(aw_queue.pop_front());
            end else begin
              assert (!axi_req_i.w.last) else $error("Did not expect last beat of W burst!");
              w_cnt++;
            end
          end
        end
      end
      // B
      forever begin
        @(posedge clk_i);
        #(ApplDelay);
        axi_rsp_o.b_valid = 1'b0;
        if (b_queue.size() != 0) begin
          axi_rsp_o.b = b_queue[0];
          axi_rsp_o.b_valid = 1'b1;
          #(AcqDelay - ApplDelay);
          if (axi_req_i.b_ready) begin
            void'(b_queue.pop_front());
          end
        end
      end
      // AR
      forever begin
        @(posedge clk_i);
        #(ApplDelay);
        axi_rsp_o.ar_ready = 1'b1;
        #(AcqDelay - ApplDelay);
        if (axi_req_i.ar_valid) begin
          automatic ar_t ar = axi_req_i.ar;
          ar_queue.push_back(ar);
        end
      end
      // R
      forever begin
        @(posedge clk_i);
        #(ApplDelay);
        axi_rsp_o.r_valid = 1'b0;
        if (ar_queue.size() != 0) begin
          automatic axi_pkg::burst_t burst = ar_queue[0].burst;
          automatic axi_pkg::len_t len = ar_queue[0].len;
          automatic axi_pkg::size_t size = ar_queue[0].size;
          automatic addr_t addr = axi_pkg::beat_addr(ar_queue[0].addr, size, len, burst, r_cnt);
          automatic r_t r_beat = '0;
          r_beat.data = 'x;
          r_beat.id = ar_queue[0].id;
          r_beat.resp = axi_pkg::RESP_OKAY;
          for (shortint unsigned
              i_byte = axi_pkg::beat_lower_byte(addr, size, len, burst, StrbWidth, r_cnt);
              i_byte <= axi_pkg::beat_upper_byte(addr, size, len, burst, StrbWidth, r_cnt);
              i_byte++) begin
            automatic addr_t byte_addr = (addr / StrbWidth) * StrbWidth + i_byte;
            if (!mem.exists(byte_addr)) begin
              if (WarnUninitialized) begin
                $warning("Access to non-initialized byte at address 0x%016x by ID 0x%x.", byte_addr,
                    r_beat.id);
              end
              r_beat.data[i_byte*8+:8] = 'x;
            end else begin
              r_beat.data[i_byte*8+:8] = mem[byte_addr];
            end
          end
          if (r_cnt == ar_queue[0].len) begin
            r_beat.last = 1'b1;
          end
          axi_rsp_o.r = r_beat;
          axi_rsp_o.r_valid = 1'b1;
          #(AcqDelay - ApplDelay);
          if (axi_req_i.r_ready) begin
            if (r_beat.last) begin
              r_cnt = 0;
              void'(ar_queue.pop_front());
            end else begin
              r_cnt++;
            end
          end
        end
      end
    join
  end

  // Parameter Assertions
  initial begin
    assert (AddrWidth != 0) else $fatal("AddrWidth must be non-zero!", 1);
    assert (DataWidth != 0) else $fatal("DataWidth must be non-zero!", 1);
    assert (IdWidth != 0) else $fatal("IdWidth must be non-zero!", 1);
    assert (UserWidth != 0) else $fatal("UserWidth must be non-zero!", 1);
  end

endmodule
