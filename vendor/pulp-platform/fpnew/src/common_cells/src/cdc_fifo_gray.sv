// Copyright 2018 ETH Zurich and University of Bologna.
//
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Fabian Schuiki <fschuiki@iis.ee.ethz.ch>

/// A clock domain crossing FIFO, using gray counters.
///
/// This FIFO has its push and pop ports in two separate clock domains. Its size
/// can only be powers of two, which is why its depth is given as 2**LOG_DEPTH.
/// LOG_DEPTH must be at least 1.
///
/// # Constraints
///
/// The following constraints need to be set:
/// - max_delay -from src_wptr_gray_q -to dst_wptr_gray_q
/// - max_delay -from dst_rptr_gray_q -to src_rptr_gray_q
/// - max_delay -from fifo_data_q -to fifo_rdata
module cdc_fifo_gray #(
  /// The data type of the payload transported by the FIFO.
  parameter type T = logic,
  /// The FIFO's depth given as 2**LOG_DEPTH.
  parameter int LOG_DEPTH = 3
)(
  input  logic src_rst_ni,
  input  logic src_clk_i,
  input  T     src_data_i,
  input  logic src_valid_i,
  output logic src_ready_o,

  input  logic dst_rst_ni,
  input  logic dst_clk_i,
  output T     dst_data_o,
  output logic dst_valid_o,
  input  logic dst_ready_i
);

  // Check the invariants.
  //pragma translate_off
  initial begin
    assert(LOG_DEPTH > 0);
  end
  //pragma translate_on

  localparam int PTR_WIDTH = LOG_DEPTH+1;
  typedef logic [PTR_WIDTH-1:0] pointer_t;
  typedef logic [LOG_DEPTH-1:0] index_t;

  localparam pointer_t PTR_FULL  = (1 << LOG_DEPTH);
  localparam pointer_t PTR_EMPTY = '0;

  // Allocate the registers for the FIFO memory with its separate write and read
  // ports. The FIFO has the following ports:
  //
  // - write: fifo_widx, fifo_wdata, fifo_write, src_clk_i
  // - read: fifo_ridx, fifo_rdata
  index_t fifo_widx, fifo_ridx;
  logic fifo_write;
  T fifo_wdata, fifo_rdata;
  T fifo_data_q [2**LOG_DEPTH];

  assign fifo_rdata = fifo_data_q[fifo_ridx];

  for (genvar i = 0; i < 2**LOG_DEPTH; i++) begin : g_word
    always_ff @(posedge src_clk_i, negedge src_rst_ni) begin
      if (!src_rst_ni)
        fifo_data_q[i] <= '0;
      else if (fifo_write && fifo_widx == i)
        fifo_data_q[i] <= fifo_wdata;
    end
  end

  // Create the write and read pointers in the source and destination domain.
  // These are binary counters combined with a Gray encoder. Both the binary and
  // the Gray coded output are registered; the binary one for use in the local
  // domain, the Gray one for synchronization into the other domain.
  pointer_t src_wptr_bin_q, src_wptr_gray_q, dst_rptr_bin_q, dst_rptr_gray_q;
  pointer_t src_wptr_bin_d, src_wptr_gray_d, dst_rptr_bin_d, dst_rptr_gray_d;

  assign src_wptr_bin_d = src_wptr_bin_q + 1;
  assign dst_rptr_bin_d = dst_rptr_bin_q + 1;

  binary_to_gray #(PTR_WIDTH) i_src_b2g (src_wptr_bin_d, src_wptr_gray_d);
  binary_to_gray #(PTR_WIDTH) i_dst_b2g (dst_rptr_bin_d, dst_rptr_gray_d);

  always_ff @(posedge src_clk_i, negedge src_rst_ni) begin
    if (!src_rst_ni) begin
      src_wptr_bin_q  <= '0;
      src_wptr_gray_q <= '0;
    end else if (src_valid_i && src_ready_o) begin
      src_wptr_bin_q  <= src_wptr_bin_d;
      src_wptr_gray_q <= src_wptr_gray_d;
    end
  end

  always_ff @(posedge dst_clk_i, negedge dst_rst_ni) begin
    if (!dst_rst_ni) begin
      dst_rptr_bin_q  <= '0;
      dst_rptr_gray_q <= '0;
    end else if (dst_valid_o && dst_ready_i) begin
      dst_rptr_bin_q  <= dst_rptr_bin_d;
      dst_rptr_gray_q <= dst_rptr_gray_d;
    end
  end

  // Move the Gray-coded pointers over into the other clock domain and
  // synchronize them to reduce the probability of metastability.
  pointer_t src_rptr_gray_q, src_rptr_gray_q2;
  pointer_t dst_wptr_gray_q, dst_wptr_gray_q2;

  always_ff @(posedge src_clk_i, negedge src_rst_ni) begin
    if (!src_rst_ni) begin
      src_rptr_gray_q  <= '0;
      src_rptr_gray_q2 <= '0;
    end else begin
      src_rptr_gray_q  <= dst_rptr_gray_q;
      src_rptr_gray_q2 <= src_rptr_gray_q;
    end
  end

  always_ff @(posedge dst_clk_i, negedge dst_rst_ni) begin
    if (!dst_rst_ni) begin
      dst_wptr_gray_q  <= '0;
      dst_wptr_gray_q2 <= '0;
    end else begin
      dst_wptr_gray_q  <= src_wptr_gray_q;
      dst_wptr_gray_q2 <= dst_wptr_gray_q;
    end
  end

  // Reverse the Gray coding of the synchronized pointers.
  pointer_t src_rptr_bin, dst_wptr_bin;

  gray_to_binary #(PTR_WIDTH) i_src_g2b (src_rptr_gray_q2, src_rptr_bin);
  gray_to_binary #(PTR_WIDTH) i_dst_g2b (dst_wptr_gray_q2, dst_wptr_bin);

  // The pointers into the FIFO are one bit wider than the actual address into
  // the FIFO. This makes detecting critical states very simple: if all but the
  // topmost bit of rptr and wptr agree, the FIFO is in a critical state. If the
  // topmost bit is equal, the FIFO is empty, otherwise it is full.
  assign src_ready_o = ((src_wptr_bin_q ^ src_rptr_bin) != PTR_FULL);
  assign dst_valid_o = ((dst_rptr_bin_q ^ dst_wptr_bin) != PTR_EMPTY);

  // Drive the FIFO write and read ports.
  assign fifo_widx  = src_wptr_bin_q;
  assign fifo_wdata = src_data_i;
  assign fifo_write = src_valid_i && src_ready_o;
  assign fifo_ridx  = dst_rptr_bin_q;
  assign dst_data_o = fifo_rdata;

endmodule
