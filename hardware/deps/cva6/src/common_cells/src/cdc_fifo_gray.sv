// Copyright 2018-2019 ETH Zurich and University of Bologna.
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
// Florian Zaruba <zarubaf@iis.ee.ethz.ch>

/// A clock domain crossing FIFO, using gray counters.
///
/// # Architecture
///
/// The design is split into two parts, each one being clocked and reset
/// separately.
/// 1. The data to be transferred  over the clock domain boundary is
///    is stored in a FIFO. The corresponding write pointer is managed
///    (incremented) in the source clock domain.
/// 2. The entire FIFO content is exposed over the `async_data` port.
///    The destination clock domain increments its read pointer
///    in its destination clock domain.
///
/// Read and write pointers are then gray coded, communicated
/// and synchronized using a classic multi-stage FF synchronizer
/// in the other clock domain. The gray coding ensures that only
/// one bit changes at each pointer increment, preventing the
/// synchronizer to accidentally latch an inconsistent state
/// on a multi-bit bus.
///
/// The not full signal e.g. `src_ready_o` (on the sending side)
/// is generated using the local write pointer and the pessimistic
/// read pointer from the destination clock domain (pessimistic
/// because it is delayed at least two cycles because of the synchronizer
/// stages). This prevents the FIFO from overflowing.
///
/// The not empty signal e.g. `dst_valid_o` is generated using
/// the pessimistic write pointer and the local read pointer in
/// the destination clock domain. This means the FIFO content
/// does not need to be synchronized as we are sure we are reading
/// data which has been written at least two cycles earlier.
/// Furthermore, the read select logic into the FIFO is completely
/// clocked by the destination clock domain which avoids
/// inefficient data synchronization.
///
/// The FIFO size must be powers of two, which is why its depth is
/// given as 2**LOG_DEPTH. LOG_DEPTH must be at least 1.
///
/// # Constraints
///
/// We need to make sure that the propagation delay of the
/// data, read and write pointer is bound to the minimum of
/// either the sending or receiving clock period to prevent
/// an inconsistent state to be latched (if for example the one
/// bit of the read/write pointer have an excessive delay).
/// Furthermore, we should deactivate setup and hold checks on
/// the asynchronous signals.
///
/// ```
/// set_ungroup [get_designs cdc_fifo_gray*] false
/// set_boundary_optimization [get_designs cdc_fifo_gray*] false
/// set_max_delay min(T_src, T_dst) \
///     -through [get_pins -hierarchical -filter async] \
///     -through [get_pins -hierarchical -filter async]
/// set_false_path -hold \
///     -through [get_pins -hierarchical -filter async] \
///     -through [get_pins -hierarchical -filter async]
/// ```

`include "common_cells/registers.svh"

(* no_ungroup *)
(* no_boundary_optimization *)
module cdc_fifo_gray #(
  /// The width of the default logic type.
  parameter WIDTH = 1,
  /// The data type of the payload transported by the FIFO.
  parameter type T = logic [WIDTH-1:0],
  /// The FIFO's depth given as 2**LOG_DEPTH.
  parameter int LOG_DEPTH = 3,
  /// The number of synchronization registers to insert on the async pointers.
  parameter int SYNC_STAGES = 2
) (
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

  T [2**LOG_DEPTH-1:0] async_data;
  logic [LOG_DEPTH:0]  async_wptr;
  logic [LOG_DEPTH:0]  async_rptr;

  cdc_fifo_gray_src #(
    .T         ( T         ),
    .LOG_DEPTH ( LOG_DEPTH )
  ) i_src (
    .src_rst_ni,
    .src_clk_i,
    .src_data_i,
    .src_valid_i,
    .src_ready_o,

    (* async *) .async_data_o ( async_data ),
    (* async *) .async_wptr_o ( async_wptr ),
    (* async *) .async_rptr_i ( async_rptr )
  );

  cdc_fifo_gray_dst #(
    .T         ( T         ),
    .LOG_DEPTH ( LOG_DEPTH )
  ) i_dst (
    .dst_rst_ni,
    .dst_clk_i,
    .dst_data_o,
    .dst_valid_o,
    .dst_ready_i,

    (* async *) .async_data_i ( async_data ),
    (* async *) .async_wptr_i ( async_wptr ),
    (* async *) .async_rptr_o ( async_rptr )
  );

  // Check the invariants.
  // pragma translate_off
  `ifndef VERILATOR
  initial assert(LOG_DEPTH > 0);
  initial assert(SYNC_STAGES >= 2);
  `endif
  // pragma translate_on

endmodule


(* no_ungroup *)
(* no_boundary_optimization *)
module cdc_fifo_gray_src #(
  parameter type T = logic,
  parameter int LOG_DEPTH = 3,
  parameter int SYNC_STAGES = 2
)(
  input  logic src_rst_ni,
  input  logic src_clk_i,
  input  T     src_data_i,
  input  logic src_valid_i,
  output logic src_ready_o,

  output T [2**LOG_DEPTH-1:0] async_data_o,
  output logic [LOG_DEPTH:0]  async_wptr_o,
  input  logic [LOG_DEPTH:0]  async_rptr_i
);

  localparam int PTR_WIDTH = LOG_DEPTH+1;
  localparam [PTR_WIDTH-1:0] PTR_FULL = (1 << LOG_DEPTH);

  T [2**LOG_DEPTH-1:0] data_q;
  logic [PTR_WIDTH-1:0] wptr_q, wptr_d, wptr_bin, wptr_next, rptr, rptr_bin;

  // Data FIFO.
  assign async_data_o = data_q;
  for (genvar i = 0; i < 2**LOG_DEPTH; i++) begin : gen_word
    `FFLNR(data_q[i], src_data_i, src_valid_i & src_ready_o & (wptr_bin[LOG_DEPTH-1:0] == i), src_clk_i)
  end

  // Read pointer.
  for (genvar i = 0; i < PTR_WIDTH; i++) begin : gen_sync
    sync #(.STAGES(SYNC_STAGES)) i_sync (
      .clk_i    ( src_clk_i       ),
      .rst_ni   ( src_rst_ni      ),
      .serial_i ( async_rptr_i[i] ),
      .serial_o ( rptr[i]         )
    );
  end
  gray_to_binary #(PTR_WIDTH) i_rptr_g2b (.A(rptr), .Z(rptr_bin));

  // Write pointer.
  assign wptr_next = wptr_bin+1;
  gray_to_binary #(PTR_WIDTH) i_wptr_g2b (.A(wptr_q), .Z(wptr_bin));
  binary_to_gray #(PTR_WIDTH) i_wptr_b2g (.A(wptr_next), .Z(wptr_d));
  `FFLARN(wptr_q, wptr_d, src_valid_i & src_ready_o, '0, src_clk_i, src_rst_ni)
  assign async_wptr_o = wptr_q;

  // The pointers into the FIFO are one bit wider than the actual address into
  // the FIFO. This makes detecting critical states very simple: if all but the
  // topmost bit of rptr and wptr agree, the FIFO is in a critical state. If the
  // topmost bit is equal, the FIFO is empty, otherwise it is full.
  assign src_ready_o = ((wptr_bin ^ rptr_bin) != PTR_FULL);

endmodule


(* no_ungroup *)
(* no_boundary_optimization *)
module cdc_fifo_gray_dst #(
  parameter type T = logic,
  parameter int LOG_DEPTH = 3,
  parameter int SYNC_STAGES = 2
)(
  input  logic dst_rst_ni,
  input  logic dst_clk_i,
  output T     dst_data_o,
  output logic dst_valid_o,
  input  logic dst_ready_i,

  input  T [2**LOG_DEPTH-1:0] async_data_i,
  input  logic [LOG_DEPTH:0]  async_wptr_i,
  output logic [LOG_DEPTH:0]  async_rptr_o
);

  localparam int PTR_WIDTH = LOG_DEPTH+1;
  localparam [PTR_WIDTH-1:0] PTR_EMPTY = '0;

  T dst_data;
  logic [PTR_WIDTH-1:0] rptr_q, rptr_d, rptr_bin, rptr_bin_d, rptr_next, wptr, wptr_bin;
  logic dst_valid, dst_ready;
  // Data selector and register.
  assign dst_data = async_data_i[rptr_bin[LOG_DEPTH-1:0]];

  // Read pointer.
  assign rptr_next = rptr_bin+1;
  gray_to_binary #(PTR_WIDTH) i_rptr_g2b (.A(rptr_q), .Z(rptr_bin));
  binary_to_gray #(PTR_WIDTH) i_rptr_b2g (.A(rptr_next), .Z(rptr_d));
  `FFLARN(rptr_q, rptr_d, dst_valid & dst_ready, '0, dst_clk_i, dst_rst_ni)
  assign async_rptr_o = rptr_q;

  // Write pointer.
  for (genvar i = 0; i < PTR_WIDTH; i++) begin : gen_sync
    sync #(.STAGES(SYNC_STAGES)) i_sync (
      .clk_i    ( dst_clk_i       ),
      .rst_ni   ( dst_rst_ni      ),
      .serial_i ( async_wptr_i[i] ),
      .serial_o ( wptr[i]         )
    );
  end
  gray_to_binary #(PTR_WIDTH) i_wptr_g2b (.A(wptr), .Z(wptr_bin));

  // The pointers into the FIFO are one bit wider than the actual address into
  // the FIFO. This makes detecting critical states very simple: if all but the
  // topmost bit of rptr and wptr agree, the FIFO is in a critical state. If the
  // topmost bit is equal, the FIFO is empty, otherwise it is full.
  assign dst_valid = ((wptr_bin ^ rptr_bin) != PTR_EMPTY);

  // Cut the combinatorial path with a spill register.
  spill_register #(
    .T       ( T           )
  ) i_spill_register (
    .clk_i   ( dst_clk_i   ),
    .rst_ni  ( dst_rst_ni  ),
    .valid_i ( dst_valid   ),
    .ready_o ( dst_ready   ),
    .data_i  ( dst_data    ),
    .valid_o ( dst_valid_o ),
    .ready_i ( dst_ready_i ),
    .data_o  ( dst_data_o  )
  );

endmodule
