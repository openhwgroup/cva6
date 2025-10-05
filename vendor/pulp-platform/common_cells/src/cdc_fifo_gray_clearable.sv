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
// Manuel Eggimann <meggimann@iis.ee.ethz.ch> (clearability feature)

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

/// Reset Behavior:
///
/// In contrast to the cdc_fifo_gray version without clear signal, this module
/// supports one-sided warm resets (asynchronously and synchronously). The way
/// this is implemented is described in more detail in the cdc_reset_ctrlr
/// module. To summarize a synchronous clear request i.e. src/dst_clear_i will
/// cause the respective other clock domain to reset as well without introducing
/// any spurious transactions. This is acomplished by an internal module
/// (cdc_reset_ctrlr) the starts a reset sequence on both sides of the CDC in
/// lock-step that first isolates the CDC from the outside world and then resets
/// it. The reset sequencer provides the following behavior:
/// 1. There are no spurious invalid or duplicated transactions regardless how
///    the individual sides are reset (can also happen roughly simultaneosly)
/// 2. The FIFO becomes unready at the src side in the next cycle after
///    synchronous reset request until the reset sequence is completed. Some of
///    the pending transactions might still complete (if the dst accepts at the
///    exact time the reset is request on the src die), some of them will be
///    dropped (of course still guaranteeing FIFO order).
/// 3. During the reset sequence the dst might withdraw the valid signal. This
///    might violate higher level protocols. If you need this feature you would
///    have to path the existing implementation to wait with the isolate_ack
///    assertion until all open handshakes were acknowledged.
/// 4. If the parameter CLEAR_ON_ASYNC_RESET is enabled, the same behavior as
///    above is also valid for asynchronous resets on either side. However, this
///    increases the minimum number of synchronization stages (SYNC_STAGES
///    parameter) from 2 to 3 (read the cdc_reset_ctrlr header to figure out
///    why).
///
///
/// # Constraints
///
/// We need to make sure that the propagation delay of the data, read and write
/// pointer is bound to the minimum of either the sending or receiving clock
/// period to prevent an inconsistent state to be latched (if for example the
/// one bit of the read/write pointer have an excessive delay). Furthermore, we
/// should deactivate setup and hold checks on the asynchronous signals.
///
/// ``` set_ungroup [get_designs cdc_fifo_gray*] false set_boundary_optimization
/// [get_designs cdc_fifo_gray*] false set_max_delay min(T_src, T_dst) \
/// -through [get_pins -hierarchical -filter async] \ -through [get_pins
/// -hierarchical -filter async] set_false_path -hold \ -through [get_pins
/// -hierarchical -filter async] \ -through [get_pins -hierarchical -filter
/// async] ```

`include "common_cells/registers.svh"
`include "common_cells/assertions.svh"

(* no_ungroup *)
(* no_boundary_optimization *)
module cdc_fifo_gray_clearable #(
  /// The width of the default logic type.
  parameter int unsigned WIDTH = 1,
  /// The data type of the payload transported by the FIFO.
  parameter type T = logic [WIDTH-1:0],
  /// The FIFO's depth given as 2**LOG_DEPTH.
  parameter int LOG_DEPTH = 3,
  /// The number of synchronization registers to insert on the async pointers
  /// between the FIFOs. If CLEAR_ON_ASYNC reset is enabled, we need at least 4
  /// synchronizer stages to provide the clear synchronizer lower latency than
  /// the async reset. I.e. if CLEAR_ON_ASYNC_RESET==1 -> SYNC_STAGES >= 4 else
  /// SYNC_STAGES >= 2.
  parameter int SYNC_STAGES = 3,
  parameter int CLEAR_ON_ASYNC_RESET = 1
) (
  input  logic src_rst_ni,
  input  logic src_clk_i,
  input  logic src_clear_i,
  output logic src_clear_pending_o,
  input  T     src_data_i,
  input  logic src_valid_i,
  output logic src_ready_o,

  input  logic dst_rst_ni,
  input  logic dst_clk_i,
  input  logic dst_clear_i,
  output logic dst_clear_pending_o,
  output T     dst_data_o,
  output logic dst_valid_o,
  input  logic dst_ready_i
);

  logic        s_src_clear_req;
  logic        s_src_clear_ack_q;
  logic        s_src_ready;
  logic        s_src_isolate_req;
  logic        s_src_isolate_ack_q;
  logic        s_dst_clear_req;
  logic        s_dst_clear_ack_q;
  logic        s_dst_valid;
  logic        s_dst_isolate_req;
  logic        s_dst_isolate_ack_q;


  T [2**LOG_DEPTH-1:0] async_data;
  logic [LOG_DEPTH:0]  async_wptr;
  logic [LOG_DEPTH:0]  async_rptr;

  if (CLEAR_ON_ASYNC_RESET) begin : gen_elaboration_assertion
    if (SYNC_STAGES < 3)
      $error("The clearable CDC FIFO with async reset synchronization requires at least",
             "3 synchronizer stages for the FIFO.");
  end else begin : gen_elaboration_assertion
    if (SYNC_STAGES < 2) begin : gen_elaboration_assertion
      $error("A minimum of 2 synchronizer stages is required for proper functionality.");
    end
  end

  if (2*SYNC_STAGES > 2**LOG_DEPTH) begin : gen_elaboration_assertion2
    $warning("The FIFOs depth of %0d is insufficient to completely hide the latency of",
             " %0d SYNC_STAGES. The FIFO will stall in the case where f_src ~= f_dst. ",
             "It is reccomended to increase the FIFO's log depth to at least %0d.",
             2**LOG_DEPTH, SYNC_STAGES, $clog2(2*SYNC_STAGES));
  end



  cdc_fifo_gray_src_clearable #(
    .T           ( T           ),
    .LOG_DEPTH   ( LOG_DEPTH   ),
    .SYNC_STAGES ( SYNC_STAGES )
  ) i_src (
    .src_rst_ni,
    .src_clk_i,
    .src_clear_i ( s_src_clear_req                  ),
    .src_data_i,
    .src_valid_i ( src_valid_i & !s_src_isolate_req ),
    .src_ready_o ( s_src_ready                      ),

    (* async *) .async_data_o ( async_data ),
    (* async *) .async_wptr_o ( async_wptr ),
    (* async *) .async_rptr_i ( async_rptr )
  );

  assign src_ready_o = s_src_ready & !s_src_isolate_req;

  cdc_fifo_gray_dst_clearable #(
    .T           ( T           ),
    .LOG_DEPTH   ( LOG_DEPTH   ),
    .SYNC_STAGES ( SYNC_STAGES )
  ) i_dst (
    .dst_rst_ni,
    .dst_clk_i,
    .dst_clear_i ( s_dst_clear_req                  ),
    .dst_data_o,
    .dst_valid_o ( s_dst_valid                      ),
    .dst_ready_i ( dst_ready_i & !s_dst_isolate_req ),

    (* async *) .async_data_i ( async_data ),
    (* async *) .async_wptr_i ( async_wptr ),
    (* async *) .async_rptr_o ( async_rptr )
  );

  assign dst_valid_o = s_dst_valid & !s_dst_isolate_req;

  // Synchronize the clear and reset signaling in both directions (see header of
  // the cdc_reset_ctrlr module for more details.)
  cdc_reset_ctrlr #(
    .SYNC_STAGES(SYNC_STAGES-1)
  ) i_cdc_reset_ctrlr (
    .a_clk_i         ( src_clk_i           ),
    .a_rst_ni        ( src_rst_ni          ),
    .a_clear_i       ( src_clear_i         ),
    .a_clear_o       ( s_src_clear_req     ),
    .a_clear_ack_i   ( s_src_clear_ack_q   ),
    .a_isolate_o     ( s_src_isolate_req   ),
    .a_isolate_ack_i ( s_src_isolate_ack_q ),
    .b_clk_i         ( dst_clk_i           ),
    .b_rst_ni        ( dst_rst_ni          ),
    .b_clear_i       ( dst_clear_i         ),
    .b_clear_o       ( s_dst_clear_req     ),
    .b_clear_ack_i   ( s_dst_clear_ack_q   ),
    .b_isolate_o     ( s_dst_isolate_req   ),
    .b_isolate_ack_i ( s_dst_isolate_ack_q )
  );

  // Just delay the isolate request by one cycle. We can ensure isolation within
  // one cycle by just deasserting valid and ready signals on both sides of the CDC.
  always_ff @(posedge src_clk_i, negedge src_rst_ni) begin
    if (!src_rst_ni) begin
      s_src_isolate_ack_q <= 1'b0;
      s_src_clear_ack_q   <= 1'b0;
    end else begin
      s_src_isolate_ack_q <= s_src_isolate_req;
      s_src_clear_ack_q   <= s_src_clear_req;
    end
  end

  always_ff @(posedge dst_clk_i, negedge dst_rst_ni) begin
    if (!dst_rst_ni) begin
      s_dst_isolate_ack_q <= 1'b0;
      s_dst_clear_ack_q   <= 1'b0;
    end else begin
      s_dst_isolate_ack_q <= s_dst_isolate_req;
      s_dst_clear_ack_q   <= s_dst_clear_req;
    end
  end


  assign src_clear_pending_o = s_src_isolate_req; // The isolate signal stays
                                                  // asserted during the whole
                                                  // clear sequence.
  assign dst_clear_pending_o = s_dst_isolate_req;

  // Check the invariants.
  `ifndef COMMON_CELLS_ASSERTS_OFF
  `ASSERT_INIT(log_depth_0, LOG_DEPTH > 0)
  `ASSERT_INIT(sync_stages_lt_2, SYNC_STAGES >= 2)
  `endif

endmodule


(* no_ungroup *)
(* no_boundary_optimization *)
module cdc_fifo_gray_src_clearable #(
  parameter type T = logic,
  parameter int LOG_DEPTH = 3,
  parameter int SYNC_STAGES = 2
)(
  input  logic src_rst_ni,
  input  logic src_clk_i,
  input  logic src_clear_i,
  input  T     src_data_i,
  input  logic src_valid_i,
  output logic src_ready_o,

  output T [2**LOG_DEPTH-1:0] async_data_o,
  output logic [LOG_DEPTH:0]  async_wptr_o,
  input  logic [LOG_DEPTH:0]  async_rptr_i
);

  localparam int PtrWidth = LOG_DEPTH+1;
  localparam logic [PtrWidth-1:0] PtrFull = (1 << LOG_DEPTH);

  T [2**LOG_DEPTH-1:0] data_q, data_d;
  logic [PtrWidth-1:0] wptr_q, wptr_d, wptr_bin, wptr_next, rptr, rptr_bin;

  // Data FIFO.
  assign async_data_o = data_q;
  always_comb begin
    data_d                          = data_q;
    data_d[wptr_bin[LOG_DEPTH-1:0]] = src_data_i;
  end
  `FFLARN(data_q, data_d, src_valid_i & src_ready_o, '0, src_clk_i, src_rst_ni)

  // Read pointer.
  for (genvar i = 0; i < PtrWidth; i++) begin : gen_sync
    sync #(.STAGES(SYNC_STAGES)) i_sync (
      .clk_i    ( src_clk_i       ),
      .rst_ni   ( src_rst_ni      ),
      .serial_i ( async_rptr_i[i] ),
      .serial_o ( rptr[i]         )
    );
  end
  gray_to_binary #(PtrWidth) i_rptr_g2b (.A(rptr), .Z(rptr_bin));

  // Write pointer.
  assign wptr_next = wptr_bin+1;
  gray_to_binary #(PtrWidth) i_wptr_g2b (.A(wptr_q), .Z(wptr_bin));
  binary_to_gray #(PtrWidth) i_wptr_b2g (.A(wptr_next), .Z(wptr_d));
  `FFLARNC(wptr_q, wptr_d, src_valid_i & src_ready_o, src_clear_i, '0, src_clk_i, src_rst_ni)
  assign async_wptr_o = wptr_q;

  // The pointers into the FIFO are one bit wider than the actual address into
  // the FIFO. This makes detecting critical states very simple: if all but the
  // topmost bit of rptr and wptr agree, the FIFO is in a critical state. If the
  // topmost bit is equal, the FIFO is empty, otherwise it is full.
  assign src_ready_o = ((wptr_bin ^ rptr_bin) != PtrFull);

endmodule


(* no_ungroup *)
(* no_boundary_optimization *)
module cdc_fifo_gray_dst_clearable #(
  parameter type T = logic,
  parameter int LOG_DEPTH = 3,
  parameter int SYNC_STAGES = 2
)(
  input  logic dst_rst_ni,
  input  logic dst_clk_i,
  input  logic dst_clear_i,
  output T     dst_data_o,
  output logic dst_valid_o,
  input  logic dst_ready_i,

  input  T [2**LOG_DEPTH-1:0] async_data_i,
  input  logic [LOG_DEPTH:0]  async_wptr_i,
  output logic [LOG_DEPTH:0]  async_rptr_o
);

  localparam int PtrWidth = LOG_DEPTH+1;
  localparam logic [PtrWidth-1:0] PtrEmpty = '0;

  T dst_data;
  logic [PtrWidth-1:0] rptr_q, rptr_d, rptr_bin, rptr_next, wptr, wptr_bin;
  logic dst_valid, dst_ready;
  // Data selector and register.
  assign dst_data = async_data_i[rptr_bin[LOG_DEPTH-1:0]];

  // Read pointer.
  assign rptr_next = rptr_bin+1;
  gray_to_binary #(PtrWidth) i_rptr_g2b (.A(rptr_q), .Z(rptr_bin));
  binary_to_gray #(PtrWidth) i_rptr_b2g (.A(rptr_next), .Z(rptr_d));
  `FFLARNC(rptr_q, rptr_d, dst_valid & dst_ready, dst_clear_i, '0, dst_clk_i, dst_rst_ni)
  assign async_rptr_o = rptr_q;

  // Write pointer.
  for (genvar i = 0; i < PtrWidth; i++) begin : gen_sync
    sync #(.STAGES(SYNC_STAGES)) i_sync (
      .clk_i    ( dst_clk_i       ),
      .rst_ni   ( dst_rst_ni      ),
      .serial_i ( async_wptr_i[i] ),
      .serial_o ( wptr[i]         )
    );
  end
  gray_to_binary #(PtrWidth) i_wptr_g2b (.A(wptr), .Z(wptr_bin));

  // The pointers into the FIFO are one bit wider than the actual address into
  // the FIFO. This makes detecting critical states very simple: if all but the
  // topmost bit of rptr and wptr agree, the FIFO is in a critical state. If the
  // topmost bit is equal, the FIFO is empty, otherwise it is full.
  assign dst_valid = ((wptr_bin ^ rptr_bin) != PtrEmpty);

  // Cut the combinatorial path with a spill register.
  spill_register_flushable #(
    .T       ( T           )
  ) i_spill_register (
    .clk_i   ( dst_clk_i                ),
    .rst_ni  ( dst_rst_ni               ),
    .flush_i ( dst_clear_i              ),
    .valid_i ( dst_valid & !dst_clear_i ),
    .ready_o ( dst_ready                ),
    .data_i  ( dst_data                 ),
    .valid_o ( dst_valid_o              ),
    .ready_i ( dst_ready_i              ),
    .data_o  ( dst_data_o               )
  );

endmodule
