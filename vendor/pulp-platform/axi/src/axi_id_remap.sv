// Copyright (c) 2014-2020 ETH Zurich, University of Bologna
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
// Andreas Kurth <akurth@iis.ee.ethz.ch>
// Florian Zaruba <zarubaf@iis.ee.ethz.ch>
// Wolfgang Roenninger <wroennin@iis.ee.ethz.ch>

`include "common_cells/registers.svh"

/// Remap AXI IDs from wide IDs at the slave port to narrower IDs at the master port.
///
/// This module is designed to remap an overly wide, sparsely used ID space to a narrower, densely
/// used ID space.  This scenario occurs, for example, when an AXI master has wide ID ports but
/// effectively only uses a (not necessarily contiguous) subset of IDs.
///
/// This module retains the independence of IDs.  That is, if two transactions have different IDs at
/// the slave port of this module, they are guaranteed to have different IDs at the master port of
/// this module.  This implies a lower bound on the [width of IDs on the master
/// port](#parameter.AxiMstPortIdWidth).  If you require narrower master port IDs and can forgo ID
/// independence, use [`axi_id_serialize`](module.axi_id_serialize) instead.
///
/// Internally, a [table is used for remapping IDs](module.axi_id_remap_table).
module axi_id_remap #(
  /// ID width of the AXI4+ATOP slave port.
  parameter int unsigned AxiSlvPortIdWidth = 32'd0,
  /// Maximum number of different IDs that can be in flight at the slave port.  Reads and writes are
  /// counted separately (except for ATOPs, which count as both read and write).
  ///
  /// It is legal for upstream to have transactions with more unique IDs than the maximum given by
  /// this parameter in flight, but a transaction exceeding the maximum will be stalled until all
  /// transactions of another ID complete.
  ///
  /// The maximum value of this parameter is `2**AxiSlvPortIdWidth`.
  parameter int unsigned AxiSlvPortMaxUniqIds = 32'd0,
  /// Maximum number of in-flight transactions with the same ID.
  ///
  /// It is legal for upstream to have more transactions than the maximum given by this parameter in
  /// flight for any ID, but a transaction exceeding the maximum will be stalled until another
  /// transaction with the same ID completes.
  parameter int unsigned AxiMaxTxnsPerId = 32'd0,
  /// ID width of the AXI4+ATOP master port.
  ///
  /// The minimum value of this parameter is the ceiled binary logarithm of `AxiSlvPortMaxUniqIds`,
  /// because IDs at the master port must be wide enough to represent IDs up to
  /// `AxiSlvPortMaxUniqIds-1`.
  ///
  /// If master IDs are wider than the minimum, they are extended by prepending zeros.
  parameter int unsigned AxiMstPortIdWidth = 32'd0,
  /// Request struct type of the AXI4+ATOP slave port.
  ///
  /// The width of all IDs in this struct must match `AxiSlvPortIdWidth`.
  parameter type slv_req_t = logic,
  /// Response struct type of the AXI4+ATOP slave port.
  ///
  /// The width of all IDs in this struct must match `AxiSlvPortIdWidth`.
  parameter type slv_resp_t = logic,
  /// Request struct type of the AXI4+ATOP master port
  ///
  /// The width of all IDs in this struct must match `AxiMstPortIdWidth`.
  parameter type mst_req_t = logic,
  /// Response struct type of the AXI4+ATOP master port
  ///
  /// The width of all IDs in this struct must match `AxiMstPortIdWidth`.
  parameter type mst_resp_t = logic
) (
  /// Rising-edge clock of all ports
  input  logic      clk_i,
  /// Asynchronous reset, active low
  input  logic      rst_ni,
  /// Slave port request
  input  slv_req_t  slv_req_i,
  /// Slave port response
  output slv_resp_t slv_resp_o,
  /// Master port request
  output mst_req_t  mst_req_o,
  /// Master port response
  input  mst_resp_t mst_resp_i
);

  // Feed all signals that are not ID or flow control of AW and AR through.
  assign mst_req_o.aw.addr   = slv_req_i.aw.addr;
  assign mst_req_o.aw.len    = slv_req_i.aw.len;
  assign mst_req_o.aw.size   = slv_req_i.aw.size;
  assign mst_req_o.aw.burst  = slv_req_i.aw.burst;
  assign mst_req_o.aw.lock   = slv_req_i.aw.lock;
  assign mst_req_o.aw.cache  = slv_req_i.aw.cache;
  assign mst_req_o.aw.prot   = slv_req_i.aw.prot;
  assign mst_req_o.aw.qos    = slv_req_i.aw.qos;
  assign mst_req_o.aw.region = slv_req_i.aw.region;
  assign mst_req_o.aw.atop   = slv_req_i.aw.atop;
  assign mst_req_o.aw.user   = slv_req_i.aw.user;

  assign mst_req_o.w         = slv_req_i.w;
  assign mst_req_o.w_valid   = slv_req_i.w_valid;
  assign slv_resp_o.w_ready  = mst_resp_i.w_ready;

  assign slv_resp_o.b.resp   = mst_resp_i.b.resp;
  assign slv_resp_o.b.user   = mst_resp_i.b.user;
  assign slv_resp_o.b_valid  = mst_resp_i.b_valid;
  assign mst_req_o.b_ready   = slv_req_i.b_ready;

  assign mst_req_o.ar.addr   = slv_req_i.ar.addr;
  assign mst_req_o.ar.len    = slv_req_i.ar.len;
  assign mst_req_o.ar.size   = slv_req_i.ar.size;
  assign mst_req_o.ar.burst  = slv_req_i.ar.burst;
  assign mst_req_o.ar.lock   = slv_req_i.ar.lock;
  assign mst_req_o.ar.cache  = slv_req_i.ar.cache;
  assign mst_req_o.ar.prot   = slv_req_i.ar.prot;
  assign mst_req_o.ar.qos    = slv_req_i.ar.qos;
  assign mst_req_o.ar.region = slv_req_i.ar.region;
  assign mst_req_o.ar.user   = slv_req_i.ar.user;

  assign slv_resp_o.r.data   = mst_resp_i.r.data;
  assign slv_resp_o.r.resp   = mst_resp_i.r.resp;
  assign slv_resp_o.r.last   = mst_resp_i.r.last;
  assign slv_resp_o.r.user   = mst_resp_i.r.user;
  assign slv_resp_o.r_valid  = mst_resp_i.r_valid;
  assign mst_req_o.r_ready   = slv_req_i.r_ready;


  // Remap tables keep track of in-flight bursts and their input and output IDs.
  localparam int unsigned IdxWidth = cf_math_pkg::idx_width(AxiSlvPortMaxUniqIds);
  typedef logic [AxiSlvPortMaxUniqIds-1:0]  field_t;
  typedef logic [AxiSlvPortIdWidth-1:0]     id_inp_t;
  typedef logic [IdxWidth-1:0]              idx_t;
  field_t   wr_free,          rd_free,          both_free;
  id_inp_t                    rd_push_inp_id;
  idx_t     wr_free_oup_id,   rd_free_oup_id,   both_free_oup_id,
            wr_push_oup_id,   rd_push_oup_id,
            wr_exists_id,     rd_exists_id;
  logic     wr_exists,        rd_exists,
            wr_exists_full,   rd_exists_full,
            wr_full,          rd_full,
            wr_push,          rd_push;

  axi_id_remap_table #(
    .InpIdWidth     ( AxiSlvPortIdWidth     ),
    .MaxUniqInpIds  ( AxiSlvPortMaxUniqIds  ),
    .MaxTxnsPerId   ( AxiMaxTxnsPerId       )
  ) i_wr_table (
    .clk_i,
    .rst_ni,
    .free_o          ( wr_free                                 ),
    .free_oup_id_o   ( wr_free_oup_id                          ),
    .full_o          ( wr_full                                 ),
    .push_i          ( wr_push                                 ),
    .push_inp_id_i   ( slv_req_i.aw.id                         ),
    .push_oup_id_i   ( wr_push_oup_id                          ),
    .exists_inp_id_i ( slv_req_i.aw.id                         ),
    .exists_o        ( wr_exists                               ),
    .exists_oup_id_o ( wr_exists_id                            ),
    .exists_full_o   ( wr_exists_full                          ),
    .pop_i           ( slv_resp_o.b_valid && slv_req_i.b_ready ),
    .pop_oup_id_i    ( mst_resp_i.b.id[IdxWidth-1:0]           ),
    .pop_inp_id_o    ( slv_resp_o.b.id                         )
  );
  axi_id_remap_table #(
    .InpIdWidth     ( AxiSlvPortIdWidth     ),
    .MaxUniqInpIds  ( AxiSlvPortMaxUniqIds  ),
    .MaxTxnsPerId   ( AxiMaxTxnsPerId       )
  ) i_rd_table (
    .clk_i,
    .rst_ni,
    .free_o           ( rd_free                                                      ),
    .free_oup_id_o    ( rd_free_oup_id                                               ),
    .full_o           ( rd_full                                                      ),
    .push_i           ( rd_push                                                      ),
    .push_inp_id_i    ( rd_push_inp_id                                               ),
    .push_oup_id_i    ( rd_push_oup_id                                               ),
    .exists_inp_id_i  ( slv_req_i.ar.id                                              ),
    .exists_o         ( rd_exists                                                    ),
    .exists_oup_id_o  ( rd_exists_id                                                 ),
    .exists_full_o    ( rd_exists_full                                               ),
    .pop_i            ( slv_resp_o.r_valid && slv_req_i.r_ready && slv_resp_o.r.last ),
    .pop_oup_id_i     ( mst_resp_i.r.id[IdxWidth-1:0]                                ),
    .pop_inp_id_o     ( slv_resp_o.r.id                                              )
  );
  assign both_free = wr_free & rd_free;
  lzc #(
    .WIDTH  ( AxiSlvPortMaxUniqIds  ),
    .MODE   ( 1'b0                  )
  ) i_lzc (
    .in_i     ( both_free        ),
    .cnt_o    ( both_free_oup_id ),
    .empty_o  ( /* unused */     )
  );

  // Zero-extend output IDs if the output IDs is are wider than the IDs from the tables.
  localparam ZeroWidth = AxiMstPortIdWidth - IdxWidth;
  assign mst_req_o.ar.id = {{ZeroWidth{1'b0}}, rd_push_oup_id};
  assign mst_req_o.aw.id = {{ZeroWidth{1'b0}}, wr_push_oup_id};

  // Handle requests.
  enum logic [1:0] {Ready, HoldAR, HoldAW, HoldAx} state_d, state_q;
  idx_t ar_id_d, ar_id_q,
        aw_id_d, aw_id_q;
  logic ar_prio_d, ar_prio_q;
  always_comb begin
    mst_req_o.aw_valid  = 1'b0;
    slv_resp_o.aw_ready = 1'b0;
    wr_push             = 1'b0;
    wr_push_oup_id      =   '0;
    mst_req_o.ar_valid  = 1'b0;
    slv_resp_o.ar_ready = 1'b0;
    rd_push             = 1'b0;
    rd_push_inp_id      =   '0;
    rd_push_oup_id      =   '0;
    ar_id_d             = ar_id_q;
    aw_id_d             = aw_id_q;
    ar_prio_d           = ar_prio_q;
    state_d             = state_q;

    unique case (state_q)
      Ready: begin
        // Reads
        if (slv_req_i.ar_valid) begin
          // If a burst with the same input ID is already in flight or there are free output IDs:
          if ((rd_exists && !rd_exists_full) || (!rd_exists && !rd_full)) begin
            // Determine the output ID: if another in-flight burst had the same input ID, we must
            // reuse its output ID to maintain ordering; else, we assign the next free ID.
            rd_push_inp_id     = slv_req_i.ar.id;
            rd_push_oup_id     = rd_exists ? rd_exists_id : rd_free_oup_id;
            // Forward the AR and push a new entry to the read table.
            mst_req_o.ar_valid = 1'b1;
            rd_push            = 1'b1;
          end
        end

        // Writes
        if (slv_req_i.aw_valid) begin
          // If this is not an ATOP that gives rise to an R response, we can handle it in isolation
          // on the write direction.
          if (!slv_req_i.aw.atop[5]) begin
            // If a burst with the same input ID is already in flight or there are free output IDs:
            if ((wr_exists && !wr_exists_full) || (!wr_exists && !wr_full)) begin
              // Determine the output ID: if another in-flight burst had the same input ID, we must
              // reuse its output ID to maintain ordering; else, we assign the next free ID.
              wr_push_oup_id     = wr_exists ? wr_exists_id : wr_free_oup_id;
              // Forward the AW and push a new entry to the write table.
              mst_req_o.aw_valid = 1'b1;
              wr_push            = 1'b1;
            end
          // If this is an ATOP that gives rise to an R response, we must remap to an ID that is
          // free on both read and write direction and push also to the read table.
          // Only allowed if AR does not have arbitration priority
          end else if (!(ar_prio_q && mst_req_o.ar_valid)) begin
            // Nullify a potential AR at our output.  This is legal in this state.
            mst_req_o.ar_valid  = 1'b0;
            slv_resp_o.ar_ready = 1'b0;
            rd_push             = 1'b0;
            if ((|both_free)) begin
              // Use an output ID that is free in both directions.
              wr_push_oup_id = both_free_oup_id;
              rd_push_inp_id = slv_req_i.aw.id;
              rd_push_oup_id = both_free_oup_id;
              // Forward the AW and push a new entry to both tables.
              mst_req_o.aw_valid = 1'b1;
              rd_push            = 1'b1;
              wr_push            = 1'b1;
              // Give AR priority in the next cycle (so ATOPs cannot infinitely preempt ARs).
              ar_prio_d = 1'b1;
            end
          end
        end

        // Hold AR, AW, or both if they are valid but not yet ready.
        if (mst_req_o.ar_valid) begin
          slv_resp_o.ar_ready = mst_resp_i.ar_ready;
          if (!mst_resp_i.ar_ready) begin
            ar_id_d = rd_push_oup_id;
          end
        end
        if (mst_req_o.aw_valid) begin
          slv_resp_o.aw_ready = mst_resp_i.aw_ready;
          if (!mst_resp_i.aw_ready) begin
            aw_id_d = wr_push_oup_id;
          end
        end
        priority casez ({mst_req_o.ar_valid, mst_resp_i.ar_ready,
                         mst_req_o.aw_valid, mst_resp_i.aw_ready})
          4'b1010: state_d = HoldAx;
          4'b10??: state_d = HoldAR;
          4'b??10: state_d = HoldAW;
          default: state_d = Ready;
        endcase

        if (mst_req_o.ar_valid && mst_resp_i.ar_ready) begin
          ar_prio_d = 1'b0; // Reset AR priority, because handshake was successful in this cycle.
        end
      end

      HoldAR: begin
        // Drive `mst_req_o.ar.id` through `rd_push_oup_id`.
        rd_push_oup_id      = ar_id_q;
        mst_req_o.ar_valid  = 1'b1;
        slv_resp_o.ar_ready = mst_resp_i.ar_ready;
        if (mst_resp_i.ar_ready) begin
          state_d = Ready;
          ar_prio_d = 1'b0; // Reset AR priority, because handshake was successful in this cycle.
        end
      end

      HoldAW: begin
        // Drive mst_req_o.aw.id through `wr_push_oup_id`.
        wr_push_oup_id      = aw_id_q;
        mst_req_o.aw_valid  = 1'b1;
        slv_resp_o.aw_ready = mst_resp_i.aw_ready;
        if (mst_resp_i.aw_ready) begin
          state_d = Ready;
        end
      end

      HoldAx: begin
        rd_push_oup_id      = ar_id_q;
        mst_req_o.ar_valid  = 1'b1;
        slv_resp_o.ar_ready = mst_resp_i.ar_ready;
        wr_push_oup_id      = aw_id_q;
        mst_req_o.aw_valid  = 1'b1;
        slv_resp_o.aw_ready = mst_resp_i.aw_ready;
        unique case ({mst_resp_i.ar_ready, mst_resp_i.aw_ready})
          2'b01:   state_d = HoldAR;
          2'b10:   state_d = HoldAW;
          2'b11:   state_d = Ready;
          default: /*do nothing / stay in this state*/;
        endcase
        if (mst_resp_i.ar_ready) begin
          ar_prio_d = 1'b0; // Reset AR priority, because handshake was successful in this cycle.
        end
      end

      default: state_d = Ready;
    endcase
  end

  // Registers
  `FFARN(ar_id_q, ar_id_d, '0, clk_i, rst_ni)
  `FFARN(ar_prio_q, ar_prio_d, 1'b0, clk_i, rst_ni)
  `FFARN(aw_id_q, aw_id_d, '0, clk_i, rst_ni)
  `FFARN(state_q, state_d, Ready, clk_i, rst_ni)

  // pragma translate_off
  `ifndef VERILATOR
  initial begin : p_assert
    assert(AxiSlvPortIdWidth > 32'd0)
      else $fatal(1, "Parameter AxiSlvPortIdWidth has to be larger than 0!");
    assert(AxiMstPortIdWidth >= IdxWidth)
      else $fatal(1, "Parameter AxiMstPortIdWidth has to be at least IdxWidth!");
    assert (AxiSlvPortMaxUniqIds > 0)
      else $fatal(1, "Parameter AxiSlvPortMaxUniqIds has to be larger than 0!");
    assert (AxiSlvPortMaxUniqIds <= 2**AxiSlvPortIdWidth)
      else $fatal(1, "Parameter AxiSlvPortMaxUniqIds may be at most 2**AxiSlvPortIdWidth!");
    assert (AxiMaxTxnsPerId > 0)
      else $fatal(1, "Parameter AxiMaxTxnsPerId has to be larger than 0!");
    assert($bits(slv_req_i.aw.addr) == $bits(mst_req_o.aw.addr))
      else $fatal(1, "AXI AW address widths are not equal!");
    assert($bits(slv_req_i.w.data) == $bits(mst_req_o.w.data))
      else $fatal(1, "AXI W data widths are not equal!");
    assert($bits(slv_req_i.w.user) == $bits(mst_req_o.w.user))
      else $fatal(1, "AXI W user widths are not equal!");
    assert($bits(slv_req_i.ar.addr) == $bits(mst_req_o.ar.addr))
      else $fatal(1, "AXI AR address widths are not equal!");
    assert($bits(slv_resp_o.r.data) == $bits(mst_resp_i.r.data))
      else $fatal(1, "AXI R data widths are not equal!");
    assert ($bits(slv_req_i.aw.id) == AxiSlvPortIdWidth);
    assert ($bits(slv_resp_o.b.id) == AxiSlvPortIdWidth);
    assert ($bits(slv_req_i.ar.id) == AxiSlvPortIdWidth);
    assert ($bits(slv_resp_o.r.id) == AxiSlvPortIdWidth);
    assert ($bits(mst_req_o.aw.id) == AxiMstPortIdWidth);
    assert ($bits(mst_resp_i.b.id) == AxiMstPortIdWidth);
    assert ($bits(mst_req_o.ar.id) == AxiMstPortIdWidth);
    assert ($bits(mst_resp_i.r.id) == AxiMstPortIdWidth);
  end
  `endif
  default disable iff (!rst_ni);
  assert property (@(posedge clk_i) slv_req_i.aw_valid && slv_resp_o.aw_ready
      |-> mst_req_o.aw_valid && mst_resp_i.aw_ready);
  assert property (@(posedge clk_i) mst_resp_i.b_valid && mst_req_o.b_ready
      |-> slv_resp_o.b_valid && slv_req_i.b_ready);
  assert property (@(posedge clk_i) slv_req_i.ar_valid && slv_resp_o.ar_ready
      |-> mst_req_o.ar_valid && mst_resp_i.ar_ready);
  assert property (@(posedge clk_i) mst_resp_i.r_valid && mst_req_o.r_ready
      |-> slv_resp_o.r_valid && slv_req_i.r_ready);
  assert property (@(posedge clk_i) slv_resp_o.r_valid
      |-> slv_resp_o.r.last == mst_resp_i.r.last);
  assert property (@(posedge clk_i) mst_req_o.ar_valid && !mst_resp_i.ar_ready
      |=> mst_req_o.ar_valid && $stable(mst_req_o.ar.id));
  assert property (@(posedge clk_i) mst_req_o.aw_valid && !mst_resp_i.aw_ready
      |=> mst_req_o.aw_valid && $stable(mst_req_o.aw.id));
  // pragma translate_on
endmodule

/// Internal module of [`axi_id_remap`](module.axi_id_remap): Table to remap input to output IDs.
///
/// This module contains a table indexed by the output ID (type `idx_t`). Each table entry has two
/// fields: the input ID and a counter that records how many transactions with the input and output
/// ID of the entry are in-flight.
///
/// The mapping from input and output IDs is injective.  Therefore, when the table contains an entry
/// for an input ID with non-zero counter value, subsequent input IDs must use the same entry and
/// thus the same output ID.
///
/// ## Relation of types and table layout
/// ![diagram of table](axi_id_remap_table.svg)
///
/// ## Complexity
/// This module has:
/// - `MaxUniqInpIds * InpIdWidth * clog2(MaxTxnsPerId)` flip flops;
/// - `MaxUniqInpIds` comparators of width `InpIdWidth`;
/// - 2 leading-zero counters of width `MaxUniqInpIds`.
module axi_id_remap_table #(
  /// Width of input IDs, therefore width of `id_inp_t`.
  parameter int unsigned InpIdWidth = 32'd0,
  /// Maximum number of different input IDs that can be in-flight. This defines the number of remap
  /// table entries.
  ///
  /// The maximum value of this parameter is `2**InpIdWidth`.
  parameter int unsigned MaxUniqInpIds = 32'd0,
  /// Maximum number of in-flight transactions with the same ID.
  parameter int unsigned MaxTxnsPerId = 32'd0,
  /// Derived (**=do not override**) type of input IDs.
  localparam type id_inp_t = logic [InpIdWidth-1:0],
  /// Derived (**=do not override**) width of table index (ceiled binary logarithm of
  /// `MaxUniqInpIds`).
  localparam int unsigned IdxWidth = cf_math_pkg::idx_width(MaxUniqInpIds),
  /// Derived (**=do not override**) type of table index (width = `IdxWidth`).
  localparam type idx_t = logic [IdxWidth-1:0],
  /// Derived (**=do not override**) type with one bit per table entry (thus also output ID).
  localparam type field_t = logic [MaxUniqInpIds-1:0]
) (
  /// Rising-edge clock of all ports
  input  logic    clk_i,
  /// Asynchronous reset, active low
  input  logic    rst_ni,

  /// One bit per table entry / output ID that indicates whether the entry is free.
  output field_t  free_o,
  /// Lowest free output ID.  Only valid if the table is not full (i.e., `!full_o`).
  output idx_t    free_oup_id_o,
  /// Indicates whether the table is full.
  output logic    full_o,

  /// Push an input/output ID pair to the table.
  input  logic    push_i,
  /// Input ID to be pushed. If the table already contains this ID, its counter must be smaller than
  /// `MaxTxnsPerId`.
  input  id_inp_t push_inp_id_i,
  /// Output ID to be pushed.  If the table already contains the input ID to be pushed, the output
  /// ID **must** match the output ID of the existing entry with the same input ID.
  input  idx_t    push_oup_id_i,

  /// Input ID to look up in the table.
  input  id_inp_t exists_inp_id_i,
  /// Indicates whether the given input ID exists in the table.
  output logic    exists_o,
  /// The output ID of the given input ID.  Only valid if the input ID exists (i.e., `exists_o`).
  output idx_t    exists_oup_id_o,
  /// Indicates whether the maximum number of transactions for the given input ID is reached.  Only
  /// valid if the input ID exists (i.e., `exists_o`).
  output logic    exists_full_o,

  /// Pop an output ID from the table.  This reduces the counter for the table index given in
  /// `pop_oup_id_i` by one.
  input  logic    pop_i,
  /// Output ID to be popped.  The counter for this ID must be larger than `0`.
  input  idx_t    pop_oup_id_i,
  /// Input ID corresponding to the popped output ID.
  output id_inp_t pop_inp_id_o
);

  /// Counter width, derived to hold numbers up to `MaxTxnsPerId`.
  localparam int unsigned CntWidth = $clog2(MaxTxnsPerId+1);
  /// Counter that tracks the number of in-flight transactions with an ID.
  typedef logic [CntWidth-1:0] cnt_t;

  /// Type of a table entry.
  typedef struct packed {
    id_inp_t  inp_id;
    cnt_t     cnt;
  } entry_t;

  // Table indexed by output IDs that contains the corresponding input IDs
  entry_t [MaxUniqInpIds-1:0] table_d, table_q;

  // Determine lowest free output ID.
  for (genvar i = 0; i < MaxUniqInpIds; i++) begin : gen_free_o
    assign free_o[i] = table_q[i].cnt == '0;
  end
  lzc #(
    .WIDTH ( MaxUniqInpIds  ),
    .MODE  ( 1'b0           )
  ) i_lzc_free (
    .in_i    ( free_o        ),
    .cnt_o   ( free_oup_id_o ),
    .empty_o ( full_o        )
  );

  // Determine the input ID for a given output ID.
  if (MaxUniqInpIds == 1) begin : gen_pop_for_single_unique_inp_id
    assign pop_inp_id_o = table_q[0].inp_id;
  end else begin : gen_pop_for_multiple_unique_inp_ids
    assign pop_inp_id_o = table_q[pop_oup_id_i].inp_id;
  end

  // Determine if given output ID is already used and, if it is, by which input ID.
  field_t match;
  for (genvar i = 0; i < MaxUniqInpIds; i++) begin : gen_match
    assign match[i] = table_q[i].cnt > 0 && table_q[i].inp_id == exists_inp_id_i;
  end
  logic no_match;
  lzc #(
      .WIDTH ( MaxUniqInpIds  ),
      .MODE  ( 1'b0           )
  ) i_lzc_match (
      .in_i     ( match           ),
      .cnt_o    ( exists_oup_id_o ),
      .empty_o  ( no_match        )
  );
  assign exists_o      = ~no_match;
  if (MaxUniqInpIds == 1) begin : gen_exists_full_for_single_unique_inp_id
    assign exists_full_o = table_q[0].cnt == MaxTxnsPerId;
  end else begin : gen_exists_full_for_multiple_unique_inp_ids
    assign exists_full_o = table_q[exists_oup_id_o].cnt == MaxTxnsPerId;
  end

  // Push and pop table entries.
  always_comb begin
    table_d = table_q;
    if (push_i) begin
      table_d[push_oup_id_i].inp_id  = push_inp_id_i;
      table_d[push_oup_id_i].cnt    += 1;
    end
    if (pop_i) begin
      table_d[pop_oup_id_i].cnt -= 1;
    end
  end

  // Registers
  `FFARN(table_q, table_d, '0, clk_i, rst_ni)

  // Assertions
  // pragma translate_off
  `ifndef VERILATOR
    default disable iff (!rst_ni);
    assume property (@(posedge clk_i) push_i |->
        table_q[push_oup_id_i].cnt == '0 || table_q[push_oup_id_i].inp_id == push_inp_id_i)
      else $error("Push must be to empty output ID or match existing input ID!");
    assume property (@(posedge clk_i) push_i |-> table_q[push_oup_id_i].cnt < MaxTxnsPerId)
      else $error("Maximum number of in-flight bursts must not be exceeded!");
    assume property (@(posedge clk_i) pop_i |-> table_q[pop_oup_id_i].cnt > 0)
      else $error("Pop must target output ID with non-zero counter!");
    assume property (@(posedge clk_i) $onehot0(match))
      else $error("Input ID in table must be unique!");
    initial begin
      assert (InpIdWidth > 0);
      assert (MaxUniqInpIds > 0);
      assert (MaxUniqInpIds <= (1 << InpIdWidth));
      assert (MaxTxnsPerId > 0);
      assert (IdxWidth >= 1);
    end
  `endif
  // pragma translate_on

endmodule


`include "axi/typedef.svh"
`include "axi/assign.svh"
/// Interface variant of [`axi_id_remap`](module.axi_id_remap).
///
/// See the documentation of the main module for the definition of ports and parameters.
module axi_id_remap_intf #(
  parameter int unsigned AXI_SLV_PORT_ID_WIDTH = 32'd0,
  parameter int unsigned AXI_SLV_PORT_MAX_UNIQ_IDS = 32'd0,
  parameter int unsigned AXI_MAX_TXNS_PER_ID = 32'd0,
  parameter int unsigned AXI_MST_PORT_ID_WIDTH = 32'd0,
  parameter int unsigned AXI_ADDR_WIDTH = 32'd0,
  parameter int unsigned AXI_DATA_WIDTH = 32'd0,
  parameter int unsigned AXI_USER_WIDTH = 32'd0
) (
  input logic     clk_i,
  input logic     rst_ni,
  AXI_BUS.Slave   slv,
  AXI_BUS.Master  mst
);
  typedef logic [AXI_SLV_PORT_ID_WIDTH-1:0] slv_id_t;
  typedef logic [AXI_MST_PORT_ID_WIDTH-1:0] mst_id_t;
  typedef logic [AXI_ADDR_WIDTH-1:0]        axi_addr_t;
  typedef logic [AXI_DATA_WIDTH-1:0]        axi_data_t;
  typedef logic [AXI_DATA_WIDTH/8-1:0]      axi_strb_t;
  typedef logic [AXI_USER_WIDTH-1:0]        axi_user_t;

  `AXI_TYPEDEF_AW_CHAN_T(slv_aw_chan_t, axi_addr_t, slv_id_t, axi_user_t)
  `AXI_TYPEDEF_W_CHAN_T(slv_w_chan_t, axi_data_t, axi_strb_t, axi_user_t)
  `AXI_TYPEDEF_B_CHAN_T(slv_b_chan_t, slv_id_t, axi_user_t)
  `AXI_TYPEDEF_AR_CHAN_T(slv_ar_chan_t, axi_addr_t, slv_id_t, axi_user_t)
  `AXI_TYPEDEF_R_CHAN_T(slv_r_chan_t, axi_data_t, slv_id_t, axi_user_t)
  `AXI_TYPEDEF_REQ_T(slv_req_t, slv_aw_chan_t, slv_w_chan_t, slv_ar_chan_t)
  `AXI_TYPEDEF_RESP_T(slv_resp_t, slv_b_chan_t, slv_r_chan_t)

  `AXI_TYPEDEF_AW_CHAN_T(mst_aw_chan_t, axi_addr_t, mst_id_t, axi_user_t)
  `AXI_TYPEDEF_W_CHAN_T(mst_w_chan_t, axi_data_t, axi_strb_t, axi_user_t)
  `AXI_TYPEDEF_B_CHAN_T(mst_b_chan_t, mst_id_t, axi_user_t)
  `AXI_TYPEDEF_AR_CHAN_T(mst_ar_chan_t, axi_addr_t, mst_id_t, axi_user_t)
  `AXI_TYPEDEF_R_CHAN_T(mst_r_chan_t, axi_data_t, mst_id_t, axi_user_t)
  `AXI_TYPEDEF_REQ_T(mst_req_t, mst_aw_chan_t, mst_w_chan_t, mst_ar_chan_t)
  `AXI_TYPEDEF_RESP_T(mst_resp_t, mst_b_chan_t, mst_r_chan_t)

  slv_req_t  slv_req;
  slv_resp_t slv_resp;
  mst_req_t  mst_req;
  mst_resp_t mst_resp;

  `AXI_ASSIGN_TO_REQ(slv_req, slv)
  `AXI_ASSIGN_FROM_RESP(slv, slv_resp)
  `AXI_ASSIGN_FROM_REQ(mst, mst_req)
  `AXI_ASSIGN_TO_RESP(mst_resp, mst)

  axi_id_remap #(
    .AxiSlvPortIdWidth    ( AXI_SLV_PORT_ID_WIDTH     ),
    .AxiSlvPortMaxUniqIds ( AXI_SLV_PORT_MAX_UNIQ_IDS ),
    .AxiMaxTxnsPerId      ( AXI_MAX_TXNS_PER_ID       ),
    .AxiMstPortIdWidth    ( AXI_MST_PORT_ID_WIDTH     ),
    .slv_req_t            ( slv_req_t                 ),
    .slv_resp_t           ( slv_resp_t                ),
    .mst_req_t            ( mst_req_t                 ),
    .mst_resp_t           ( mst_resp_t                )
  ) i_axi_id_remap (
    .clk_i,
    .rst_ni,
    .slv_req_i  ( slv_req  ),
    .slv_resp_o ( slv_resp ),
    .mst_req_o  ( mst_req  ),
    .mst_resp_i ( mst_resp )
  );
  // pragma translate_off
  `ifndef VERILATOR
    initial begin
      assert (slv.AXI_ID_WIDTH   == AXI_SLV_PORT_ID_WIDTH);
      assert (slv.AXI_ADDR_WIDTH == AXI_ADDR_WIDTH);
      assert (slv.AXI_DATA_WIDTH == AXI_DATA_WIDTH);
      assert (slv.AXI_USER_WIDTH == AXI_USER_WIDTH);
      assert (mst.AXI_ID_WIDTH   == AXI_MST_PORT_ID_WIDTH);
      assert (mst.AXI_ADDR_WIDTH == AXI_ADDR_WIDTH);
      assert (mst.AXI_DATA_WIDTH == AXI_DATA_WIDTH);
      assert (mst.AXI_USER_WIDTH == AXI_USER_WIDTH);
    end
  `endif
  // pragma translate_on
endmodule
