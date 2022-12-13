// Copyright (c) 2020 ETH Zurich and University of Bologna.
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

`include "common_cells/registers.svh"

/// Serialize all AXI transactions to a single ID (zero).
///
/// This module contains one queue with slave port IDs for the read direction and one for the write
/// direction.  These queues are used to reconstruct the ID of responses at the slave port.  The
/// depth of each queue is defined by `MaxReadTxns` and `MaxWriteTxns`, respectively.
module axi_serializer #(
  /// Maximum number of in flight read transactions.
  parameter int unsigned MaxReadTxns  = 32'd0,
  /// Maximum number of in flight write transactions.
  parameter int unsigned MaxWriteTxns = 32'd0,
  /// AXI4+ATOP ID width.
  parameter int unsigned AxiIdWidth   = 32'd0,
  /// AXI4+ATOP request struct definition.
  parameter type         req_t        = logic,
  /// AXI4+ATOP response struct definition.
  parameter type         resp_t       = logic
) (
  /// Clock
  input  logic  clk_i,
  /// Asynchronous reset, active low
  input  logic  rst_ni,
  /// Slave port request
  input  req_t  slv_req_i,
  /// Slave port response
  output resp_t slv_resp_o,
  /// Master port request
  output req_t  mst_req_o,
  /// Master port response
  input  resp_t mst_resp_i
);

  typedef logic [AxiIdWidth-1:0] id_t;
  typedef enum logic [1:0] {
    AtopIdle    = 2'b00,
    AtopDrain   = 2'b01,
    AtopExecute = 2'b10
  } state_e;

  logic   rd_fifo_full, rd_fifo_empty, rd_fifo_push, rd_fifo_pop,
          wr_fifo_full, wr_fifo_empty, wr_fifo_push, wr_fifo_pop;
  id_t    b_id,
          r_id,         ar_id;
  state_e state_q,      state_d;

  always_comb begin
    // Default assignments
    state_d      = state_q;
    rd_fifo_push = 1'b0;
    wr_fifo_push = 1'b0;

    // Default, connect the channels
    mst_req_o  = slv_req_i;
    slv_resp_o = mst_resp_i;

    // Serialize transactions -> tie downstream IDs to zero.
    mst_req_o.aw.id = '0;
    mst_req_o.ar.id = '0;

    // Reflect upstream ID in response.
    ar_id           = slv_req_i.ar.id;
    slv_resp_o.b.id = b_id;
    slv_resp_o.r.id = r_id;

    // Default, cut the AW/AR handshaking
    mst_req_o.ar_valid  = 1'b0;
    slv_resp_o.ar_ready = 1'b0;
    mst_req_o.aw_valid  = 1'b0;
    slv_resp_o.aw_ready = 1'b0;

    unique case (state_q)
      AtopIdle, AtopExecute: begin

        // Wait until the ATOP response(s) have been sent back upstream.
        if (state_q == AtopExecute) begin
          if ((wr_fifo_empty && rd_fifo_empty) || (wr_fifo_pop && rd_fifo_pop) ||
              (wr_fifo_empty && rd_fifo_pop)   || (wr_fifo_pop && rd_fifo_empty)) begin
            state_d = AtopIdle;
          end
        end

        // This part lets new Transactions through, if no ATOP is underway or the last ATOP
        // response has been transmitted.
        if ((state_q == AtopIdle) || (state_d == AtopIdle)) begin
          // Gate AR handshake with ready output of Read FIFO.
          mst_req_o.ar_valid  = slv_req_i.ar_valid  & ~rd_fifo_full;
          slv_resp_o.ar_ready = mst_resp_i.ar_ready & ~rd_fifo_full;
          rd_fifo_push        = mst_req_o.ar_valid  & mst_resp_i.ar_ready;
          if (slv_req_i.aw_valid) begin
            if (slv_req_i.aw.atop[5:4] == axi_pkg::ATOP_NONE) begin
              // Normal operation
              // Gate AW handshake with ready output of Write FIFO.
              mst_req_o.aw_valid  = ~wr_fifo_full;
              slv_resp_o.aw_ready = mst_resp_i.aw_ready & ~wr_fifo_full;
              wr_fifo_push        = mst_req_o.aw_valid  & mst_resp_i.aw_ready;
            end else begin
              // Atomic Operation received, go to drain state, when both channels are ready
              // Wait for finished or no AR beat
              if (!mst_req_o.ar_valid || (mst_req_o.ar_valid && mst_resp_i.ar_ready)) begin
                state_d = AtopDrain;
              end
            end
          end
        end
      end
      AtopDrain: begin
        // Send the ATOP AW when the last open transaction terminates
        if (wr_fifo_empty && rd_fifo_empty) begin
          mst_req_o.aw_valid  = 1'b1;
          slv_resp_o.aw_ready = mst_resp_i.aw_ready;
          wr_fifo_push        = mst_resp_i.aw_ready;
          if (slv_req_i.aw.atop[axi_pkg::ATOP_R_RESP]) begin
            // Overwrite the read ID with the one from AW
            ar_id        = slv_req_i.aw.id;
            rd_fifo_push = mst_resp_i.aw_ready;
          end
          if (mst_resp_i.aw_ready) begin
            state_d = AtopExecute;
          end
        end
      end
      default : /* do nothing */;
    endcase

    // Gate B handshake with empty flag output of Write FIFO.
    slv_resp_o.b_valid = mst_resp_i.b_valid & ~wr_fifo_empty;
    mst_req_o.b_ready  = slv_req_i.b_ready  & ~wr_fifo_empty;

    // Gate R handshake with empty flag output of Read FIFO.
    slv_resp_o.r_valid = mst_resp_i.r_valid & ~rd_fifo_empty;
    mst_req_o.r_ready  = slv_req_i.r_ready  & ~rd_fifo_empty;
  end

  fifo_v3 #(
    .FALL_THROUGH ( 1'b0        ), // No fall-through as response has to come a cycle later anyway
    .DEPTH        ( MaxReadTxns ),
    .dtype        ( id_t        )
  ) i_rd_id_fifo (
    .clk_i,
    .rst_ni,
    .flush_i    ( 1'b0          ),
    .testmode_i ( 1'b0          ),
    .data_i     ( ar_id         ),
    .push_i     ( rd_fifo_push  ),
    .full_o     ( rd_fifo_full  ),
    .data_o     ( r_id          ),
    .empty_o    ( rd_fifo_empty ),
    .pop_i      ( rd_fifo_pop   ),
    .usage_o    ( /*not used*/  )
  );
  // Assign as this condition is needed in FSM
  assign rd_fifo_pop = slv_resp_o.r_valid & slv_req_i.r_ready & slv_resp_o.r.last;

  fifo_v3 #(
    .FALL_THROUGH ( 1'b0         ),
    .DEPTH        ( MaxWriteTxns ),
    .dtype        ( id_t         )
  ) i_wr_id_fifo (
    .clk_i,
    .rst_ni,
    .flush_i    ( 1'b0            ),
    .testmode_i ( 1'b0            ),
    .data_i     ( slv_req_i.aw.id ),
    .push_i     ( wr_fifo_push    ),
    .full_o     ( wr_fifo_full    ),
    .data_o     ( b_id            ),
    .empty_o    ( wr_fifo_empty   ),
    .pop_i      ( wr_fifo_pop     ),
    .usage_o    ( /*not used*/    )
  );
  // Assign as this condition is needed in FSM
  assign wr_fifo_pop = slv_resp_o.b_valid & slv_req_i.b_ready;

  `FFARN(state_q, state_d, AtopIdle, clk_i, rst_ni)

// pragma translate_off
`ifndef VERILATOR
  initial begin: p_assertions
    assert (AxiIdWidth    >= 1) else $fatal(1, "AXI ID width must be at least 1!");
    assert (MaxReadTxns   >= 1)
      else $fatal(1, "Maximum number of read transactions must be >= 1!");
    assert (MaxWriteTxns  >= 1)
      else $fatal(1, "Maximum number of write transactions must be >= 1!");
  end
  default disable iff (~rst_ni);
  aw_lost : assert property( @(posedge clk_i)
      (slv_req_i.aw_valid & slv_resp_o.aw_ready |-> mst_req_o.aw_valid & mst_resp_i.aw_ready))
    else $error("AW beat lost.");
  w_lost  : assert property( @(posedge clk_i)
      (slv_req_i.w_valid & slv_resp_o.w_ready |-> mst_req_o.w_valid & mst_resp_i.w_ready))
    else $error("W beat lost.");
  b_lost  : assert property( @(posedge clk_i)
      (mst_resp_i.b_valid & mst_req_o.b_ready |-> slv_resp_o.b_valid & slv_req_i.b_ready))
    else $error("B beat lost.");
  ar_lost : assert property( @(posedge clk_i)
      (slv_req_i.ar_valid & slv_resp_o.ar_ready |-> mst_req_o.ar_valid & mst_resp_i.ar_ready))
    else $error("AR beat lost.");
  r_lost :  assert property( @(posedge clk_i)
      (mst_resp_i.r_valid & mst_req_o.r_ready |-> slv_resp_o.r_valid & slv_req_i.r_ready))
    else $error("R beat lost.");
`endif
// pragma translate_on
endmodule

`include "axi/typedef.svh"
`include "axi/assign.svh"
/// Serialize all AXI transactions to a single ID (zero), interface version.
module axi_serializer_intf #(
  /// AXI4+ATOP ID width.
  parameter int unsigned AXI_ID_WIDTH   = 32'd0,
  /// AXI4+ATOP address width.
  parameter int unsigned AXI_ADDR_WIDTH = 32'd0,
  /// AXI4+ATOP data width.
  parameter int unsigned AXI_DATA_WIDTH = 32'd0,
  /// AXI4+ATOP user width.
  parameter int unsigned AXI_USER_WIDTH = 32'd0,
  /// Maximum number of in flight read transactions.
  parameter int unsigned MAX_READ_TXNS  = 32'd0,
  /// Maximum number of in flight write transactions.
  parameter int unsigned MAX_WRITE_TXNS = 32'd0
) (
  /// Clock
  input  logic    clk_i,
  /// Asynchronous reset, active low
  input  logic    rst_ni,
  /// AXI4+ATOP Slave modport
  AXI_BUS.Slave   slv,
  /// AXI4+ATOP Master modport
  AXI_BUS.Master  mst
);

  typedef logic [AXI_ID_WIDTH    -1:0] id_t;
  typedef logic [AXI_ADDR_WIDTH  -1:0] addr_t;
  typedef logic [AXI_DATA_WIDTH  -1:0] data_t;
  typedef logic [AXI_DATA_WIDTH/8-1:0] strb_t;
  typedef logic [AXI_USER_WIDTH  -1:0] user_t;
  `AXI_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(b_chan_t, id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(r_chan_t, data_t, id_t, user_t)
  `AXI_TYPEDEF_REQ_T(req_t, aw_chan_t, w_chan_t, ar_chan_t)
  `AXI_TYPEDEF_RESP_T(resp_t, b_chan_t, r_chan_t)
  req_t  slv_req,  mst_req;
  resp_t slv_resp, mst_resp;
  `AXI_ASSIGN_TO_REQ(slv_req, slv)
  `AXI_ASSIGN_FROM_RESP(slv, slv_resp)
  `AXI_ASSIGN_FROM_REQ(mst, mst_req)
  `AXI_ASSIGN_TO_RESP(mst_resp, mst)

  axi_serializer #(
    .MaxReadTxns  ( MAX_READ_TXNS  ),
    .MaxWriteTxns ( MAX_WRITE_TXNS ),
    .AxiIdWidth   ( AXI_ID_WIDTH   ),
    .req_t        ( req_t          ),
    .resp_t       ( resp_t         )
  ) i_axi_serializer (
    .clk_i,
    .rst_ni,
    .slv_req_i  ( slv_req  ),
    .slv_resp_o ( slv_resp ),
    .mst_req_o  ( mst_req  ),
    .mst_resp_i ( mst_resp )
  );

// pragma translate_off
`ifndef VERILATOR
  initial begin: p_assertions
    assert (AXI_ADDR_WIDTH  >= 1) else $fatal(1, "AXI address width must be at least 1!");
    assert (AXI_DATA_WIDTH  >= 1) else $fatal(1, "AXI data width must be at least 1!");
    assert (AXI_ID_WIDTH    >= 1) else $fatal(1, "AXI ID width must be at least 1!");
    assert (AXI_USER_WIDTH  >= 1) else $fatal(1, "AXI user width must be at least 1!");
    assert (MAX_READ_TXNS   >= 1)
      else $fatal(1, "Maximum number of read transactions must be >= 1!");
    assert (MAX_WRITE_TXNS  >= 1)
      else $fatal(1, "Maximum number of write transactions must be >= 1!");
  end
`endif
// pragma translate_on
endmodule
