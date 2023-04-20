// Copyright (c) 2019-2020 ETH Zurich, University of Bologna
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

`include "axi/typedef.svh"
`include "common_cells/registers.svh"

/// This module can isolate the AXI4+ATOPs bus on the master port from the slave port.  When the
/// isolation is not active, the two ports are directly connected.
///
/// This module counts how many open transactions are currently in flight on the read and write
/// channels.  It is further capable of tracking the amount of open atomic transactions with read
/// responses.
///
/// The isolation interface has two signals: `isolate_i` and `isolated_o`.  When `isolate_i` is
/// asserted, all open transactions are gracefully terminated.  When no transactions are in flight
/// anymore, the `isolated_o` output is asserted.  As long as `isolated_o` is asserted, all output
/// signals in `mst_req_o` are silenced to `'0`.  When isolated, new transactions initiated on the
/// slave port are stalled until the isolation is terminated by deasserting `isolate_i`.
///
/// ## Response
///
/// If the `TerminateTransaction` parameter is set to `1'b1`, the module will return response errors
/// in case there is an incoming transaction while the module isolates.  The data returned on the
/// bus is `1501A7ED` (hexspeak for isolated).
///
/// If `TerminateTransaction` is set to `1'b0`, the transaction will block indefinitely until the
/// module is de-isolated again.
module axi_isolate #(
  /// Maximum number of pending requests per channel
  parameter int unsigned NumPending = 32'd16,
  /// Gracefully terminate all incoming transactions in case of isolation by returning proper error
  /// responses.
  parameter bit TerminateTransaction = 1'b0,
  /// Support atomic operations (ATOPs)
  parameter bit AtopSupport = 1'b1,
  /// Address width of all AXI4+ATOP ports
  parameter int signed AxiAddrWidth = 32'd0,
  /// Data width of all AXI4+ATOP ports
  parameter int signed AxiDataWidth = 32'd0,
  /// ID width of all AXI4+ATOP ports
  parameter int signed AxiIdWidth = 32'd0,
  /// User signal width of all AXI4+ATOP ports
  parameter int signed AxiUserWidth = 32'd0,
  /// Request struct type of all AXI4+ATOP ports
  parameter type         axi_req_t  = logic,
  /// Response struct type of all AXI4+ATOP ports
  parameter type         axi_resp_t = logic
) (
  /// Rising-edge clock of all ports
  input  logic      clk_i,
  /// Asynchronous reset, active low
  input  logic      rst_ni,
  /// Slave port request
  input  axi_req_t  slv_req_i,
  /// Slave port response
  output axi_resp_t slv_resp_o,
  /// Master port request
  output axi_req_t  mst_req_o,
  /// Master port response
  input  axi_resp_t mst_resp_i,
  /// Isolate master port from slave port
  input  logic      isolate_i,
  /// Master port is isolated from slave port
  output logic      isolated_o
);

  typedef logic [AxiIdWidth-1:0]     id_t;
  typedef logic [AxiAddrWidth-1:0]   addr_t;
  typedef logic [AxiDataWidth-1:0]   data_t;
  typedef logic [AxiDataWidth/8-1:0] strb_t;
  typedef logic [AxiUserWidth-1:0]   user_t;

  `AXI_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(b_chan_t, id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(r_chan_t, data_t, id_t, user_t)

  axi_req_t [1:0]   demux_req;
  axi_resp_t [1:0]  demux_rsp;

  if (TerminateTransaction) begin
    axi_demux #(
      .AxiIdWidth     ( AxiIdWidth  ),
      .AtopSupport    ( AtopSupport ),
      .aw_chan_t      ( aw_chan_t   ),
      .w_chan_t       ( w_chan_t    ),
      .b_chan_t       ( b_chan_t    ),
      .ar_chan_t      ( ar_chan_t   ),
      .r_chan_t       ( r_chan_t    ),
      .axi_req_t      ( axi_req_t   ),
      .axi_resp_t     ( axi_resp_t  ),
      .NoMstPorts     ( 2           ),
      .MaxTrans       ( NumPending  ),
      // We don't need many bits here as the common case will be to go for the pass-through.
      .AxiLookBits    ( 1           ),
      .UniqueIds      ( 1'b0        ),
      .SpillAw        ( 1'b0        ),
      .SpillW         ( 1'b0        ),
      .SpillB         ( 1'b0        ),
      .SpillAr        ( 1'b0        ),
      .SpillR         ( 1'b0        )
    ) i_axi_demux (
      .clk_i,
      .rst_ni,
      .test_i          ( 1'b0       ),
      .slv_req_i,
      .slv_aw_select_i ( isolated_o ),
      .slv_ar_select_i ( isolated_o ),
      .slv_resp_o,
      .mst_reqs_o      ( demux_req ),
      .mst_resps_i     ( demux_rsp )
    );

    axi_err_slv #(
      .AxiIdWidth  ( AxiIdWidth           ),
      .axi_req_t   ( axi_req_t            ),
      .axi_resp_t  ( axi_resp_t           ),
      .Resp        ( axi_pkg::RESP_DECERR ),
      .RespData    ( 'h1501A7ED           ),
      .ATOPs       ( AtopSupport          ),
      .MaxTrans    ( 1                    )
    ) i_axi_err_slv (
      .clk_i,
      .rst_ni,
      .test_i     ( 1'b0         ),
      .slv_req_i  ( demux_req[1] ),
      .slv_resp_o ( demux_rsp[1] )
    );
  end else begin
    assign demux_req[0] = slv_req_i;
    assign slv_resp_o = demux_rsp[0];
  end

  axi_isolate_inner #(
    .NumPending ( NumPending  ),
    .axi_req_t  ( axi_req_t   ),
    .axi_resp_t ( axi_resp_t  )
  ) i_axi_isolate (
    .clk_i,
    .rst_ni,
    .slv_req_i  ( demux_req[0] ),
    .slv_resp_o ( demux_rsp[0] ),
    .mst_req_o,
    .mst_resp_i,
    .isolate_i,
    .isolated_o
  );
endmodule

module axi_isolate_inner #(
  parameter int unsigned NumPending = 32'd16,
  parameter type         axi_req_t  = logic,
  parameter type         axi_resp_t = logic
) (
  input  logic      clk_i,
  input  logic      rst_ni,
  input  axi_req_t  slv_req_i,
  output axi_resp_t slv_resp_o,
  output axi_req_t  mst_req_o,
  input  axi_resp_t mst_resp_i,
  input  logic      isolate_i,
  output logic      isolated_o
);

  // plus 1 in clog for accouning no open transaction, plus one bit for atomic injection
  localparam int unsigned CounterWidth = $clog2(NumPending + 32'd1) + 32'd1;
  typedef logic [CounterWidth-1:0] cnt_t;

  typedef enum logic [1:0] {
    Normal,
    Hold,
    Drain,
    Isolate
  } isolate_state_e;
  isolate_state_e state_aw_d, state_aw_q, state_ar_d, state_ar_q;
  logic           update_aw_state,        update_ar_state;

  cnt_t pending_aw_d,  pending_aw_q;
  logic update_aw_cnt;

  cnt_t pending_w_d,   pending_w_q;
  logic update_w_cnt,  connect_w;

  cnt_t pending_ar_d,  pending_ar_q;
  logic update_ar_cnt;

  `FFLARN(pending_aw_q, pending_aw_d, update_aw_cnt, '0, clk_i, rst_ni)
  `FFLARN(pending_w_q, pending_w_d, update_w_cnt, '0, clk_i, rst_ni)
  `FFLARN(pending_ar_q, pending_ar_d, update_ar_cnt, '0, clk_i, rst_ni)
  `FFLARN(state_aw_q, state_aw_d, update_aw_state, Isolate, clk_i, rst_ni)
  `FFLARN(state_ar_q, state_ar_d, update_ar_state, Isolate, clk_i, rst_ni)

  // Update counters.
  always_comb begin
    pending_aw_d  = pending_aw_q;
    update_aw_cnt = 1'b0;
    pending_w_d   = pending_w_q;
    update_w_cnt  = 1'b0;
    connect_w     = 1'b0;
    pending_ar_d  = pending_ar_q;
    update_ar_cnt = 1'b0;
    // write counters
    if (mst_req_o.aw_valid && (state_aw_q == Normal)) begin
      pending_aw_d++;
      update_aw_cnt   = 1'b1;
      pending_w_d++;
      update_w_cnt    = 1'b1;
      connect_w       = 1'b1;
      if (mst_req_o.aw.atop[axi_pkg::ATOP_R_RESP]) begin
        pending_ar_d++; // handle atomic with read response by injecting a count in AR
        update_ar_cnt = 1'b1;
      end
    end
    if (mst_req_o.w_valid  && mst_resp_i.w_ready && mst_req_o.w.last) begin
      pending_w_d--;
      update_w_cnt  = 1'b1;
    end
    if (mst_resp_i.b_valid  && mst_req_o.b_ready) begin
      pending_aw_d--;
      update_aw_cnt = 1'b1;
    end
    // read counters
    if (mst_req_o.ar_valid && (state_ar_q == Normal)) begin
      pending_ar_d++;
      update_ar_cnt = 1'b1;
    end
    if (mst_resp_i.r_valid  && mst_req_o.r_ready && mst_resp_i.r.last) begin
      pending_ar_d--;
      update_ar_cnt = 1'b1;
    end
  end

  // Perform isolation.
  always_comb begin
    // Default assignments
    state_aw_d      = state_aw_q;
    update_aw_state = 1'b0;
    state_ar_d      = state_ar_q;
    update_ar_state = 1'b0;
    // Connect channel per default
    mst_req_o       = slv_req_i;
    slv_resp_o      = mst_resp_i;

    /////////////////////////////////////////////////////////////
    // Write transaction
    /////////////////////////////////////////////////////////////
    unique case (state_aw_q)
      Normal:  begin // Normal operation
        // Cut valid handshake if a counter capacity is reached.  It has to check AR counter in case
        // of atomics.  Counters are wide enough to account for injected count in the read response
        // counter.
        if (pending_aw_q >= cnt_t'(NumPending) || pending_ar_q >= cnt_t'(2*NumPending)
            || (pending_w_q >= cnt_t'(NumPending))) begin
          mst_req_o.aw_valid  = 1'b0;
          slv_resp_o.aw_ready = 1'b0;
          if (isolate_i) begin
            state_aw_d      = Drain;
            update_aw_state = 1'b1;
          end
        end else begin
          // here the AW handshake is connected normally
          if (slv_req_i.aw_valid && !mst_resp_i.aw_ready) begin
            state_aw_d      = Hold;
            update_aw_state = 1'b1;
          end else begin
            if (isolate_i) begin
              state_aw_d      = Drain;
              update_aw_state = 1'b1;
            end
          end
        end
      end
      Hold: begin // Hold the valid signal on 1'b1 if there was no transfer
        mst_req_o.aw_valid = 1'b1;
        // aw_ready normal connected
        if (mst_resp_i.aw_ready) begin
          update_aw_state = 1'b1;
          state_aw_d      = isolate_i ? Drain : Normal;
        end
      end
      Drain: begin // cut the AW channel until counter is zero
        mst_req_o.aw        = '0;
        mst_req_o.aw_valid  = 1'b0;
        slv_resp_o.aw_ready = 1'b0;
        if (pending_aw_q == '0) begin
          state_aw_d      = Isolate;
          update_aw_state = 1'b1;
        end
      end
      Isolate: begin // Cut the signals to the outputs
        mst_req_o.aw        = '0;
        mst_req_o.aw_valid  = 1'b0;
        slv_resp_o.aw_ready = 1'b0;
        slv_resp_o.b        = '0;
        slv_resp_o.b_valid  = 1'b0;
        mst_req_o.b_ready   = 1'b0;
        if (!isolate_i) begin
          state_aw_d      = Normal;
          update_aw_state = 1'b1;
        end
      end
      default: /*do nothing*/;
    endcase

    // W channel is cut as long the counter is zero and not explicitly unlocked through an AW.
    if ((pending_w_q == '0) && !connect_w ) begin
      mst_req_o.w         = '0;
      mst_req_o.w_valid   = 1'b0;
      slv_resp_o.w_ready  = 1'b0;
    end

    /////////////////////////////////////////////////////////////
    // Read transaction
    /////////////////////////////////////////////////////////////
    unique case (state_ar_q)
      Normal: begin
        // cut handshake if counter capacity is reached
        if (pending_ar_q >= NumPending) begin
          mst_req_o.ar_valid  = 1'b0;
          slv_resp_o.ar_ready = 1'b0;
          if (isolate_i) begin
            state_ar_d      = Drain;
            update_ar_state = 1'b1;
          end
        end else begin
          // here the AR handshake is connected normally
          if (slv_req_i.ar_valid && !mst_resp_i.ar_ready) begin
            state_ar_d      = Hold;
            update_ar_state = 1'b1;
          end else begin
            if (isolate_i) begin
              state_ar_d      = Drain;
              update_ar_state = 1'b1;
            end
          end
        end
      end
      Hold: begin // Hold the valid signal on 1'b1 if there was no transfer
        mst_req_o.ar_valid = 1'b1;
        // ar_ready normal connected
        if (mst_resp_i.ar_ready) begin
          update_ar_state = 1'b1;
          state_ar_d      = isolate_i ? Drain : Normal;
        end
      end
      Drain: begin
        mst_req_o.ar        = '0;
        mst_req_o.ar_valid  = 1'b0;
        slv_resp_o.ar_ready = 1'b0;
        if (pending_ar_q == '0) begin
          state_ar_d      = Isolate;
          update_ar_state = 1'b1;
        end
      end
      Isolate: begin
        mst_req_o.ar        = '0;
        mst_req_o.ar_valid  = 1'b0;
        slv_resp_o.ar_ready = 1'b0;
        slv_resp_o.r        = '0;
        slv_resp_o.r_valid  = 1'b0;
        mst_req_o.r_ready   = 1'b0;
        if (!isolate_i) begin
          state_ar_d      = Normal;
          update_ar_state = 1'b1;
        end
      end
      default: /*do nothing*/;
    endcase
  end

  // the isolated output signal
  assign isolated_o = (state_aw_q == Isolate && state_ar_q == Isolate);

// pragma translate_off
`ifndef VERILATOR
  initial begin
    assume (NumPending > 0) else $fatal(1, "At least one pending transaction required.");
  end
  default disable iff (!rst_ni);
  aw_overflow: assert property (@(posedge clk_i)
      (pending_aw_q == '1) |=> (pending_aw_q != '0)) else
      $fatal(1, "pending_aw_q overflowed");
  ar_overflow: assert property (@(posedge clk_i)
      (pending_ar_q == '1) |=> (pending_ar_q != '0)) else
      $fatal(1, "pending_ar_q overflowed");
  aw_underflow: assert property (@(posedge clk_i)
      (pending_aw_q == '0) |=> (pending_aw_q != '1)) else
      $fatal(1, "pending_aw_q underflowed");
  ar_underflow: assert property (@(posedge clk_i)
      (pending_ar_q == '0) |=> (pending_ar_q != '1)) else
      $fatal(1, "pending_ar_q underflowed");
`endif
// pragma translate_on
endmodule

`include "axi/assign.svh"

/// Interface variant of [`axi_isolate`](module.axi_isolate).
///
/// See the documentation of the main module for the definition of ports and parameters.
module axi_isolate_intf #(
  parameter int unsigned NUM_PENDING    = 32'd16,
  parameter bit TERMINATE_TRANSACTION   = 1'b0,
  parameter bit ATOP_SUPPORT            = 1'b1,
  parameter int unsigned AXI_ID_WIDTH   = 32'd0,
  parameter int unsigned AXI_ADDR_WIDTH = 32'd0,
  parameter int unsigned AXI_DATA_WIDTH = 32'd0,
  parameter int unsigned AXI_USER_WIDTH = 32'd0
) (
  input  logic   clk_i,
  input  logic   rst_ni,
  AXI_BUS.Slave  slv,
  AXI_BUS.Master mst,
  input  logic   isolate_i,
  output logic   isolated_o
);
  typedef logic [AXI_ID_WIDTH-1:0]     id_t;
  typedef logic [AXI_ADDR_WIDTH-1:0]   addr_t;
  typedef logic [AXI_DATA_WIDTH-1:0]   data_t;
  typedef logic [AXI_DATA_WIDTH/8-1:0] strb_t;
  typedef logic [AXI_USER_WIDTH-1:0]   user_t;

  `AXI_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(b_chan_t, id_t, user_t)

  `AXI_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(r_chan_t, data_t, id_t, user_t)

  `AXI_TYPEDEF_REQ_T(axi_req_t, aw_chan_t, w_chan_t, ar_chan_t)
  `AXI_TYPEDEF_RESP_T(axi_resp_t, b_chan_t, r_chan_t)

  axi_req_t  slv_req,  mst_req;
  axi_resp_t slv_resp, mst_resp;

  `AXI_ASSIGN_TO_REQ(slv_req, slv)
  `AXI_ASSIGN_FROM_RESP(slv, slv_resp)

  `AXI_ASSIGN_FROM_REQ(mst, mst_req)
  `AXI_ASSIGN_TO_RESP(mst_resp, mst)

  axi_isolate #(
    .NumPending           ( NUM_PENDING           ),
    .TerminateTransaction ( TERMINATE_TRANSACTION ),
    .AtopSupport          ( ATOP_SUPPORT          ),
    .AxiAddrWidth         ( AXI_ADDR_WIDTH        ),
    .AxiDataWidth         ( AXI_DATA_WIDTH        ),
    .AxiIdWidth           ( AXI_ID_WIDTH          ),
    .AxiUserWidth         ( AXI_USER_WIDTH        ),
    .axi_req_t            ( axi_req_t             ),
    .axi_resp_t           ( axi_resp_t            )
  ) i_axi_isolate (
    .clk_i,
    .rst_ni,
    .slv_req_i  ( slv_req  ),
    .slv_resp_o ( slv_resp ),
    .mst_req_o  ( mst_req  ),
    .mst_resp_i ( mst_resp ),
    .isolate_i,
    .isolated_o
  );

  // pragma translate_off
  `ifndef VERILATOR
  initial begin
    assume (AXI_ID_WIDTH   > 0) else $fatal(1, "AXI_ID_WIDTH   has to be > 0.");
    assume (AXI_ADDR_WIDTH > 0) else $fatal(1, "AXI_ADDR_WIDTH has to be > 0.");
    assume (AXI_DATA_WIDTH > 0) else $fatal(1, "AXI_DATA_WIDTH has to be > 0.");
    assume (AXI_USER_WIDTH > 0) else $fatal(1, "AXI_USER_WIDTH has to be > 0.");
  end
  `endif
  // pragma translate_on
endmodule

