// Copyright (c) 2020 ETH Zurich, University of Bologna
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

/// Split AXI4 bursts into single-beat transactions.
///
/// ## Limitations
///
/// - This module does not support wrapping ([`axi_pkg::BURST_WRAP`](package.axi_pkg)) bursts and
///   responds to such bursts with slave error(s).
/// - This module does not support atomic operations (ATOPs) and responds to ATOPs with a slave
///   error.  Place an [`axi_atop_filter`](module.axi_atop_filter) before this module if upstream
///   modules can generate ATOPs.
module axi_burst_splitter #(
  // Maximum number of AXI read bursts outstanding at the same time
  parameter int unsigned MaxReadTxns  = 32'd0,
  // Maximum number of AXI write bursts outstanding at the same time
  parameter int unsigned MaxWriteTxns = 32'd0,
  // AXI Bus Types
  parameter int unsigned AddrWidth    = 32'd0,
  parameter int unsigned DataWidth    = 32'd0,
  parameter int unsigned IdWidth      = 32'd0,
  parameter int unsigned UserWidth    = 32'd0,
  parameter type         req_t        = logic,
  parameter type         resp_t       = logic
) (
  input  logic  clk_i,
  input  logic  rst_ni,

  // Input / Slave Port
  input  req_t  slv_req_i,
  output resp_t slv_resp_o,

  // Output / Master Port
  output req_t  mst_req_o,
  input  resp_t mst_resp_i
);

  typedef logic [AddrWidth-1:0]   addr_t;
  typedef logic [DataWidth-1:0]   data_t;
  typedef logic [IdWidth-1:0]     id_t;
  typedef logic [DataWidth/8-1:0] strb_t;
  typedef logic [UserWidth-1:0]   user_t;
  `AXI_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(b_chan_t, id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t, id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(r_chan_t, data_t, id_t, user_t)

  // Demultiplex between supported and unsupported transactions.
  req_t   act_req,  unsupported_req;
  resp_t  act_resp, unsupported_resp;
  logic   sel_aw_unsupported, sel_ar_unsupported;
  localparam int unsigned MaxTxns = (MaxReadTxns > MaxWriteTxns) ? MaxReadTxns : MaxWriteTxns;
  axi_demux #(
    .AxiIdWidth   ( IdWidth   ),
    .aw_chan_t    ( aw_chan_t ),
    .w_chan_t     ( w_chan_t  ),
    .b_chan_t     ( b_chan_t  ),
    .ar_chan_t    ( ar_chan_t ),
    .r_chan_t     ( r_chan_t  ),
    .req_t        ( req_t     ),
    .resp_t       ( resp_t    ),
    .NoMstPorts   ( 2         ),
    .MaxTrans     ( MaxTxns   ),
    .AxiLookBits  ( IdWidth   ),
    .FallThrough  ( 1'b1      ),
    .SpillAw      ( 1'b0      ),
    .SpillW       ( 1'b0      ),
    .SpillB       ( 1'b0      ),
    .SpillAr      ( 1'b0      ),
    .SpillR       ( 1'b0      )
  ) i_demux_supported_vs_unsupported (
    .clk_i,
    .rst_ni,
    .test_i           ( 1'b0                          ),
    .slv_req_i,
    .slv_aw_select_i  ( sel_aw_unsupported            ),
    .slv_ar_select_i  ( sel_ar_unsupported            ),
    .slv_resp_o,
    .mst_reqs_o       ( {unsupported_req,  act_req}   ),
    .mst_resps_i      ( {unsupported_resp, act_resp}  )
  );
  // Define supported transactions.
  function bit txn_supported(axi_pkg::atop_t atop, axi_pkg::burst_t burst, axi_pkg::cache_t cache,
      axi_pkg::len_t len);
    // Single-beat transactions do not need splitting, so all are supported.
    if (len == '0) return 1'b1;
    // Wrapping bursts are currently not supported.
    if (burst == axi_pkg::BURST_WRAP) return 1'b0;
    // ATOPs are not supported.
    if (atop != '0) return 1'b0;
    // The AXI Spec (A3.4.1) only allows splitting non-modifiable transactions ..
    if (!axi_pkg::modifiable(cache)) begin
      // .. if they are INCR bursts and longer than 16 beats.
      return (burst == axi_pkg::BURST_INCR) & (len > 16);
    end
    // All other transactions are supported.
    return 1'b1;
  endfunction
  assign sel_aw_unsupported = ~txn_supported(slv_req_i.aw.atop, slv_req_i.aw.burst,
                                              slv_req_i.aw.cache, slv_req_i.aw.len);
  assign sel_ar_unsupported = ~txn_supported('0, slv_req_i.ar.burst,
                                              slv_req_i.ar.cache, slv_req_i.ar.len);
  // Respond to unsupported transactions with slave errors.
  axi_err_slv #(
    .AxiIdWidth ( IdWidth               ),
    .req_t      ( req_t                 ),
    .resp_t     ( resp_t                ),
    .Resp       ( axi_pkg::RESP_SLVERR  ),
    .ATOPs      ( 1'b0                  ),  // The burst splitter does not support ATOPs.
    .MaxTrans   ( 1                     )   // Splitting bursts implies a low-performance bus.
  ) i_err_slv (
    .clk_i,
    .rst_ni,
    .test_i     ( 1'b0              ),
    .slv_req_i  ( unsupported_req   ),
    .slv_resp_o ( unsupported_resp  )
  );

  // --------------------------------------------------
  // AW Channel
  // --------------------------------------------------
  logic           w_cnt_dec, w_cnt_req, w_cnt_gnt, w_cnt_err;
  axi_pkg::len_t  w_cnt_len;
  axi_burst_splitter_ax_chan #(
    .chan_t   ( aw_chan_t    ),
    .IdWidth  ( IdWidth      ),
    .MaxTxns  ( MaxWriteTxns )
  ) i_axi_burst_splitter_aw_chan (
    .clk_i,
    .rst_ni,
    .ax_i           ( act_req.aw           ),
    .ax_valid_i     ( act_req.aw_valid     ),
    .ax_ready_o     ( act_resp.aw_ready    ),
    .ax_o           ( mst_req_o.aw         ),
    .ax_valid_o     ( mst_req_o.aw_valid   ),
    .ax_ready_i     ( mst_resp_i.aw_ready  ),
    .cnt_id_i       ( mst_resp_i.b.id      ),
    .cnt_len_o      ( w_cnt_len            ),
    .cnt_set_err_i  ( mst_resp_i.b.resp[1] ),
    .cnt_err_o      ( w_cnt_err            ),
    .cnt_dec_i      ( w_cnt_dec            ),
    .cnt_req_i      ( w_cnt_req            ),
    .cnt_gnt_o      ( w_cnt_gnt            )
  );

  // --------------------------------------------------
  // W Channel
  // --------------------------------------------------
  // Feed through, except `last`, which is always set.
  always_comb begin
    mst_req_o.w        = act_req.w;
    mst_req_o.w.last   = 1'b1;        // overwrite last flag
  end
  assign mst_req_o.w_valid  = act_req.w_valid;
  assign act_resp.w_ready   = mst_resp_i.w_ready;

  // --------------------------------------------------
  // B Channel
  // --------------------------------------------------
  // Filter B response, except for the last one
  enum logic {BReady, BWait} b_state_d, b_state_q;
  logic b_err_d, b_err_q;
  always_comb begin
    mst_req_o.b_ready = 1'b0;
    act_resp.b        = '0;
    act_resp.b_valid  = 1'b0;
    w_cnt_dec         = 1'b0;
    w_cnt_req         = 1'b0;
    b_err_d           = b_err_q;
    b_state_d         = b_state_q;

    unique case (b_state_q)
      BReady: begin
        if (mst_resp_i.b_valid) begin
          w_cnt_req = 1'b1;
          if (w_cnt_gnt) begin
            if (w_cnt_len == 8'd0) begin
              act_resp.b = mst_resp_i.b;
              if (w_cnt_err) begin
                act_resp.b.resp = axi_pkg::RESP_SLVERR;
              end
              act_resp.b_valid  = 1'b1;
              w_cnt_dec         = 1'b1;
              if (act_req.b_ready) begin
                mst_req_o.b_ready = 1'b1;
              end else begin
                b_state_d = BWait;
                b_err_d   = w_cnt_err;
              end
            end else begin
              mst_req_o.b_ready = 1'b1;
              w_cnt_dec         = 1'b1;
            end
          end
        end
      end
      BWait: begin
        act_resp.b = mst_resp_i.b;
        if (b_err_q) begin
          act_resp.b.resp = axi_pkg::RESP_SLVERR;
        end
        act_resp.b_valid  = 1'b1;
        if (mst_resp_i.b_valid && act_req.b_ready) begin
          mst_req_o.b_ready = 1'b1;
          b_state_d         = BReady;
        end
      end
      default: /*do nothing*/;
    endcase
  end

  // --------------------------------------------------
  // AR Channel
  // --------------------------------------------------
  // See description of `ax_chan` module.
  logic           r_cnt_dec, r_cnt_req, r_cnt_gnt;
  axi_pkg::len_t  r_cnt_len;
  axi_burst_splitter_ax_chan #(
    .chan_t   ( ar_chan_t   ),
    .IdWidth  ( IdWidth     ),
    .MaxTxns  ( MaxReadTxns )
  ) i_axi_burst_splitter_ar_chan (
    .clk_i,
    .rst_ni,
    .ax_i           ( act_req.ar          ),
    .ax_valid_i     ( act_req.ar_valid    ),
    .ax_ready_o     ( act_resp.ar_ready   ),
    .ax_o           ( mst_req_o.ar        ),
    .ax_valid_o     ( mst_req_o.ar_valid  ),
    .ax_ready_i     ( mst_resp_i.ar_ready ),
    .cnt_id_i       ( mst_resp_i.r.id     ),
    .cnt_len_o      ( r_cnt_len           ),
    .cnt_set_err_i  ( 1'b0                ),
    .cnt_err_o      (                     ),
    .cnt_dec_i      ( r_cnt_dec           ),
    .cnt_req_i      ( r_cnt_req           ),
    .cnt_gnt_o      ( r_cnt_gnt           )
  );

  // --------------------------------------------------
  // R Channel
  // --------------------------------------------------
  // Reconstruct `last`, feed rest through.
  logic r_last_d, r_last_q;
  enum logic {RFeedthrough, RWait} r_state_d, r_state_q;
  always_comb begin
    r_cnt_dec         = 1'b0;
    r_cnt_req         = 1'b0;
    r_last_d          = r_last_q;
    r_state_d         = r_state_q;
    mst_req_o.r_ready = 1'b0;
    act_resp.r        = mst_resp_i.r;
    act_resp.r.last   = 1'b0;
    act_resp.r_valid  = 1'b0;

    unique case (r_state_q)
      RFeedthrough: begin
        // If downstream has an R beat and the R counters can give us the remaining length of
        // that burst, ...
        if (mst_resp_i.r_valid) begin
          r_cnt_req = 1'b1;
          if (r_cnt_gnt) begin
            r_last_d = (r_cnt_len == 8'd0);
            act_resp.r.last   = r_last_d;
            // Decrement the counter.
            r_cnt_dec         = 1'b1;
            // Try to forward the beat upstream.
            act_resp.r_valid  = 1'b1;
            if (act_req.r_ready) begin
              // Acknowledge downstream.
              mst_req_o.r_ready = 1'b1;
            end else begin
              // Wait for upstream to become ready.
              r_state_d = RWait;
            end
          end
        end
      end
      RWait: begin
        act_resp.r.last   = r_last_q;
        act_resp.r_valid  = mst_resp_i.r_valid;
        if (mst_resp_i.r_valid && act_req.r_ready) begin
          mst_req_o.r_ready = 1'b1;
          r_state_d         = RFeedthrough;
        end
      end
      default: /*do nothing*/;
    endcase
  end

  // --------------------------------------------------
  // Flip-Flops
  // --------------------------------------------------
  `FFARN(b_err_q, b_err_d, 1'b0, clk_i, rst_ni)
  `FFARN(b_state_q, b_state_d, BReady, clk_i, rst_ni)
  `FFARN(r_last_q, r_last_d, 1'b0, clk_i, rst_ni)
  `FFARN(r_state_q, r_state_d, RFeedthrough, clk_i, rst_ni)

  // --------------------------------------------------
  // Assumptions and assertions
  // --------------------------------------------------
  `ifndef VERILATOR
  // pragma translate_off
  default disable iff (!rst_ni);
  // Inputs
  assume property (@(posedge clk_i) slv_req_i.aw_valid |->
      txn_supported(slv_req_i.aw.atop, slv_req_i.aw.burst, slv_req_i.aw.cache, slv_req_i.aw.len)
    ) else $warning("Unsupported AW transaction received, returning slave error!");
  assume property (@(posedge clk_i) slv_req_i.ar_valid |->
      txn_supported('0, slv_req_i.ar.burst, slv_req_i.ar.cache, slv_req_i.ar.len)
    ) else $warning("Unsupported AR transaction received, returning slave error!");
  assume property (@(posedge clk_i) slv_req_i.aw_valid |->
      slv_req_i.aw.atop == '0 || slv_req_i.aw.atop[5:4] == axi_pkg::ATOP_ATOMICSTORE
    ) else $fatal(1, "Unsupported ATOP that gives rise to a R response received,\
                      cannot respond in protocol-compliant manner!");
  // Outputs
  assert property (@(posedge clk_i) mst_req_o.aw_valid |-> mst_req_o.aw.len == '0)
    else $fatal(1, "AW burst longer than a single beat emitted!");
  assert property (@(posedge clk_i) mst_req_o.ar_valid |-> mst_req_o.ar.len == '0)
    else $fatal(1, "AR burst longer than a single beat emitted!");
  // pragma translate_on
  `endif

endmodule

/// Internal module of [`axi_burst_splitter`](module.axi_burst_splitter) to control Ax channels.
///
/// Store burst lengths in counters, which are associated to AXI IDs through ID queues (to allow
/// reordering of responses w.r.t. requests).
module axi_burst_splitter_ax_chan #(
  parameter type         chan_t  = logic,
  parameter int unsigned IdWidth = 0,
  parameter int unsigned MaxTxns = 0,
  parameter type         id_t    = logic[IdWidth-1:0]
) (
  input  logic          clk_i,
  input  logic          rst_ni,

  input  chan_t         ax_i,
  input  logic          ax_valid_i,
  output logic          ax_ready_o,
  output chan_t         ax_o,
  output logic          ax_valid_o,
  input  logic          ax_ready_i,

  input  id_t           cnt_id_i,
  output axi_pkg::len_t cnt_len_o,
  input  logic          cnt_set_err_i,
  output logic          cnt_err_o,
  input  logic          cnt_dec_i,
  input  logic          cnt_req_i,
  output logic          cnt_gnt_o
);
  typedef logic[IdWidth-1:0] cnt_id_t;

  logic cnt_alloc_req, cnt_alloc_gnt;
  axi_burst_splitter_counters #(
    .MaxTxns ( MaxTxns  ),
    .IdWidth ( IdWidth  )
  ) i_axi_burst_splitter_counters (
    .clk_i,
    .rst_ni,
    .alloc_id_i     ( ax_i.id       ),
    .alloc_len_i    ( ax_i.len      ),
    .alloc_req_i    ( cnt_alloc_req ),
    .alloc_gnt_o    ( cnt_alloc_gnt ),
    .cnt_id_i       ( cnt_id_i      ),
    .cnt_len_o      ( cnt_len_o     ),
    .cnt_set_err_i  ( cnt_set_err_i ),
    .cnt_err_o      ( cnt_err_o     ),
    .cnt_dec_i      ( cnt_dec_i     ),
    .cnt_req_i      ( cnt_req_i     ),
    .cnt_gnt_o      ( cnt_gnt_o     )
  );

  chan_t ax_d, ax_q;

  enum logic {Idle, Busy} state_d, state_q;
  always_comb begin
    cnt_alloc_req = 1'b0;
    ax_d          = ax_q;
    state_d       = state_q;
    ax_o          = '0;
    ax_valid_o    = 1'b0;
    ax_ready_o    = 1'b0;
    unique case (state_q)
      Idle: begin
        if (ax_valid_i && cnt_alloc_gnt) begin
          if (ax_i.len == '0) begin // No splitting required -> feed through.
            ax_o       = ax_i;
            ax_valid_o = 1'b1;
            // As soon as downstream is ready, allocate a counter and acknowledge upstream.
            if (ax_ready_i) begin
              cnt_alloc_req = 1'b1;
              ax_ready_o    = 1'b1;
            end
          end else begin // Splitting required.
            // Store Ax, allocate a counter, and acknowledge upstream.
            ax_d          = ax_i;
            cnt_alloc_req = 1'b1;
            ax_ready_o    = 1'b1;
            // Try to feed first burst through.
            ax_o       = ax_d;
            ax_o.len   = '0;
            ax_valid_o = 1'b1;
            if (ax_ready_i) begin
              // Reduce number of bursts still to be sent by one and increment address.
              ax_d.len--;
              if (ax_d.burst == axi_pkg::BURST_INCR) begin
                ax_d.addr += (1 << ax_d.size);
              end
            end
            state_d = Busy;
          end
        end
      end
      Busy: begin
        // Sent next burst from split.
        ax_o       = ax_q;
        ax_o.len   = '0;
        ax_valid_o = 1'b1;
        if (ax_ready_i) begin
          if (ax_q.len == '0) begin
            // If this was the last burst, go back to idle.
            state_d = Idle;
          end else begin
            // Otherwise, continue with the next burst.
            ax_d.len--;
            if (ax_q.burst == axi_pkg::BURST_INCR) begin
              ax_d.addr += (1 << ax_q.size);
            end
          end
        end
      end
      default: /*do nothing*/;
    endcase
  end

  // registers
  `FFARN(ax_q, ax_d, '0, clk_i, rst_ni)
  `FFARN(state_q, state_d, Idle, clk_i, rst_ni)
endmodule

/// Internal module of [`axi_burst_splitter`](module.axi_burst_splitter) to order transactions.
module axi_burst_splitter_counters #(
  parameter int unsigned MaxTxns = 0,
  parameter int unsigned IdWidth = 0,
  parameter type         id_t    = logic [IdWidth-1:0]
) (
  input  logic          clk_i,
  input  logic          rst_ni,

  input  id_t           alloc_id_i,
  input  axi_pkg::len_t alloc_len_i,
  input  logic          alloc_req_i,
  output logic          alloc_gnt_o,

  input  id_t           cnt_id_i,
  output axi_pkg::len_t cnt_len_o,
  input  logic          cnt_set_err_i,
  output logic          cnt_err_o,
  input  logic          cnt_dec_i,
  input  logic          cnt_req_i,
  output logic          cnt_gnt_o
);
  localparam int unsigned CntIdxWidth = (MaxTxns > 1) ? $clog2(MaxTxns) : 32'd1;
  typedef logic [CntIdxWidth-1:0]         cnt_idx_t;
  typedef logic [$bits(axi_pkg::len_t):0] cnt_t;
  logic [MaxTxns-1:0]  cnt_dec, cnt_free, cnt_set, err_d, err_q;
  cnt_t                cnt_inp;
  cnt_t [MaxTxns-1:0]  cnt_oup;
  cnt_idx_t            cnt_free_idx, cnt_r_idx;
  for (genvar i = 0; i < MaxTxns; i++) begin : gen_cnt
    counter #(
      .WIDTH ( $bits(cnt_t) )
    ) i_cnt (
      .clk_i,
      .rst_ni,
      .clear_i    ( 1'b0       ),
      .en_i       ( cnt_dec[i] ),
      .load_i     ( cnt_set[i] ),
      .down_i     ( 1'b1       ),
      .d_i        ( cnt_inp    ),
      .q_o        ( cnt_oup[i] ),
      .overflow_o (            )  // not used
    );
    assign cnt_free[i] = (cnt_oup[i] == '0);
  end
  assign cnt_inp = {1'b0, alloc_len_i} + 1;

  lzc #(
    .WIDTH  ( MaxTxns ),
    .MODE   ( 1'b0    )  // start counting at index 0
  ) i_lzc (
    .in_i    ( cnt_free     ),
    .cnt_o   ( cnt_free_idx ),
    .empty_o (              )
  );

  logic idq_inp_req, idq_inp_gnt,
        idq_oup_gnt, idq_oup_valid, idq_oup_pop;
  id_queue #(
    .ID_WIDTH ( $bits(id_t) ),
    .CAPACITY ( MaxTxns     ),
    .data_t   ( cnt_idx_t   )
  ) i_idq (
    .clk_i,
    .rst_ni,
    .inp_id_i         ( alloc_id_i    ),
    .inp_data_i       ( cnt_free_idx  ),
    .inp_req_i        ( idq_inp_req   ),
    .inp_gnt_o        ( idq_inp_gnt   ),
    .exists_data_i    ( '0            ),
    .exists_mask_i    ( '0            ),
    .exists_req_i     ( 1'b0          ),
    .exists_o         (/* keep open */),
    .exists_gnt_o     (/* keep open */),
    .oup_id_i         ( cnt_id_i      ),
    .oup_pop_i        ( idq_oup_pop   ),
    .oup_req_i        ( cnt_req_i     ),
    .oup_data_o       ( cnt_r_idx     ),
    .oup_data_valid_o ( idq_oup_valid ),
    .oup_gnt_o        ( idq_oup_gnt   )
  );
  assign idq_inp_req = alloc_req_i & alloc_gnt_o;
  assign alloc_gnt_o = idq_inp_gnt & |(cnt_free);
  assign cnt_gnt_o   = idq_oup_gnt & idq_oup_valid;
  logic [8:0] read_len;
  assign read_len    = cnt_oup[cnt_r_idx] - 1;
  assign cnt_len_o   = read_len[7:0];

  assign idq_oup_pop = cnt_req_i & cnt_gnt_o & cnt_dec_i & (cnt_len_o == 8'd0);
  always_comb begin
    cnt_dec            = '0;
    cnt_dec[cnt_r_idx] = cnt_req_i & cnt_gnt_o & cnt_dec_i;
  end
  always_comb begin
    cnt_set               = '0;
    cnt_set[cnt_free_idx] = alloc_req_i & alloc_gnt_o;
  end
  always_comb begin
    err_d     = err_q;
    cnt_err_o = err_q[cnt_r_idx];
    if (cnt_req_i && cnt_gnt_o && cnt_set_err_i) begin
      err_d[cnt_r_idx] = 1'b1;
      cnt_err_o        = 1'b1;
    end
    if (alloc_req_i && alloc_gnt_o) begin
      err_d[cnt_free_idx] = 1'b0;
    end
  end

  // registers
  `FFARN(err_q, err_d, '0, clk_i, rst_ni)

  `ifndef VERILATOR
  // pragma translate_off
  assume property (@(posedge clk_i) idq_oup_gnt |-> idq_oup_valid)
    else $warning("Invalid output at ID queue, read not granted!");
  // pragma translate_on
  `endif

endmodule
