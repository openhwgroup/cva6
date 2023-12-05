// Copyright 2020 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Authors:
// - Wolfgang Roenninger <wroennin@iis.ee.ethz.ch>

/// # AXI4-Lite data width downsize module.
///
/// ## Down Conversion
///
/// The module will be in this mode if `AxiSlvPortDataWidth > AxiMstPortDataWidth`.
/// The module does multiple transactions on the master port for each transaction of the salve port.
///
/// The address on the master port will be aligned to the bus width, regardless what the input
/// address was. The number of transactions generated on the master port is equal to the
/// `DownsizeFactor = AxiSlvPortDataWidth / AxiMstPortDataWidth`.
///
/// Eg: `AxiAddrWidth == 32'd16`, `AxiSlvPortDataWidth == 32'64`, `AxiMstPortDataWidth == 32'd32'
///     This is for write transactions. Reads are accessing the whole width of the slave port.
///
///
/// | EG NUM | SLV ADDR | SLV W DATA         | SLV W STRB | MST ADDR | MST W DATA | MST W STRB |
/// |--------|----------|--------------------|------------|----------|------------|------------|
/// |      1 | 0x0000   | 0xBEEFBEEFAAAABBBB | 0xAB       | 0x0000   | 0xAAAABBBB | 0xB        |
/// |      1 |          |                    |            | 0x0004   | 0xBEEFBEEF | 0xA        |
/// |        |          |                    |            |          |            |            |
/// |      2 | 0x0000   | 0xBEEFBEEFAAAABBBB | 0xF0       | 0x0000   | 0xAAAABBBB | 0x0        |
/// |      2 |          |                    |            | 0x0004   | 0xBEEFBEEF | 0xF        |
/// |        |          |                    |            |          |            |            |
/// |      3 | 0x0004   | 0xBEEFBEEFAAAABBBB | 0xF0       | 0x0000   | 0xAAAABBBB | 0x0        |
/// |      3 |          |                    |            | 0x0004   | 0xBEEFBEEF | 0xF        |
/// |        |          |                    |            |          |            |            |
/// |      4 | 0x0004   | 0xBEEFBEEFAAAABBBB | 0x0F       | 0x0000   | 0xAAAABBBB | 0xF        |
/// |      4 |          |                    |            | 0x0004   | 0xBEEFBEEF | 0x0        |
/// |        |          |                    |            |          |            |            |
/// |      5 | 0x0005   | 0xBEEFBE0000000000 | 0xE0       | 0x0000   | 0x00000000 | 0x0        |
/// |      5 |          |                    |            | 0x0004   | 0xBEEFBE00 | 0xE        |
///
/// Response field is aggregated (OR'ed) between the multiple requests made on the master port.
/// If one of the requests on the master port errors, the error response of the request
/// on the slave port will also signal an error.
///
/// ## Up conversion
///
/// The module will be in this mode if `AxiSlvPortDataWidth < AxiMstPortDataWidth`.
/// This mode will generate the same amount of transactions on the master port as on the slave port.
/// Data is replicated to match the bus width. Write strobes are silenced for the byte lanes not
/// written.
///
/// ## Pass Through
///
/// The module will be in this mode if `AxiSlvPortDataWidth == AxiMstPortDataWidth`.
/// Here the module passes through the slave port to the master port.
`include "common_cells/registers.svh"
module axi_lite_dw_converter #(
  /// AXI4-Lite address width of the ports.
  parameter int unsigned AxiAddrWidth        = 32'd0,
  /// AXI4-Lite data width of the slave port.
  parameter int unsigned AxiSlvPortDataWidth = 32'd0,
  /// AXI4-Lite data width of the master port.
  parameter int unsigned AxiMstPortDataWidth = 32'd0,
  /// AXI4-Lite AW channel struct type. This is for both ports the same.
  parameter type         axi_lite_aw_t       = logic,
  /// AXI4-Lite W channel struct type of the slave port.
  parameter type         axi_lite_slv_w_t    = logic,
  /// AXI4-Lite W channel struct type of the master port.
  parameter type         axi_lite_mst_w_t    = logic,
  /// AXI4-Lite B channel struct type. This is for both ports.
  parameter type         axi_lite_b_t        = logic,
  /// AXI4-Lite AR channel struct type. This is for both ports.
  parameter type         axi_lite_ar_t       = logic,
  /// AXI4-Lite R channel struct type of the slave port.
  parameter type         axi_lite_slv_r_t    = logic,
  /// AXI4-Lite R channel struct type of the master port.
  parameter type         axi_lite_mst_r_t    = logic,
  /// AXI4-Lite request struct of the slave port.
  parameter type         axi_lite_slv_req_t  = logic,
  /// AXI4-Lite response struct of the slave port.
  parameter type         axi_lite_slv_res_t  = logic,
  /// AXI4-Lite request struct of the master port.
  parameter type         axi_lite_mst_req_t  = logic,
  /// AXI4-Lite response struct of the master port.
  parameter type         axi_lite_mst_res_t  = logic
) (
  /// Clock, positive edge triggered.
  input  logic               clk_i,
  /// Asynchrounous reset, active low.
  input  logic               rst_ni,
  /// Salve port, AXI4-Lite request.
  input  axi_lite_slv_req_t  slv_req_i,
  /// Salve port, AXI4-Lite response.
  output axi_lite_slv_res_t  slv_res_o,
  /// Master port, AXI4-Lite request.
  output axi_lite_mst_req_t  mst_req_o,
  /// Master port, AXI4-Lite response.
  input  axi_lite_mst_res_t  mst_res_i
);
  // Strobe parameter for the two AXI4-Lite ports.
  localparam int unsigned AxiSlvPortStrbWidth = AxiSlvPortDataWidth / 32'd8;
  localparam int unsigned AxiMstPortStrbWidth = AxiMstPortDataWidth / 32'd8;
  typedef logic [AxiAddrWidth-1:0] addr_t;

  // AXI4-Lite downsizer
  if (AxiSlvPortDataWidth > AxiMstPortDataWidth) begin : gen_downsizer
    // The Downsize factor determines how often the data channel has to be multiplexed.
    localparam int unsigned DownsizeFactor = AxiSlvPortDataWidth / AxiMstPortDataWidth;
    // Selection width for choosing the byte lanes.
    localparam int unsigned SelWidth       = $clog2(DownsizeFactor);
    // Type for the selection signal.
    typedef logic [SelWidth-1:0] sel_t;
    // Offset determines, which part of the address corresponds to the `w_chan_sel` signal.
    localparam int unsigned SelOffset      = $clog2(AxiMstPortStrbWidth);

    // Calculate the output address for the master port.
    // `address`: The address as seen on the salve port.
    // `sel`: T   The current selection.
    // `l_zero`:  If set, the lowest bits are zero, for all generated addresses after the first.
    function automatic addr_t out_address(input addr_t address, input sel_t sel);
      out_address                      = address;
      out_address[SelOffset+:SelWidth] = sel;
      out_address[SelOffset-1:0]       = SelOffset'(0);
    endfunction : out_address

    // Write channels.
    // Input spill register of the AW channel.
    axi_lite_aw_t aw_chan_spill;
    logic         aw_chan_spill_valid, aw_chan_spill_ready;

    spill_register #(
      .T      ( axi_lite_aw_t ),
      .Bypass ( 1'b0          )
    ) i_spill_register_aw (
      .clk_i,
      .rst_ni,
      .valid_i ( slv_req_i.aw_valid  ),
      .ready_o ( slv_res_o.aw_ready  ),
      .data_i  ( slv_req_i.aw        ),
      .valid_o ( aw_chan_spill_valid ),
      .ready_i ( aw_chan_spill_ready ),
      .data_o  ( aw_chan_spill       )
    );

    sel_t aw_sel_q,    aw_sel_d;
    logic aw_sel_load;
    // AW channel output assignment
    always_comb begin : proc_aw_chan_oup
      mst_req_o.aw      = aw_chan_spill;
      mst_req_o.aw.addr = out_address(aw_chan_spill.addr, aw_sel_q);
    end
    // Slave port aw is valid, if there is something in the spill register.
    assign mst_req_o.aw_valid  = aw_chan_spill_valid;
    assign aw_chan_spill_ready = mst_res_i.aw_ready & (&aw_sel_q);

    assign aw_sel_load = mst_req_o.aw_valid & mst_res_i.aw_ready;
    assign aw_sel_d    = sel_t'(aw_sel_q + 1'b1);
    `FFLARN(aw_sel_q, aw_sel_d, aw_sel_load, '0, clk_i, rst_ni)

    // Input spill register of the W channel.
    axi_lite_slv_w_t w_chan_spill;
    logic            w_chan_spill_valid, w_chan_spill_ready;
    spill_register #(
      .T      ( axi_lite_slv_w_t ),
      .Bypass ( 1'b0             )
    ) i_spill_register_w (
      .clk_i,
      .rst_ni,
      .valid_i ( slv_req_i.w_valid  ),
      .ready_o ( slv_res_o.w_ready  ),
      .data_i  ( slv_req_i.w        ),
      .valid_o ( w_chan_spill_valid ),
      .ready_i ( w_chan_spill_ready ),
      .data_o  ( w_chan_spill       )
    );

    // Data multiplexer on the W channel
    sel_t w_sel_q,    w_sel_d;
    logic w_sel_load;
    // W channel output assignment
    assign mst_req_o.w = axi_lite_mst_w_t'{
      data:    w_chan_spill.data[w_sel_q*AxiMstPortDataWidth+:AxiMstPortDataWidth],
      strb:    w_chan_spill.strb[w_sel_q*AxiMstPortStrbWidth+:AxiMstPortStrbWidth],
      default: '0
    };
    assign mst_req_o.w_valid  = w_chan_spill_valid;
    assign w_chan_spill_ready = mst_res_i.w_ready & (&w_sel_q);

    assign w_sel_load = mst_req_o.w_valid & mst_res_i.w_ready;
    assign w_sel_d    = sel_t'(w_sel_q + 1'b1);
    `FFLARN(w_sel_q, w_sel_d, w_sel_load, '0, clk_i, rst_ni)

    // B response aggregation
    // Slave port B output is the aggregated error of the last few B responses.
    sel_t           b_sel_q,     b_sel_d;
    axi_pkg::resp_t b_resp_q,    b_resp_d;
    logic           b_resp_load;

    assign slv_res_o.b = axi_lite_b_t'{
      resp:    b_resp_q | mst_res_i.b.resp,
      default: '0
    };
    // Output is valid, if it is the last b response for the wide W, we have something
    // in the B FIFO and the B response is valid from the master port.
    assign slv_res_o.b_valid = mst_res_i.b_valid & (&b_sel_q);

    // Assign the b_channel ready output. The master port is ready if something is in the
    // B FIFO. Except, if it is the last one which should do a response on the slave port.
    assign mst_req_o.b_ready = (&b_sel_q) ? slv_req_i.b_ready : 1'b1;
    // B channel error response retention FF
    assign b_sel_d     = sel_t'(b_sel_q + 1'b1);
    assign b_resp_d    = (&b_sel_q) ? axi_pkg::RESP_OKAY : (b_resp_q | mst_res_i.b.resp);
    assign b_resp_load = mst_res_i.b_valid & mst_req_o.b_ready;
    `FFLARN(b_sel_q, b_sel_d, b_resp_load, '0, clk_i, rst_ni)
    `FFLARN(b_resp_q, b_resp_d, b_resp_load, axi_pkg::RESP_OKAY, clk_i, rst_ni)

    // Read channels.
    // Input spill register of the AW channel.
    axi_lite_ar_t ar_chan_spill;
    logic         ar_chan_spill_valid, ar_chan_spill_ready;

    spill_register #(
      .T      ( axi_lite_ar_t ),
      .Bypass ( 1'b0          )
    ) i_spill_register_ar (
      .clk_i,
      .rst_ni,
      .valid_i ( slv_req_i.ar_valid  ),
      .ready_o ( slv_res_o.ar_ready  ),
      .data_i  ( slv_req_i.ar        ),
      .valid_o ( ar_chan_spill_valid ),
      .ready_i ( ar_chan_spill_ready ),
      .data_o  ( ar_chan_spill       )
    );

    sel_t ar_sel_q,    ar_sel_d;
    logic ar_sel_load;
    // AR channel output assignment
    always_comb begin : proc_ar_chan_oup
      mst_req_o.ar      = ar_chan_spill;
      mst_req_o.ar.addr = out_address(ar_chan_spill.addr, ar_sel_q);
    end
    // Slave port aw is valid, if there is something in the spill register.
    assign mst_req_o.ar_valid  = ar_chan_spill_valid;
    assign ar_chan_spill_ready = mst_res_i.ar_ready & (&ar_sel_q);

    assign ar_sel_load = mst_req_o.ar_valid & mst_res_i.ar_ready;
    assign ar_sel_d    = sel_t'(ar_sel_q + 1'b1);
    `FFLARN(ar_sel_q, ar_sel_d, ar_sel_load, '0, clk_i, rst_ni)

    // Responses have to be aggregated, one FF less, as the last data is feed directly through.
    sel_t                                 r_sel_q,        r_sel_d;
    logic                                 r_sel_load;
    axi_lite_mst_r_t [DownsizeFactor-2:0] r_chan_mst_q;
    logic            [DownsizeFactor-2:0] r_chan_mst_load;
    for (genvar i = 0; unsigned'(i) < (DownsizeFactor-1); i++) begin : gen_r_chan_ff
      assign r_chan_mst_load[i] = (sel_t'(i) == r_sel_q) & mst_res_i.r_valid & mst_req_o.r_ready;
      `FFLARN(r_chan_mst_q[i], mst_res_i.r, r_chan_mst_load[i], axi_lite_mst_r_t'{default: '0}, clk_i, rst_ni)
    end
    assign r_sel_load = mst_res_i.r_valid & mst_req_o.r_ready;
    assign r_sel_d    = sel_t'(r_sel_q + 1'b1);
    `FFLARN(r_sel_q, r_sel_d, r_sel_load, '0, clk_i, rst_ni)

    always_comb begin : proc_r_chan_oup
      slv_res_o.r = axi_lite_slv_r_t'{
        resp:    mst_res_i.r.resp,
        default: '0
      };
      // Response is the OR of all responses
      for (int unsigned i = 0; i < (DownsizeFactor-1); i++) begin
        slv_res_o.r.resp = slv_res_o.r.resp | r_chan_mst_q[i].resp;
        slv_res_o.r.data[i*AxiMstPortDataWidth+:AxiMstPortDataWidth] = r_chan_mst_q[i].data;
      end
      // The highest bits of the data can be directly the master port.
      slv_res_o.r.data[(DownsizeFactor-1)*AxiMstPortDataWidth+:AxiMstPortDataWidth] =
          mst_res_i.r.data;
    end

    assign slv_res_o.r_valid = (&r_sel_q) ? mst_res_i.r_valid : 1'b0;
    assign mst_req_o.r_ready = (&r_sel_q) ? slv_req_i.r_ready : 1'b1;

  end else if (AxiMstPortDataWidth > AxiSlvPortDataWidth) begin : gen_upsizer
    // The upsize factor determines the amount of replication.
    localparam int unsigned UpsizeFactor = AxiMstPortDataWidth / AxiSlvPortDataWidth;

    // Selection type and offset for the address
    localparam int unsigned SelOffset = $clog2(AxiSlvPortStrbWidth);
    localparam int unsigned SelWidth  = $clog2(UpsizeFactor);
    typedef logic [SelWidth-1:0] sel_t;

    // AW channel can be passed through, however block handshake if FIFO is full.
    assign mst_req_o.aw       = slv_req_i.aw;
    // Lock the valid on the master port if it has been given.
    logic lock_aw_q, lock_aw_d, load_aw_lock;
    // W channel needs a FIFO to determine the silencing of the strobe signal.
    logic w_full, w_empty, w_push, w_pop;
    sel_t aw_sel, w_sel;

    // AW channel handshake control
    always_comb begin : proc_aw_handshake
      // default assignment
      load_aw_lock       = 1'b0; // the FF is toggling back and forth when loaded.
      mst_req_o.aw_valid = 1'b0;
      slv_res_o.aw_ready = 1'b0;
      w_push             = 1'b0;

      if (lock_aw_q) begin
        mst_req_o.aw_valid = 1'b1;
        slv_res_o.aw_ready = mst_res_i.aw_ready;
        if (mst_res_i.aw_ready) begin
          load_aw_lock = 1'b1;
        end
      end else begin
        // Only connect handshake if there is space in the FIFO
        if (!w_full) begin
          mst_req_o.aw_valid = slv_req_i.aw_valid;
          slv_res_o.aw_ready = mst_res_i.aw_ready;
          // If there is a valid on the slave port, push the FIFO
          if (slv_req_i.aw_valid) begin
            w_push = 1'b1;
            // When no transaction, lock AW
            if (!mst_res_i.aw_ready) begin
              load_aw_lock = 1'b1;
            end
          end
        end
      end
    end
    assign lock_aw_d = ~lock_aw_q;
    `FFLARN(lock_aw_q, lock_aw_d, load_aw_lock, 1'b0, clk_i, rst_ni)

    // The selection comes from part of the AW address.
    assign aw_sel = sel_t'(slv_req_i.aw.addr >> SelOffset);

    fifo_v3 #(
      .FALL_THROUGH ( 1'b1         ),
      .DEPTH        ( UpsizeFactor ),
      .dtype        ( sel_t        )
    ) i_fifo_w_sel (
      .clk_i,
      .rst_ni,
      .flush_i    ( 1'b0         ),
      .testmode_i ( 1'b0         ),
      .full_o     ( w_full       ),
      .empty_o    ( w_empty      ),
      .usage_o    ( /*not used*/ ),
      .data_i     ( aw_sel       ),
      .push_i     ( w_push       ),
      .data_o     ( w_sel        ),
      .pop_i      ( w_pop        )
    );
    // Pop if there is a W transaction on the master port.
    assign w_pop = mst_req_o.w_valid & mst_res_i.w_ready;

    // Replicate Data but silence strobe signal.
    assign mst_req_o.w = axi_lite_mst_w_t'{
      data:    {UpsizeFactor{slv_req_i.w.data}},
      strb:    {AxiMstPortStrbWidth{1'b0}} | (slv_req_i.w.strb << (w_sel * AxiSlvPortStrbWidth)),
      default: '0
    };

    // Connect W handshake if the selection is in the FIFO
    assign mst_req_o.w_valid = slv_req_i.w_valid & ~w_empty;
    assign slv_res_o.w_ready = mst_res_i.w_ready & ~w_empty;


    // B channel can be passed through
    assign slv_res_o.b       = mst_res_i.b;
    assign slv_res_o.b_valid = mst_res_i.b_valid;
    assign mst_req_o.b_ready = slv_req_i.b_ready;


    // AR channel can be passed through, however block handshake if FIFO is full.
    assign mst_req_o.ar       = slv_req_i.ar;
    // Lock the valid on the master port if it has been given.
    logic lock_ar_q, lock_ar_d, load_ar_lock;
    // W channel needs a FIFO to determine the silencing of the strobe signal.
    logic r_full, r_empty, r_push, r_pop;
    sel_t ar_sel, r_sel;

    // AW channel handshake control
    always_comb begin : proc_ar_handshake
      // default assignment
      load_ar_lock       = 1'b0; // the FF is toggling back and forth when loaded.
      mst_req_o.ar_valid = 1'b0;
      slv_res_o.ar_ready = 1'b0;
      r_push             = 1'b0;

      if (lock_ar_q) begin
        mst_req_o.ar_valid = 1'b1;
        slv_res_o.ar_ready = mst_res_i.ar_ready;
        if (mst_res_i.ar_ready) begin
          load_ar_lock = 1'b1;
        end
      end else begin
        // Only connect handshake if there is space in the FIFO
        if (!r_full) begin
          mst_req_o.ar_valid = slv_req_i.ar_valid;
          slv_res_o.ar_ready = mst_res_i.ar_ready;
          // If there is a valid on the slave port, push the FIFO
          if (slv_req_i.ar_valid) begin
            r_push = 1'b1;
            // When no transaction, lock AW
            if (!mst_res_i.ar_ready) begin
              load_ar_lock = 1'b1;
            end
          end
        end
      end
    end
    assign lock_ar_d = ~lock_ar_q;
    `FFLARN(lock_ar_q, lock_ar_d, load_ar_lock, 1'b0, clk_i, rst_ni)

    // The selection comes from part of the AW address.
    assign ar_sel = sel_t'(slv_req_i.ar.addr >> SelOffset);

    fifo_v3 #(
      .FALL_THROUGH ( 1'b1         ),
      .DEPTH        ( UpsizeFactor ),
      .dtype        ( sel_t        )
    ) i_fifo_r_sel (
      .clk_i,
      .rst_ni,
      .flush_i    ( 1'b0         ),
      .testmode_i ( 1'b0         ),
      .full_o     ( r_full       ),
      .empty_o    ( r_empty      ),
      .usage_o    ( /*not used*/ ),
      .data_i     ( ar_sel       ),
      .push_i     ( r_push       ),
      .data_o     ( r_sel        ),
      .pop_i      ( r_pop        )
    );
    // Pop if there is a R transaction on the slave port.
    assign r_pop = slv_res_o.r_valid & slv_req_i.r_ready;

    // R channel has to be cut out
    assign slv_res_o.r = axi_lite_slv_r_t'{
      data: mst_res_i.r.data[(r_sel*AxiSlvPortDataWidth)+:AxiSlvPortDataWidth],
      resp: mst_res_i.r.resp,
      default: '0
    };
    // Connect R handshake if there is something in the FIFO.
    assign slv_res_o.r_valid = mst_res_i.r_valid & ~r_empty;
    assign mst_req_o.r_ready = slv_req_i.r_ready & ~r_empty;

  end else begin : gen_passthrough
    assign mst_req_o = slv_req_i;
    assign slv_res_o = mst_res_i;
  end

  // Assertions, check params
  // pragma translate_off
  `ifndef VERILATOR
  initial begin
    assume (AxiAddrWidth        > 0) else $fatal(1, "AXI address width has to be > 0");
    assume (AxiSlvPortDataWidth > 8) else $fatal(1, "AxiSlvPortDataWidth has to be > 8");
    assume (AxiMstPortDataWidth > 8) else $fatal(1, "AxiMstPortDataWidth has to be > 8");
    assume ($onehot(AxiSlvPortDataWidth)) else $fatal(1, "AxiSlvPortDataWidth must be power of 2");
    assume ($onehot(AxiMstPortDataWidth)) else $fatal(1, "AxiMstPortDataWidth must be power of 2");
  end
  default disable iff (~rst_ni);
  stable_aw: assert property (@(posedge clk_i)
      (mst_req_o.aw_valid && !mst_res_i.aw_ready) |=> $stable(mst_req_o.aw)) else
      $fatal(1, "AW must remain stable until handshake happened.");
  stable_w:  assert property (@(posedge clk_i)
      (mst_req_o.w_valid  && !mst_res_i.w_ready)  |=> $stable(mst_req_o.w)) else
      $fatal(1, "W must remain stable until handshake happened.");
  stable_b:  assert property (@(posedge clk_i)
      (slv_res_o.b_valid  && !slv_req_i.b_ready)  |=> $stable(slv_res_o.b)) else
      $fatal(1, "B must remain stable until handshake happened.");
  stable_ar: assert property (@(posedge clk_i)
      (mst_req_o.ar_valid && !mst_res_i.ar_ready) |=> $stable(mst_req_o.ar)) else
      $fatal(1, "AR must remain stable until handshake happened.");
  stable_r:  assert property (@(posedge clk_i)
      (slv_res_o.r_valid  && !slv_req_i.r_ready)  |=> $stable(slv_res_o.r)) else
      $fatal(1, "R must remain stable until handshake happened.");
  `endif
  // pragma translate_on
endmodule

/// Interface wrapper for `axi_lite_dw_converter`.
`include "axi/typedef.svh"
`include "axi/assign.svh"
module axi_lite_dw_converter_intf #(
  /// AXI4-Lite address width of the ports.
  parameter int unsigned AXI_ADDR_WIDTH          = 32'd0,
  /// AXI4-Lite data width of the slave port.
  parameter int unsigned AXI_SLV_PORT_DATA_WIDTH = 32'd0,
  /// AXI4-Lite data width of the master port.
  parameter int unsigned AXI_MST_PORT_DATA_WIDTH = 32'd0
) (
  /// Clock, positive edge triggered.
  input  logic    clk_i,
  /// Asynchrounous reset, active low.
  input  logic    rst_ni,
  /// Slave port interface.
  AXI_LITE.Slave  slv,
  /// Master port interface.
  AXI_LITE.Master mst
);
  // AXI configuration
  localparam int unsigned AxiStrbWidthSlv =  AXI_SLV_PORT_DATA_WIDTH / 32'd8;
  localparam int unsigned AxiStrbWidthMst =  AXI_MST_PORT_DATA_WIDTH / 32'd8;
  // Type definitions
  typedef logic [AXI_ADDR_WIDTH-1:0]          lite_addr_t;
  typedef logic [AXI_SLV_PORT_DATA_WIDTH-1:0] lite_data_slv_t;
  typedef logic [AxiStrbWidthSlv-1:0]         lite_strb_slv_t;
  typedef logic [AXI_MST_PORT_DATA_WIDTH-1:0] lite_data_mst_t;
  typedef logic [AxiStrbWidthMst-1:0]         lite_strb_mst_t;


  `AXI_LITE_TYPEDEF_AW_CHAN_T(aw_chan_lite_t, lite_addr_t)
  `AXI_LITE_TYPEDEF_W_CHAN_T(w_chan_lite_slv_t, lite_data_slv_t, lite_strb_slv_t)
  `AXI_LITE_TYPEDEF_W_CHAN_T(w_chan_lite_mst_t, lite_data_mst_t, lite_strb_mst_t)
  `AXI_LITE_TYPEDEF_B_CHAN_T(b_chan_lite_t)

  `AXI_LITE_TYPEDEF_AR_CHAN_T(ar_chan_lite_t, lite_addr_t)
  `AXI_LITE_TYPEDEF_R_CHAN_T(r_chan_lite_slv_t, lite_data_slv_t)
  `AXI_LITE_TYPEDEF_R_CHAN_T(r_chan_lite_mst_t, lite_data_mst_t)


  `AXI_LITE_TYPEDEF_REQ_T(req_lite_slv_t, aw_chan_lite_t, w_chan_lite_slv_t, ar_chan_lite_t)
  `AXI_LITE_TYPEDEF_RESP_T(res_lite_slv_t, b_chan_lite_t, r_chan_lite_slv_t)

  `AXI_LITE_TYPEDEF_REQ_T(req_lite_mst_t, aw_chan_lite_t, w_chan_lite_mst_t, ar_chan_lite_t)
  `AXI_LITE_TYPEDEF_RESP_T(res_lite_mst_t, b_chan_lite_t, r_chan_lite_mst_t)

  req_lite_slv_t slv_req;
  res_lite_slv_t slv_res;
  req_lite_mst_t mst_req;
  res_lite_mst_t mst_res;

  `AXI_LITE_ASSIGN_TO_REQ(slv_req, slv)
  `AXI_LITE_ASSIGN_FROM_RESP(slv, slv_res)
  `AXI_LITE_ASSIGN_FROM_REQ(mst, mst_req)
  `AXI_LITE_ASSIGN_TO_RESP(mst_res, mst)

  axi_lite_dw_converter #(
    .AxiAddrWidth        ( AXI_ADDR_WIDTH          ),
    .AxiSlvPortDataWidth ( AXI_SLV_PORT_DATA_WIDTH ),
    .AxiMstPortDataWidth ( AXI_MST_PORT_DATA_WIDTH ),
    .axi_lite_aw_t       ( aw_chan_lite_t          ),
    .axi_lite_slv_w_t    ( w_chan_lite_slv_t       ),
    .axi_lite_mst_w_t    ( w_chan_lite_mst_t       ),
    .axi_lite_b_t        ( b_chan_lite_t           ),
    .axi_lite_ar_t       ( ar_chan_lite_t          ),
    .axi_lite_slv_r_t    ( r_chan_lite_slv_t       ),
    .axi_lite_mst_r_t    ( r_chan_lite_mst_t       ),
    .axi_lite_slv_req_t  ( req_lite_slv_t          ),
    .axi_lite_slv_res_t  ( res_lite_slv_t          ),
    .axi_lite_mst_req_t  ( req_lite_mst_t          ),
    .axi_lite_mst_res_t  ( res_lite_mst_t          )
  ) i_axi_lite_dw_converter (
    .clk_i,
    .rst_ni,
    .slv_req_i ( slv_req ),
    .slv_res_o ( slv_res ),
    .mst_req_o ( mst_req ),
    .mst_res_i ( mst_res )
  );
endmodule
