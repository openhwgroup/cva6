// Copyright (c) 2019 ETH Zurich, University of Bologna
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

// AXI Multiplexer: This module multiplexes the AXI4 slave ports down to one master port.
// The AXI IDs from the slave ports get extended with the respective slave port index.
// The extension width can be calculated with `$clog2(NoSlvPorts)`. This means the AXI
// ID for the master port has to be this `$clog2(NoSlvPorts)` wider than the ID for the
// slave ports.
// Responses are switched based on these bits. For example, with 4 slave ports
// a response with ID `6'b100110` will be forwarded to slave port 2 (`2'b10`).

// register macros
`include "common_cells/registers.svh"

module axi_mux #(
  // AXI parameter and channel types
  parameter int unsigned SlvAxiIDWidth = 32'd0, // AXI ID width, slave ports
  parameter type         slv_aw_chan_t = logic, // AW Channel Type, slave ports
  parameter type         mst_aw_chan_t = logic, // AW Channel Type, master port
  parameter type         w_chan_t      = logic, //  W Channel Type, all ports
  parameter type         slv_b_chan_t  = logic, //  B Channel Type, slave ports
  parameter type         mst_b_chan_t  = logic, //  B Channel Type, master port
  parameter type         slv_ar_chan_t = logic, // AR Channel Type, slave ports
  parameter type         mst_ar_chan_t = logic, // AR Channel Type, master port
  parameter type         slv_r_chan_t  = logic, //  R Channel Type, slave ports
  parameter type         mst_r_chan_t  = logic, //  R Channel Type, master port
  parameter type         slv_req_t     = logic, // Slave port request type
  parameter type         slv_resp_t    = logic, // Slave port response type
  parameter type         mst_req_t     = logic, // Master ports request type
  parameter type         mst_resp_t    = logic, // Master ports response type
  parameter int unsigned NoSlvPorts    = 32'd0, // Number of slave ports
  // Maximum number of outstanding transactions per write
  parameter int unsigned MaxWTrans     = 32'd8,
  // If enabled, this multiplexer is purely combinatorial
  parameter bit          FallThrough   = 1'b0,
  // add spill register on write master ports, adds a cycle latency on write channels
  parameter bit          SpillAw       = 1'b1,
  parameter bit          SpillW        = 1'b0,
  parameter bit          SpillB        = 1'b0,
  // add spill register on read master ports, adds a cycle latency on read channels
  parameter bit          SpillAr       = 1'b1,
  parameter bit          SpillR        = 1'b0
) (
  input  logic                       clk_i,    // Clock
  input  logic                       rst_ni,   // Asynchronous reset active low
  input  logic                       test_i,   // Test Mode enable
  // slave ports (AXI inputs), connect master modules here
  input  slv_req_t  [NoSlvPorts-1:0] slv_reqs_i,
  output slv_resp_t [NoSlvPorts-1:0] slv_resps_o,
  // master port (AXI outputs), connect slave modules here
  output mst_req_t                   mst_req_o,
  input  mst_resp_t                  mst_resp_i
);

  localparam int unsigned MstIdxBits    = $clog2(NoSlvPorts);
  localparam int unsigned MstAxiIDWidth = SlvAxiIDWidth + MstIdxBits;

  // pass through if only one slave port
  if (NoSlvPorts == 32'h1) begin : gen_no_mux
    assign mst_req_o      = slv_reqs_i[0];
    assign slv_resps_o[0] = mst_resp_i;
  // other non degenerate cases
  end else begin : gen_mux

    typedef logic [MstIdxBits-1:0] switch_id_t;

    // AXI channels between the ID prepend unit and the rest of the multiplexer
    mst_aw_chan_t [NoSlvPorts-1:0] slv_aw_chans;
    logic         [NoSlvPorts-1:0] slv_aw_valids, slv_aw_readies;
    w_chan_t      [NoSlvPorts-1:0] slv_w_chans;
    logic         [NoSlvPorts-1:0] slv_w_valids,  slv_w_readies;
    mst_b_chan_t  [NoSlvPorts-1:0] slv_b_chans;
    logic         [NoSlvPorts-1:0] slv_b_valids,  slv_b_readies;
    mst_ar_chan_t [NoSlvPorts-1:0] slv_ar_chans;
    logic         [NoSlvPorts-1:0] slv_ar_valids, slv_ar_readies;
    mst_r_chan_t  [NoSlvPorts-1:0] slv_r_chans;
    logic         [NoSlvPorts-1:0] slv_r_valids,  slv_r_readies;

    // These signals are all ID prepended
    // AW channel
    mst_aw_chan_t   mst_aw_chan;
    logic           mst_aw_valid, mst_aw_ready;

    // AW master handshake internal, so that we are able to stall, if w_fifo is full
    logic           aw_valid,     aw_ready;

    // FF to lock the AW valid signal, when a new arbitration decision is made the decision
    // gets pushed into the W FIFO, when it now stalls prevent subsequent pushing
    // This FF removes AW to W dependency
    logic           lock_aw_valid_d, lock_aw_valid_q;
    logic           load_aw_lock;

    // signals for the FIFO that holds the last switching decision of the AW channel
    logic           w_fifo_full,  w_fifo_empty;
    logic           w_fifo_push,  w_fifo_pop;
    switch_id_t     w_fifo_data;

    // W channel spill reg
    w_chan_t        mst_w_chan;
    logic           mst_w_valid,  mst_w_ready;

    // master ID in the b_id
    switch_id_t     switch_b_id;

    // B channel spill reg
    mst_b_chan_t    mst_b_chan;
    logic           mst_b_valid;

    // AR channel for when spill is enabled
    mst_ar_chan_t   mst_ar_chan;
    logic           ar_valid,     ar_ready;

    // master ID in the r_id
    switch_id_t     switch_r_id;

    // R channel spill reg
    mst_r_chan_t    mst_r_chan;
    logic           mst_r_valid;

    //--------------------------------------
    // ID prepend for all slave ports
    //--------------------------------------
    for (genvar i = 0; i < NoSlvPorts; i++) begin : gen_id_prepend
      axi_id_prepend #(
        .NoBus            ( 32'd1               ), // one AXI bus per slave port
        .AxiIdWidthSlvPort( SlvAxiIDWidth       ),
        .AxiIdWidthMstPort( MstAxiIDWidth       ),
        .slv_aw_chan_t    ( slv_aw_chan_t       ),
        .slv_w_chan_t     ( w_chan_t            ),
        .slv_b_chan_t     ( slv_b_chan_t        ),
        .slv_ar_chan_t    ( slv_ar_chan_t       ),
        .slv_r_chan_t     ( slv_r_chan_t        ),
        .mst_aw_chan_t    ( mst_aw_chan_t       ),
        .mst_w_chan_t     ( w_chan_t            ),
        .mst_b_chan_t     ( mst_b_chan_t        ),
        .mst_ar_chan_t    ( mst_ar_chan_t       ),
        .mst_r_chan_t     ( mst_r_chan_t        )
      ) i_id_prepend (
        .pre_id_i         ( switch_id_t'(i)         ),
        .slv_aw_chans_i   ( slv_reqs_i[i].aw        ),
        .slv_aw_valids_i  ( slv_reqs_i[i].aw_valid  ),
        .slv_aw_readies_o ( slv_resps_o[i].aw_ready ),
        .slv_w_chans_i    ( slv_reqs_i[i].w         ),
        .slv_w_valids_i   ( slv_reqs_i[i].w_valid   ),
        .slv_w_readies_o  ( slv_resps_o[i].w_ready  ),
        .slv_b_chans_o    ( slv_resps_o[i].b        ),
        .slv_b_valids_o   ( slv_resps_o[i].b_valid  ),
        .slv_b_readies_i  ( slv_reqs_i[i].b_ready   ),
        .slv_ar_chans_i   ( slv_reqs_i[i].ar        ),
        .slv_ar_valids_i  ( slv_reqs_i[i].ar_valid  ),
        .slv_ar_readies_o ( slv_resps_o[i].ar_ready ),
        .slv_r_chans_o    ( slv_resps_o[i].r        ),
        .slv_r_valids_o   ( slv_resps_o[i].r_valid  ),
        .slv_r_readies_i  ( slv_reqs_i[i].r_ready   ),
        .mst_aw_chans_o   ( slv_aw_chans[i]         ),
        .mst_aw_valids_o  ( slv_aw_valids[i]        ),
        .mst_aw_readies_i ( slv_aw_readies[i]       ),
        .mst_w_chans_o    ( slv_w_chans[i]          ),
        .mst_w_valids_o   ( slv_w_valids[i]         ),
        .mst_w_readies_i  ( slv_w_readies[i]        ),
        .mst_b_chans_i    ( slv_b_chans[i]          ),
        .mst_b_valids_i   ( slv_b_valids[i]         ),
        .mst_b_readies_o  ( slv_b_readies[i]        ),
        .mst_ar_chans_o   ( slv_ar_chans[i]         ),
        .mst_ar_valids_o  ( slv_ar_valids[i]        ),
        .mst_ar_readies_i ( slv_ar_readies[i]       ),
        .mst_r_chans_i    ( slv_r_chans[i]          ),
        .mst_r_valids_i   ( slv_r_valids[i]         ),
        .mst_r_readies_o  ( slv_r_readies[i]        )
      );
    end

    //--------------------------------------
    // AW Channel
    //--------------------------------------
    rr_arb_tree #(
      .NumIn    ( NoSlvPorts    ),
      .DataType ( mst_aw_chan_t ),
      .AxiVldRdy( 1'b1          ),
      .LockIn   ( 1'b1          )
    ) i_aw_arbiter (
      .clk_i  ( clk_i           ),
      .rst_ni ( rst_ni          ),
      .flush_i( 1'b0            ),
      .rr_i   ( '0              ),
      .req_i  ( slv_aw_valids   ),
      .gnt_o  ( slv_aw_readies  ),
      .data_i ( slv_aw_chans    ),
      .gnt_i  ( aw_ready        ),
      .req_o  ( aw_valid        ),
      .data_o ( mst_aw_chan     ),
      .idx_o  (                 )
    );

    // control of the AW channel
    always_comb begin
      // default assignments
      lock_aw_valid_d = lock_aw_valid_q;
      load_aw_lock    = 1'b0;
      w_fifo_push     = 1'b0;
      mst_aw_valid    = 1'b0;
      aw_ready        = 1'b0;
      // had a downstream stall, be valid and send the AW along
      if (lock_aw_valid_q) begin
        mst_aw_valid = 1'b1;
        // transaction
        if (mst_aw_ready) begin
          aw_ready        = 1'b1;
          lock_aw_valid_d = 1'b0;
          load_aw_lock    = 1'b1;
        end
      end else begin
        if (!w_fifo_full && aw_valid) begin
          mst_aw_valid = 1'b1;
          w_fifo_push = 1'b1;
          if (mst_aw_ready) begin
            aw_ready = 1'b1;
          end else begin
            // go to lock if transaction not in this cycle
            lock_aw_valid_d = 1'b1;
            load_aw_lock    = 1'b1;
          end
        end
      end
    end

    `FFLARN(lock_aw_valid_q, lock_aw_valid_d, load_aw_lock, '0, clk_i, rst_ni)

    fifo_v3 #(
      .FALL_THROUGH ( FallThrough ),
      .DEPTH        ( MaxWTrans   ),
      .dtype        ( switch_id_t )
    ) i_w_fifo (
      .clk_i     ( clk_i                                     ),
      .rst_ni    ( rst_ni                                    ),
      .flush_i   ( 1'b0                                      ),
      .testmode_i( test_i                                    ),
      .full_o    ( w_fifo_full                               ),
      .empty_o   ( w_fifo_empty                              ),
      .usage_o   (                                           ),
      .data_i    ( mst_aw_chan.id[SlvAxiIDWidth+:MstIdxBits] ),
      .push_i    ( w_fifo_push                               ),
      .data_o    ( w_fifo_data                               ),
      .pop_i     ( w_fifo_pop                                )
    );

    spill_register #(
      .T       ( mst_aw_chan_t ),
      .Bypass  ( ~SpillAw      ) // Param indicated that we want a spill reg
    ) i_aw_spill_reg (
      .clk_i   ( clk_i               ),
      .rst_ni  ( rst_ni              ),
      .valid_i ( mst_aw_valid        ),
      .ready_o ( mst_aw_ready        ),
      .data_i  ( mst_aw_chan         ),
      .valid_o ( mst_req_o.aw_valid  ),
      .ready_i ( mst_resp_i.aw_ready ),
      .data_o  ( mst_req_o.aw        )
    );

    //--------------------------------------
    // W Channel
    //--------------------------------------
    // multiplexer
    assign mst_w_chan = slv_w_chans[w_fifo_data];
    always_comb begin
      // default assignments
      mst_w_valid   = 1'b0;
      slv_w_readies = '0;
      w_fifo_pop    = 1'b0;
      // control
      if (!w_fifo_empty) begin
        // connect the handshake
        mst_w_valid                = slv_w_valids[w_fifo_data];
        slv_w_readies[w_fifo_data] = mst_w_ready;
        // pop FIFO on a last transaction
        w_fifo_pop = slv_w_valids[w_fifo_data] & mst_w_ready & mst_w_chan.last;
      end
    end

    spill_register #(
      .T       ( w_chan_t ),
      .Bypass  ( ~SpillW  )
    ) i_w_spill_reg (
      .clk_i   ( clk_i              ),
      .rst_ni  ( rst_ni             ),
      .valid_i ( mst_w_valid        ),
      .ready_o ( mst_w_ready        ),
      .data_i  ( mst_w_chan         ),
      .valid_o ( mst_req_o.w_valid  ),
      .ready_i ( mst_resp_i.w_ready ),
      .data_o  ( mst_req_o.w        )
    );

    //--------------------------------------
    // B Channel
    //--------------------------------------
    // replicate B channels
    assign slv_b_chans  = {NoSlvPorts{mst_b_chan}};
    // control B channel handshake
    assign switch_b_id  = mst_b_chan.id[SlvAxiIDWidth+:MstIdxBits];
    assign slv_b_valids = (mst_b_valid) ? (1 << switch_b_id) : '0;

    spill_register #(
      .T       ( mst_b_chan_t ),
      .Bypass  ( ~SpillB      )
    ) i_b_spill_reg (
      .clk_i   ( clk_i                      ),
      .rst_ni  ( rst_ni                     ),
      .valid_i ( mst_resp_i.b_valid         ),
      .ready_o ( mst_req_o.b_ready          ),
      .data_i  ( mst_resp_i.b               ),
      .valid_o ( mst_b_valid                ),
      .ready_i ( slv_b_readies[switch_b_id] ),
      .data_o  ( mst_b_chan                 )
    );

    //--------------------------------------
    // AR Channel
    //--------------------------------------
    rr_arb_tree #(
      .NumIn    ( NoSlvPorts    ),
      .DataType ( mst_ar_chan_t ),
      .AxiVldRdy( 1'b1          ),
      .LockIn   ( 1'b1          )
    ) i_ar_arbiter (
      .clk_i  ( clk_i           ),
      .rst_ni ( rst_ni          ),
      .flush_i( 1'b0            ),
      .rr_i   ( '0              ),
      .req_i  ( slv_ar_valids   ),
      .gnt_o  ( slv_ar_readies  ),
      .data_i ( slv_ar_chans    ),
      .gnt_i  ( ar_ready        ),
      .req_o  ( ar_valid        ),
      .data_o ( mst_ar_chan     ),
      .idx_o  (                 )
    );

    spill_register #(
      .T       ( mst_ar_chan_t ),
      .Bypass  ( ~SpillAr      )
    ) i_ar_spill_reg (
      .clk_i   ( clk_i               ),
      .rst_ni  ( rst_ni              ),
      .valid_i ( ar_valid            ),
      .ready_o ( ar_ready            ),
      .data_i  ( mst_ar_chan         ),
      .valid_o ( mst_req_o.ar_valid  ),
      .ready_i ( mst_resp_i.ar_ready ),
      .data_o  ( mst_req_o.ar        )
    );

    //--------------------------------------
    // R Channel
    //--------------------------------------
    // replicate R channels
    assign slv_r_chans  = {NoSlvPorts{mst_r_chan}};
    // R channel handshake control
    assign switch_r_id  = mst_r_chan.id[SlvAxiIDWidth+:MstIdxBits];
    assign slv_r_valids = (mst_r_valid) ? (1 << switch_r_id) : '0;

    spill_register #(
      .T       ( mst_r_chan_t ),
      .Bypass  ( ~SpillR      )
    ) i_r_spill_reg (
      .clk_i   ( clk_i                      ),
      .rst_ni  ( rst_ni                     ),
      .valid_i ( mst_resp_i.r_valid         ),
      .ready_o ( mst_req_o.r_ready          ),
      .data_i  ( mst_resp_i.r               ),
      .valid_o ( mst_r_valid                ),
      .ready_i ( slv_r_readies[switch_r_id] ),
      .data_o  ( mst_r_chan                 )
    );
  end

// pragma translate_off
`ifndef VERILATOR
  initial begin
    assert (SlvAxiIDWidth > 0) else $fatal(1, "AXI ID width of slave ports must be non-zero!");
    assert (NoSlvPorts > 0) else $fatal(1, "Number of slave ports must be non-zero!");
    assert (MaxWTrans > 0)
      else $fatal(1, "Maximum number of outstanding writes must be non-zero!");
    assert (MstAxiIDWidth >= SlvAxiIDWidth + $clog2(NoSlvPorts))
      else $fatal(1, "AXI ID width of master ports must be wide enough to identify slave ports!");
    // Assert ID widths (one slave is sufficient since they all have the same type).
    assert ($unsigned($bits(slv_reqs_i[0].aw.id)) == SlvAxiIDWidth)
      else $fatal(1, "ID width of AW channel of slave ports does not match parameter!");
    assert ($unsigned($bits(slv_reqs_i[0].ar.id)) == SlvAxiIDWidth)
      else $fatal(1, "ID width of AR channel of slave ports does not match parameter!");
    assert ($unsigned($bits(slv_resps_o[0].b.id)) == SlvAxiIDWidth)
      else $fatal(1, "ID width of B channel of slave ports does not match parameter!");
    assert ($unsigned($bits(slv_resps_o[0].r.id)) == SlvAxiIDWidth)
      else $fatal(1, "ID width of R channel of slave ports does not match parameter!");
    assert ($unsigned($bits(mst_req_o.aw.id)) == MstAxiIDWidth)
      else $fatal(1, "ID width of AW channel of master port is wrong!");
    assert ($unsigned($bits(mst_req_o.ar.id)) == MstAxiIDWidth)
      else $fatal(1, "ID width of AR channel of master port is wrong!");
    assert ($unsigned($bits(mst_resp_i.b.id)) == MstAxiIDWidth)
      else $fatal(1, "ID width of B channel of master port is wrong!");
    assert ($unsigned($bits(mst_resp_i.r.id)) == MstAxiIDWidth)
      else $fatal(1, "ID width of R channel of master port is wrong!");
  end
`endif
// pragma translate_on
endmodule

// interface wrap
`include "axi/assign.svh"
`include "axi/typedef.svh"
module axi_mux_intf #(
  parameter int unsigned SLV_AXI_ID_WIDTH = 32'd0, // Synopsys DC requires default value for params
  parameter int unsigned MST_AXI_ID_WIDTH = 32'd0,
  parameter int unsigned AXI_ADDR_WIDTH   = 32'd0,
  parameter int unsigned AXI_DATA_WIDTH   = 32'd0,
  parameter int unsigned AXI_USER_WIDTH   = 32'd0,
  parameter int unsigned NO_SLV_PORTS     = 32'd0, // Number of slave ports
  // Maximum number of outstanding transactions per write
  parameter int unsigned MAX_W_TRANS      = 32'd8,
  // if enabled, this multiplexer is purely combinatorial
  parameter bit          FALL_THROUGH     = 1'b0,
  // add spill register on write master ports, adds a cycle latency on write channels
  parameter bit          SPILL_AW         = 1'b1,
  parameter bit          SPILL_W          = 1'b0,
  parameter bit          SPILL_B          = 1'b0,
  // add spill register on read master ports, adds a cycle latency on read channels
  parameter bit          SPILL_AR         = 1'b1,
  parameter bit          SPILL_R          = 1'b0
) (
  input  logic   clk_i,                  // Clock
  input  logic   rst_ni,                 // Asynchronous reset active low
  input  logic   test_i,                 // Testmode enable
  AXI_BUS.Slave  slv [NO_SLV_PORTS-1:0], // slave ports
  AXI_BUS.Master mst                     // master port
);

  typedef logic [SLV_AXI_ID_WIDTH-1:0] slv_id_t;
  typedef logic [MST_AXI_ID_WIDTH-1:0] mst_id_t;
  typedef logic [AXI_ADDR_WIDTH -1:0]  addr_t;
  typedef logic [AXI_DATA_WIDTH-1:0]   data_t;
  typedef logic [AXI_DATA_WIDTH/8-1:0] strb_t;
  typedef logic [AXI_USER_WIDTH-1:0]   user_t;
  // channels typedef
  `AXI_TYPEDEF_AW_CHAN_T(slv_aw_chan_t, addr_t, slv_id_t, user_t)
  `AXI_TYPEDEF_AW_CHAN_T(mst_aw_chan_t, addr_t, mst_id_t, user_t)

  `AXI_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t, user_t)

  `AXI_TYPEDEF_B_CHAN_T(slv_b_chan_t, slv_id_t, user_t)
  `AXI_TYPEDEF_B_CHAN_T(mst_b_chan_t, mst_id_t, user_t)

  `AXI_TYPEDEF_AR_CHAN_T(slv_ar_chan_t, addr_t, slv_id_t, user_t)
  `AXI_TYPEDEF_AR_CHAN_T(mst_ar_chan_t, addr_t, mst_id_t, user_t)

  `AXI_TYPEDEF_R_CHAN_T(slv_r_chan_t, data_t, slv_id_t, user_t)
  `AXI_TYPEDEF_R_CHAN_T(mst_r_chan_t, data_t, mst_id_t, user_t)

  `AXI_TYPEDEF_REQ_T(slv_req_t, slv_aw_chan_t, w_chan_t, slv_ar_chan_t)
  `AXI_TYPEDEF_RESP_T(slv_resp_t, slv_b_chan_t, slv_r_chan_t)

  `AXI_TYPEDEF_REQ_T(mst_req_t, mst_aw_chan_t, w_chan_t, mst_ar_chan_t)
  `AXI_TYPEDEF_RESP_T(mst_resp_t, mst_b_chan_t, mst_r_chan_t)

  slv_req_t  [NO_SLV_PORTS-1:0] slv_reqs;
  slv_resp_t [NO_SLV_PORTS-1:0] slv_resps;
  mst_req_t                     mst_req;
  mst_resp_t                    mst_resp;

  for (genvar i = 0; i < NO_SLV_PORTS; i++) begin : gen_assign_slv_ports
    `AXI_ASSIGN_TO_REQ(slv_reqs[i], slv[i])
    `AXI_ASSIGN_FROM_RESP(slv[i], slv_resps[i])
  end

  `AXI_ASSIGN_FROM_REQ(mst, mst_req)
  `AXI_ASSIGN_TO_RESP(mst_resp, mst)

  axi_mux #(
    .SlvAxiIDWidth ( SLV_AXI_ID_WIDTH ),
    .slv_aw_chan_t ( slv_aw_chan_t    ), // AW Channel Type, slave ports
    .mst_aw_chan_t ( mst_aw_chan_t    ), // AW Channel Type, master port
    .w_chan_t      ( w_chan_t         ), //  W Channel Type, all ports
    .slv_b_chan_t  ( slv_b_chan_t     ), //  B Channel Type, slave ports
    .mst_b_chan_t  ( mst_b_chan_t     ), //  B Channel Type, master port
    .slv_ar_chan_t ( slv_ar_chan_t    ), // AR Channel Type, slave ports
    .mst_ar_chan_t ( mst_ar_chan_t    ), // AR Channel Type, master port
    .slv_r_chan_t  ( slv_r_chan_t     ), //  R Channel Type, slave ports
    .mst_r_chan_t  ( mst_r_chan_t     ), //  R Channel Type, master port
    .slv_req_t     ( slv_req_t        ),
    .slv_resp_t    ( slv_resp_t       ),
    .mst_req_t     ( mst_req_t        ),
    .mst_resp_t    ( mst_resp_t       ),
    .NoSlvPorts    ( NO_SLV_PORTS     ), // Number of slave ports
    .MaxWTrans     ( MAX_W_TRANS      ),
    .FallThrough   ( FALL_THROUGH     ),
    .SpillAw       ( SPILL_AW         ),
    .SpillW        ( SPILL_W          ),
    .SpillB        ( SPILL_B          ),
    .SpillAr       ( SPILL_AR         ),
    .SpillR        ( SPILL_R          )
  ) i_axi_mux (
    .clk_i       ( clk_i     ), // Clock
    .rst_ni      ( rst_ni    ), // Asynchronous reset active low
    .test_i      ( test_i    ), // Test Mode enable
    .slv_reqs_i  ( slv_reqs  ),
    .slv_resps_o ( slv_resps ),
    .mst_req_o   ( mst_req   ),
    .mst_resp_i  ( mst_resp  )
  );
endmodule
