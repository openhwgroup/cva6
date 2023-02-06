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

// AXI4-Lite Multiplexer: This module multiplexes the AXI4-Lite slave ports down to one master port.
//                        The multiplexing happens in a round robin fashion, responses get
//                        sent back in order.

// register macros
`include "common_cells/registers.svh"

module axi_lite_mux #(
  // AXI4-Lite parameter and channel types
  parameter type          aw_chan_t  = logic, // AW LITE Channel Type
  parameter type           w_chan_t  = logic, //  W LITE Channel Type
  parameter type           b_chan_t  = logic, //  B LITE Channel Type
  parameter type          ar_chan_t  = logic, // AR LITE Channel Type
  parameter type           r_chan_t  = logic, //  R LITE Channel Type
  parameter type              req_t  = logic, // AXI4-Lite request type
  parameter type             resp_t  = logic, // AXI4-Lite response type
  parameter int unsigned NoSlvPorts  = 32'd0, // Number of slave ports
  // Maximum number of outstanding transactions per write or read
  parameter int unsigned MaxTrans    = 32'd0,
  // If enabled, this multiplexer is purely combinatorial
  parameter bit          FallThrough = 1'b0,
  // add spill register on write master port, adds a cycle latency on write channels
  parameter bit          SpillAw     = 1'b1,
  parameter bit          SpillW      = 1'b0,
  parameter bit          SpillB      = 1'b0,
  // add spill register on read master port, adds a cycle latency on read channels
  parameter bit          SpillAr     = 1'b1,
  parameter bit          SpillR      = 1'b0
) (
  input  logic                   clk_i,    // Clock
  input  logic                   rst_ni,   // Asynchronous reset active low
  input  logic                   test_i,   // Test Mode enable
  // slave ports (AXI4-Lite inputs), connect master modules here
  input  req_t  [NoSlvPorts-1:0] slv_reqs_i,
  output resp_t [NoSlvPorts-1:0] slv_resps_o,
  // master port (AXI4-Lite output), connect slave module here
  output req_t                   mst_req_o,
  input  resp_t                  mst_resp_i
);
  // pass through if only one slave port
  if (NoSlvPorts == 32'h1) begin : gen_no_mux
    assign mst_req_o = slv_reqs_i[0];
    assign slv_resps_o[0] = mst_resp_i;
  // other non degenerate cases
  end else begin : gen_mux
    // typedef for the FIFO types
    typedef logic [$clog2(NoSlvPorts)-1:0] select_t;

    // input to the AW arbitration tree, unpacked from request struct
    aw_chan_t [NoSlvPorts-1:0] slv_aw_chans;
    logic     [NoSlvPorts-1:0] slv_aw_valids, slv_aw_readies;

    // AW channel arb tree decision
    select_t  aw_select;
    aw_chan_t mst_aw_chan;
    logic     mst_aw_valid, mst_aw_ready;

    // AW master handshake internal, so that we are able to stall, if w_fifo is full
    logic     aw_valid,     aw_ready;

    // FF to lock the AW valid signal, when a new arbitration decision is made the decision
    // gets pushed into the W FIFO, when it now stalls prevent subsequent pushing
    // This FF removes AW to W dependency
    logic     lock_aw_valid_d, lock_aw_valid_q;
    logic     load_aw_lock;

    // signals for the FIFO that holds the last switching decision of the AW channel
    logic     w_fifo_full,  w_fifo_empty;
    logic     w_fifo_push,  w_fifo_pop;

    // W channel spill reg
    select_t  w_select;
    w_chan_t  mst_w_chan;
    logic     mst_w_valid,  mst_w_ready;

    // switching decision for the B response back routing
    select_t  b_select;
    // signals for the FIFO that holds the last switching decision of the AW channel
    logic     b_fifo_full,  b_fifo_empty;
    logic     /*w_fifo_pop*/b_fifo_pop;

    // B channel spill reg
    b_chan_t  mst_b_chan;
    logic     mst_b_valid,  mst_b_ready;

    // input to the AR arbitration tree, unpacked from request struct
    ar_chan_t [NoSlvPorts-1:0] slv_ar_chans;
    logic     [NoSlvPorts-1:0] slv_ar_valids, slv_ar_readies;

    // AR channel for when spill is enabled
    select_t  ar_select;
    ar_chan_t mst_ar_chan;
    logic     mst_ar_valid, mst_ar_ready;

    // AR master handshake internal, so that we are able to stall, if R_fifo is full
    logic     ar_valid,     ar_ready;

    // master ID in the r_id
    select_t  r_select;

    // signals for the FIFO that holds the last switching decision of the AR channel
    logic     r_fifo_full,  r_fifo_empty;
    logic     r_fifo_push,  r_fifo_pop;

    // R channel spill reg
    r_chan_t  mst_r_chan;
    logic     mst_r_valid,  mst_r_ready;

    //--------------------------------------
    // AW Channel
    //--------------------------------------
    // unpach AW channel from request/response array
    for (genvar i = 0; i < NoSlvPorts; i++) begin : gen_aw_arb_input
      assign slv_aw_chans[i]         = slv_reqs_i[i].aw;
      assign slv_aw_valids[i]        = slv_reqs_i[i].aw_valid;
      assign slv_resps_o[i].aw_ready = slv_aw_readies[i];
    end
    rr_arb_tree #(
      .NumIn    ( NoSlvPorts ),
      .DataType ( aw_chan_t  ),
      .AxiVldRdy( 1'b1       ),
      .LockIn   ( 1'b1       )
    ) i_aw_arbiter (
      .clk_i  ( clk_i          ),
      .rst_ni ( rst_ni         ),
      .flush_i( 1'b0           ),
      .rr_i   ( '0             ),
      .req_i  ( slv_aw_valids  ),
      .gnt_o  ( slv_aw_readies ),
      .data_i ( slv_aw_chans   ),
      .gnt_i  ( aw_ready       ),
      .req_o  ( aw_valid       ),
      .data_o ( mst_aw_chan    ),
      .idx_o  ( aw_select      )
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
      .DEPTH        ( MaxTrans    ),
      .dtype        ( select_t    )
    ) i_w_fifo (
      .clk_i     ( clk_i        ),
      .rst_ni    ( rst_ni       ),
      .flush_i   ( 1'b0         ),
      .testmode_i( test_i       ),
      .full_o    ( w_fifo_full  ),
      .empty_o   ( w_fifo_empty ),
      .usage_o   (              ),
      .data_i    ( aw_select    ),
      .push_i    ( w_fifo_push  ),
      .data_o    ( w_select     ),
      .pop_i     ( w_fifo_pop   )
    );

    spill_register #(
      .T       ( aw_chan_t  ),
      .Bypass  ( ~SpillAw   ) // Param indicated that we want a spill reg
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
    assign mst_w_chan      = (!w_fifo_empty && !b_fifo_full) ? slv_reqs_i[w_select].w        :   '0;
    assign mst_w_valid     = (!w_fifo_empty && !b_fifo_full) ? slv_reqs_i[w_select].w_valid  : 1'b0;
    for (genvar i = 0; i < NoSlvPorts; i++) begin : gen_slv_w_ready
      assign slv_resps_o[i].w_ready =  mst_w_ready & ~w_fifo_empty &
                                      ~b_fifo_full & (w_select == select_t'(i));
    end
    assign w_fifo_pop      = mst_w_valid & mst_w_ready;

    fifo_v3 #(
      .FALL_THROUGH ( FallThrough ),
      .DEPTH        ( MaxTrans    ),
      .dtype        ( select_t    )
    ) i_b_fifo (
      .clk_i     ( clk_i        ),
      .rst_ni    ( rst_ni       ),
      .flush_i   ( 1'b0         ),
      .testmode_i( test_i       ),
      .full_o    ( b_fifo_full  ),
      .empty_o   ( b_fifo_empty ),
      .usage_o   (              ),
      .data_i    ( w_select     ),
      .push_i    ( w_fifo_pop   ), // push the selection for the B channel on W transaction
      .data_o    ( b_select     ),
      .pop_i     ( b_fifo_pop   )
    );

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
    for (genvar i = 0; i < NoSlvPorts; i++) begin : gen_slv_resps_b
      assign slv_resps_o[i].b       = mst_b_chan;
      assign slv_resps_o[i].b_valid = mst_b_valid & ~b_fifo_empty & (b_select == select_t'(i));
    end
    assign mst_b_ready    = ~b_fifo_empty & slv_reqs_i[b_select].b_ready;
    assign b_fifo_pop     = mst_b_valid & mst_b_ready;

    spill_register #(
      .T       ( b_chan_t ),
      .Bypass  ( ~SpillB  )
    ) i_b_spill_reg (
      .clk_i   ( clk_i              ),
      .rst_ni  ( rst_ni             ),
      .valid_i ( mst_resp_i.b_valid ),
      .ready_o ( mst_req_o.b_ready  ),
      .data_i  ( mst_resp_i.b       ),
      .valid_o ( mst_b_valid        ),
      .ready_i ( mst_b_ready        ),
      .data_o  ( mst_b_chan         )
    );

    //--------------------------------------
    // AR Channel
    //--------------------------------------
    // unpack AR channel from request/response struct
    for (genvar i = 0; i < NoSlvPorts; i++) begin : gen_ar_arb_input
      assign slv_ar_chans[i]         = slv_reqs_i[i].ar;
      assign slv_ar_valids[i]        = slv_reqs_i[i].ar_valid;
      assign slv_resps_o[i].ar_ready = slv_ar_readies[i];
    end
    rr_arb_tree #(
      .NumIn    ( NoSlvPorts ),
      .DataType ( ar_chan_t  ),
      .AxiVldRdy( 1'b1       ),
      .LockIn   ( 1'b1       )
    ) i_ar_arbiter (
      .clk_i  ( clk_i          ),
      .rst_ni ( rst_ni         ),
      .flush_i( 1'b0           ),
      .rr_i   ( '0             ),
      .req_i  ( slv_ar_valids  ),
      .gnt_o  ( slv_ar_readies ),
      .data_i ( slv_ar_chans   ),
      .gnt_i  ( ar_ready       ),
      .req_o  ( ar_valid       ),
      .data_o ( mst_ar_chan    ),
      .idx_o  ( ar_select      )
    );

    // connect the handshake if there is space in the FIFO, no need for valid locking
    // as the R response is only allowed, when AR is transferred
    assign mst_ar_valid = (!r_fifo_full) ? ar_valid     : 1'b0;
    assign ar_ready     = (!r_fifo_full) ? mst_ar_ready : 1'b0;
    assign r_fifo_push  = mst_ar_valid & mst_ar_ready;

    fifo_v3 #(
      .FALL_THROUGH ( FallThrough ),
      .DEPTH        ( MaxTrans    ),
      .dtype        ( select_t    )
    ) i_r_fifo (
      .clk_i     ( clk_i        ),
      .rst_ni    ( rst_ni       ),
      .flush_i   ( 1'b0         ),
      .testmode_i( test_i       ),
      .full_o    ( r_fifo_full  ),
      .empty_o   ( r_fifo_empty ),
      .usage_o   (              ),
      .data_i    ( ar_select    ),
      .push_i    ( r_fifo_push  ), // push the selection when w transaction happens
      .data_o    ( r_select     ),
      .pop_i     ( r_fifo_pop   )
    );

    spill_register #(
      .T       ( ar_chan_t ),
      .Bypass  ( ~SpillAr  )
    ) i_ar_spill_reg (
      .clk_i   ( clk_i               ),
      .rst_ni  ( rst_ni              ),
      .valid_i ( mst_ar_valid        ),
      .ready_o ( mst_ar_ready        ),
      .data_i  ( mst_ar_chan         ),
      .valid_o ( mst_req_o.ar_valid  ),
      .ready_i ( mst_resp_i.ar_ready ),
      .data_o  ( mst_req_o.ar        )
    );

    //--------------------------------------
    // R Channel
    //--------------------------------------
    // replicate R channels
    for (genvar i = 0; i < NoSlvPorts; i++) begin : gen_slv_resps_r
      assign slv_resps_o[i].r       = mst_r_chan;
      assign slv_resps_o[i].r_valid = mst_r_valid & ~r_fifo_empty & (r_select == select_t'(i));
    end
    assign mst_r_ready    = ~r_fifo_empty & slv_reqs_i[r_select].r_ready;
    assign r_fifo_pop     = mst_r_valid & mst_r_ready;

    spill_register #(
      .T       ( r_chan_t ),
      .Bypass  ( ~SpillR  )
    ) i_r_spill_reg (
      .clk_i   ( clk_i              ),
      .rst_ni  ( rst_ni             ),
      .valid_i ( mst_resp_i.r_valid ),
      .ready_o ( mst_req_o.r_ready  ),
      .data_i  ( mst_resp_i.r       ),
      .valid_o ( mst_r_valid        ),
      .ready_i ( mst_r_ready        ),
      .data_o  ( mst_r_chan         )
    );
  end

  // pragma translate_off
  `ifndef VERILATOR
    initial begin: p_assertions
      NoPorts:  assert (NoSlvPorts > 0) else $fatal("Number of slave ports must be at least 1!");
      MaxTnx:   assert (MaxTrans   > 0) else $fatal("Number of transactions must be at least 1!");
    end
  `endif
  // pragma translate_on
endmodule

// interface wrap
`include "axi/assign.svh"
`include "axi/typedef.svh"

module axi_lite_mux_intf #(
  parameter int unsigned AxiAddrWidth  = 32'd0,
  parameter int unsigned AxiDataWidth  = 32'd0,
  parameter int unsigned NoSlvPorts    = 32'd0, // Number of slave ports
  // Maximum number of outstanding transactions per write
  parameter int unsigned MaxTrans      = 32'd0,
  // if enabled, this multiplexer is purely combinatorial
  parameter bit          FallThrough   = 1'b0,
  // add spill register on write master ports, adds a cycle latency on write channels
  parameter bit          SpillAw       = 1'b1,
  parameter bit          SpillW        = 1'b0,
  parameter bit          SpillB        = 1'b0,
  // add spill register on read master ports, adds a cycle latency on read channels
  parameter bit          SpillAr       = 1'b1,
  parameter bit          SpillR        = 1'b0
) (
  input  logic   clk_i,                // Clock
  input  logic   rst_ni,               // Asynchronous reset active low
  input  logic   test_i,               // Testmode enable
  AXI_BUS.Slave  slv [NoSlvPorts-1:0], // slave ports
  AXI_BUS.Master mst                   // master port
);

  typedef logic [AxiAddrWidth-1:0]   addr_t;
  typedef logic [AxiDataWidth-1:0]   data_t;
  typedef logic [AxiDataWidth/8-1:0] strb_t;
  // channels typedef
  `AXI_LITE_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t)
  `AXI_LITE_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t)
  `AXI_LITE_TYPEDEF_B_CHAN_T(b_chan_t)
  `AXI_LITE_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t)
  `AXI_LITE_TYPEDEF_R_CHAN_T(r_chan_t, data_t)
  `AXI_LITE_TYPEDEF_REQ_T(req_t, aw_chan_t, w_chan_t, ar_chan_t)
  `AXI_LITE_TYPEDEF_RESP_T(resp_t, b_chan_t, r_chan_t)

  req_t     [NoSlvPorts-1:0] slv_reqs;
  resp_t    [NoSlvPorts-1:0] slv_resps;
  req_t                      mst_req;
  resp_t                     mst_resp;

  for (genvar i = 0; i < NoSlvPorts; i++) begin : gen_assign_slv_ports
    `AXI_LITE_ASSIGN_TO_REQ(slv_reqs[i], slv[i])
    `AXI_LITE_ASSIGN_FROM_RESP(slv[i], slv_resps[i])
  end

  `AXI_LITE_ASSIGN_FROM_REQ(mst, mst_req)
  `AXI_LITE_ASSIGN_TO_RESP(mst_resp, mst)

  axi_lite_mux #(
    .aw_chan_t     ( aw_chan_t     ), // AW Channel Type
    .w_chan_t      (  w_chan_t     ), //  W Channel Type
    .b_chan_t      (  b_chan_t     ), //  B Channel Type
    .ar_chan_t     ( ar_chan_t     ), // AR Channel Type
    .r_chan_t      (  r_chan_t     ), //  R Channel Type
    .NoSlvPorts    ( NoSlvPorts    ), // Number of slave ports
    .MaxTrans      ( MaxTrans      ),
    .FallThrough   ( FallThrough   ),
    .SpillAw       ( SpillAw       ),
    .SpillW        ( SpillW        ),
    .SpillB        ( SpillB        ),
    .SpillAr       ( SpillAr       ),
    .SpillR        ( SpillR        )
  ) i_axi_mux (
    .clk_i,  // Clock
    .rst_ni, // Asynchronous reset active low
    .test_i, // Test Mode enable
    .slv_reqs_i  ( slv_reqs  ),
    .slv_resps_o ( slv_resps ),
    .mst_req_o   ( mst_req   ),
    .mst_resp_i  ( mst_resp  )
  );

  // pragma translate_off
  `ifndef VERILATOR
    initial begin: p_assertions
      AddrWidth: assert (AxiAddrWidth > 0) else $fatal("Axi Parameter has to be > 0!");
      DataWidth: assert (AxiDataWidth > 0) else $fatal("Axi Parameter has to be > 0!");
    end
  `endif
  // pragma translate_on
endmodule
