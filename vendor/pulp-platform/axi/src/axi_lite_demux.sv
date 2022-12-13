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

// axi_lite_demux: Demultiplex an AXI4-Lite bus from one slave port to multiple master ports.
//                 The selection signal at the AW and AR channel has to follow the same
//                 stability rules as the corresponding AXI4-Lite channel.

module axi_lite_demux #(
  parameter type         aw_chan_t      = logic, // AXI4-Lite AW channel
  parameter type         w_chan_t       = logic, // AXI4-Lite  W channel
  parameter type         b_chan_t       = logic, // AXI4-Lite  B channel
  parameter type         ar_chan_t      = logic, // AXI4-Lite AR channel
  parameter type         r_chan_t       = logic, // AXI4-Lite  R channel
  parameter type         req_t          = logic, // AXI4-Lite request struct
  parameter type         resp_t         = logic, // AXI4-Lite response struct
  parameter int unsigned NoMstPorts     = 32'd0, // Number of instantiated ports
  parameter int unsigned MaxTrans       = 32'd0, // Maximum number of open transactions per channel
  parameter bit          FallThrough    = 1'b0,  // FIFOs are in fall through mode
  parameter bit          SpillAw        = 1'b1,  // insert one cycle latency on slave AW
  parameter bit          SpillW         = 1'b0,  // insert one cycle latency on slave  W
  parameter bit          SpillB         = 1'b0,  // insert one cycle latency on slave  B
  parameter bit          SpillAr        = 1'b1,  // insert one cycle latency on slave AR
  parameter bit          SpillR         = 1'b0,  // insert one cycle latency on slave  R
  // Dependent parameters, DO NOT OVERRIDE!
  parameter type         select_t       = logic [$clog2(NoMstPorts)-1:0]
) (
  input  logic                   clk_i,
  input  logic                   rst_ni,
  input  logic                   test_i,
  // slave port (AXI4-Lite input), connect master module here
  input  req_t                   slv_req_i,
  input  select_t                slv_aw_select_i,
  input  select_t                slv_ar_select_i,
  output resp_t                  slv_resp_o,
  // master ports (AXI4-Lite outputs), connect slave modules here
  output req_t  [NoMstPorts-1:0] mst_reqs_o,
  input  resp_t [NoMstPorts-1:0] mst_resps_i
);

  //--------------------------------------
  // Typedefs for the spill registers
  //--------------------------------------
  typedef struct packed {
    aw_chan_t aw;
    select_t  select;
  } aw_chan_select_t;
  typedef struct packed {
    ar_chan_t ar;
    select_t  select;
  } ar_chan_select_t;

  if (NoMstPorts == 32'd1) begin : gen_no_demux
    // degenerate case, connect slave to master port
    // AW channel
    assign mst_reqs_o[0] = slv_req_i;
    assign slv_resp_o    = mst_resps_i[0];
  end else begin : gen_demux
    // normal non degenerate case


    //--------------------------------------
    //--------------------------------------
    // Signal Declarations
    //--------------------------------------
    //--------------------------------------

    //--------------------------------------
    // Write Transaction
    //--------------------------------------
    aw_chan_select_t       slv_aw_chan;
    logic                  slv_aw_valid,    slv_aw_ready;

    logic [NoMstPorts-1:0] mst_aw_valids, mst_aw_readies;

    logic                  lock_aw_valid_d, lock_aw_valid_q, load_aw_lock;

    logic                  w_fifo_push,     w_fifo_pop;
    logic                  w_fifo_full,     w_fifo_empty;

    w_chan_t               slv_w_chan;
    select_t               w_select;
    logic                  slv_w_valid,     slv_w_ready;

    logic                  /*w_pop*/        b_fifo_pop;
    logic                  b_fifo_full,     b_fifo_empty;

    b_chan_t               slv_b_chan;
    select_t               b_select;
    logic                  slv_b_valid,     slv_b_ready;

    //--------------------------------------
    // Read Transaction
    //--------------------------------------
    ar_chan_select_t slv_ar_chan;
    logic            slv_ar_valid,    slv_ar_ready;

    logic            r_fifo_push,     r_fifo_pop;
    logic            r_fifo_full,     r_fifo_empty;

    r_chan_t         slv_r_chan;
    select_t         r_select;
    logic            slv_r_valid,     slv_r_ready;

    //--------------------------------------
    //--------------------------------------
    // Channel control
    //--------------------------------------
    //--------------------------------------

    //--------------------------------------
    // AW Channel
    //--------------------------------------
    // Workaround for bug in Questa 2021.1: Flatten the struct into a logic vector before
    // instantiating `spill_register`.
    typedef logic [$bits(aw_chan_select_t)-1:0] aw_chan_select_flat_t;
    aw_chan_select_flat_t slv_aw_chan_select_in_flat,
                          slv_aw_chan_select_out_flat;
    assign slv_aw_chan_select_in_flat = {slv_req_i.aw, slv_aw_select_i};
    spill_register #(
      .T      ( aw_chan_select_flat_t         ),
      .Bypass ( ~SpillAw                      )
    ) i_aw_spill_reg (
      .clk_i   ( clk_i                        ),
      .rst_ni  ( rst_ni                       ),
      .valid_i ( slv_req_i.aw_valid           ),
      .ready_o ( slv_resp_o.aw_ready          ),
      .data_i  ( slv_aw_chan_select_in_flat   ),
      .valid_o ( slv_aw_valid                 ),
      .ready_i ( slv_aw_ready                 ),
      .data_o  ( slv_aw_chan_select_out_flat  )
    );
    assign slv_aw_chan = slv_aw_chan_select_out_flat;

    // replicate AW channel to the request output
    for (genvar i = 0; i < NoMstPorts; i++) begin : gen_mst_aw
      assign mst_reqs_o[i].aw       = slv_aw_chan.aw;
      assign mst_reqs_o[i].aw_valid = mst_aw_valids[i];
      assign mst_aw_readies[i]      = mst_resps_i[i].aw_ready;
    end

    // AW channel handshake control
    always_comb begin
      // default assignments
      lock_aw_valid_d = lock_aw_valid_q;
      load_aw_lock    = 1'b0;
      // handshake
      slv_aw_ready    = 1'b0;
      mst_aw_valids   = '0;
      // W FIFO input control
      w_fifo_push     = 1'b0;
      // control
      if (lock_aw_valid_q) begin
        // AW channel is locked and has valid output, fifo was pushed, as the new request was issued
        mst_aw_valids[slv_aw_chan.select] = 1'b1;
        if (mst_aw_readies[slv_aw_chan.select]) begin
          // transaction, go back to IDLE
          slv_aw_ready    = 1'b1;
          lock_aw_valid_d = 1'b0;
          load_aw_lock    = 1'b1;
        end
      end else begin
        if (!w_fifo_full && slv_aw_valid) begin
          // new transaction, push select in the FIFO and then look if transaction happened
          w_fifo_push                       = 1'b1;
          mst_aw_valids[slv_aw_chan.select] = 1'b1; // only set the valid when FIFO is not full
          if (mst_aw_readies[slv_aw_chan.select]) begin
            // transaction, notify slave port
            slv_aw_ready = 1'b1;
          end else begin
            // no transaction, lock valid
            lock_aw_valid_d = 1'b1;
            load_aw_lock    = 1'b1;
          end
        end
      end
    end

    // lock the valid signal, as the selection gets pushed into the W FIFO on first assertion,
    // prevent further pushing
    `FFLARN(lock_aw_valid_q, lock_aw_valid_d, load_aw_lock, '0, clk_i, rst_ni)

    fifo_v3 #(
      .FALL_THROUGH( FallThrough ),
      .DEPTH       ( MaxTrans    ),
      .dtype       ( select_t    )
    ) i_w_fifo (
      .clk_i      ( clk_i              ),
      .rst_ni     ( rst_ni             ),
      .flush_i    ( 1'b0               ), // not used, because AXI4-Lite no preemtion rule
      .testmode_i ( test_i             ),
      .full_o     ( w_fifo_full        ),
      .empty_o    ( w_fifo_empty       ),
      .usage_o    ( /*not used*/       ),
      .data_i     ( slv_aw_chan.select ),
      .push_i     ( w_fifo_push        ),
      .data_o     ( w_select           ),
      .pop_i      ( w_fifo_pop         )
    );

    //--------------------------------------
    // W Channel
    //--------------------------------------
    spill_register #(
      .T      ( w_chan_t ),
      .Bypass ( ~SpillW  )
    ) i_w_spill_reg (
      .clk_i   ( clk_i              ),
      .rst_ni  ( rst_ni             ),
      .valid_i ( slv_req_i.w_valid  ),
      .ready_o ( slv_resp_o.w_ready ),
      .data_i  ( slv_req_i.w        ),
      .valid_o ( slv_w_valid        ),
      .ready_i ( slv_w_ready        ),
      .data_o  ( slv_w_chan         )
    );

    // replicate W channel
    for (genvar i = 0; i < NoMstPorts; i++) begin : gen_mst_w
      assign mst_reqs_o[i].w       = slv_w_chan;
      assign mst_reqs_o[i].w_valid = ~w_fifo_empty & ~b_fifo_full &
                                       slv_w_valid & (w_select == select_t'(i));
    end
    assign slv_w_ready = ~w_fifo_empty & ~b_fifo_full & mst_resps_i[w_select].w_ready;
    assign w_fifo_pop  = slv_w_valid & slv_w_ready;

    fifo_v3 #(
      .FALL_THROUGH( FallThrough ),
      .DEPTH       ( MaxTrans    ),
      .dtype       ( select_t    )
    ) i_b_fifo (
      .clk_i      ( clk_i        ),
      .rst_ni     ( rst_ni       ),
      .flush_i    ( 1'b0         ), // not used, because AXI4-Lite no preemption
      .testmode_i ( test_i       ),
      .full_o     ( b_fifo_full  ),
      .empty_o    ( b_fifo_empty ),
      .usage_o    ( /*not used*/ ),
      .data_i     ( w_select     ),
      .push_i     ( w_fifo_pop   ), // w beat was transferred, push selection to b channel
      .data_o     ( b_select     ),
      .pop_i      ( b_fifo_pop   )
    );

    //--------------------------------------
    // B Channel
    //--------------------------------------
    spill_register #(
      .T      ( b_chan_t ),
      .Bypass ( ~SpillB  )
    ) i_b_spill_reg (
      .clk_i   ( clk_i              ),
      .rst_ni  ( rst_ni             ),
      .valid_i ( slv_b_valid        ),
      .ready_o ( slv_b_ready        ),
      .data_i  ( slv_b_chan         ),
      .valid_o ( slv_resp_o.b_valid ),
      .ready_i ( slv_req_i.b_ready  ),
      .data_o  ( slv_resp_o.b       )
    );

    // connect the response if the FIFO has valid data in it
    assign slv_b_chan      = (!b_fifo_empty) ? mst_resps_i[b_select].b : '0;
    assign slv_b_valid     =  ~b_fifo_empty  & mst_resps_i[b_select].b_valid;
    for (genvar i = 0; i < NoMstPorts; i++) begin : gen_mst_b
      assign mst_reqs_o[i].b_ready = ~b_fifo_empty & slv_b_ready & (b_select == select_t'(i));
    end
    assign b_fifo_pop = slv_b_valid & slv_b_ready;

    //--------------------------------------
    // AR Channel
    //--------------------------------------
    // Workaround for bug in Questa 2021.1: Flatten the struct into a logic vector before
    // instantiating `spill_register`.
    typedef logic [$bits(ar_chan_select_t)-1:0] ar_chan_select_flat_t;
    ar_chan_select_flat_t slv_ar_chan_select_in_flat,
                          slv_ar_chan_select_out_flat;
    assign slv_ar_chan_select_in_flat = {slv_req_i.ar, slv_ar_select_i};
    spill_register #(
      .T      ( ar_chan_select_flat_t         ),
      .Bypass ( ~SpillAr                      )
    ) i_ar_spill_reg (
      .clk_i   ( clk_i                        ),
      .rst_ni  ( rst_ni                       ),
      .valid_i ( slv_req_i.ar_valid           ),
      .ready_o ( slv_resp_o.ar_ready          ),
      .data_i  ( slv_ar_chan_select_in_flat   ),
      .valid_o ( slv_ar_valid                 ),
      .ready_i ( slv_ar_ready                 ),
      .data_o  ( slv_ar_chan_select_out_flat  )
    );
    assign slv_ar_chan = slv_ar_chan_select_out_flat;

    // replicate AR channel
    for (genvar i = 0; i < NoMstPorts; i++) begin : gen_mst_ar
      assign mst_reqs_o[i].ar       = slv_ar_chan.ar;
      assign mst_reqs_o[i].ar_valid = ~r_fifo_full & slv_ar_valid &
                                       (slv_ar_chan.select == select_t'(i));
    end
    assign slv_ar_ready = ~r_fifo_full & mst_resps_i[slv_ar_chan.select].ar_ready;
    assign r_fifo_push  = slv_ar_valid & slv_ar_ready;

    fifo_v3 #(
      .FALL_THROUGH( FallThrough ),
      .DEPTH       ( MaxTrans    ),
      .dtype       ( select_t    )
    ) i_r_fifo (
      .clk_i      ( clk_i              ),
      .rst_ni     ( rst_ni             ),
      .flush_i    ( 1'b0               ), // not used, because AXI4-Lite no preemption rule
      .testmode_i ( test_i             ),
      .full_o     ( r_fifo_full        ),
      .empty_o    ( r_fifo_empty       ),
      .usage_o    ( /*not used*/       ),
      .data_i     ( slv_ar_chan.select ),
      .push_i     ( r_fifo_push        ),
      .data_o     ( r_select           ),
      .pop_i      ( r_fifo_pop         )
    );

    //--------------------------------------
    // R Channel
    //--------------------------------------
    spill_register #(
      .T      ( r_chan_t ),
      .Bypass ( ~SpillR  )
    ) i_r_spill_reg (
      .clk_i   ( clk_i              ),
      .rst_ni  ( rst_ni             ),
      .valid_i ( slv_r_valid        ),
      .ready_o ( slv_r_ready        ),
      .data_i  ( slv_r_chan         ),
      .valid_o ( slv_resp_o.r_valid ),
      .ready_i ( slv_req_i.r_ready  ),
      .data_o  ( slv_resp_o.r       )
    );

    // connect the response if the FIFO has valid data in it
    assign slv_r_chan      = (!r_fifo_empty) ? mst_resps_i[r_select].r : '0;
    assign slv_r_valid     =  ~r_fifo_empty  & mst_resps_i[r_select].r_valid;
    for (genvar i = 0; i < NoMstPorts; i++) begin : gen_mst_r
      assign mst_reqs_o[i].r_ready = ~r_fifo_empty & slv_r_ready & (r_select == select_t'(i));
    end
    assign r_fifo_pop      = slv_r_valid & slv_r_ready;

    // pragma translate_off
    `ifndef VERILATOR
    default disable iff (!rst_ni);
    aw_select: assume property( @(posedge clk_i) (slv_req_i.aw_valid |->
                                                 (slv_aw_select_i < NoMstPorts))) else
      $fatal(1, "slv_aw_select_i is %d: AW has selected a slave that is not defined.\
                 NoMstPorts: %d", slv_aw_select_i, NoMstPorts);
    ar_select: assume property( @(posedge clk_i) (slv_req_i.ar_valid |->
                                                 (slv_ar_select_i < NoMstPorts))) else
      $fatal(1, "slv_ar_select_i is %d: AR has selected a slave that is not defined.\
                 NoMstPorts: %d", slv_ar_select_i, NoMstPorts);
    aw_valid_stable: assert property( @(posedge clk_i) (slv_aw_valid && !slv_aw_ready)
                                                       |=> slv_aw_valid) else
      $fatal(1, "aw_valid was deasserted, when aw_ready = 0 in last cycle.");
    ar_valid_stable: assert property( @(posedge clk_i) (slv_ar_valid && !slv_ar_ready)
                                                       |=> slv_ar_valid) else
      $fatal(1, "ar_valid was deasserted, when ar_ready = 0 in last cycle.");
    aw_stable: assert property( @(posedge clk_i) (slv_aw_valid && !slv_aw_ready)
                               |=> $stable(slv_aw_chan)) else
      $fatal(1, "slv_aw_chan_select unstable with valid set.");
    ar_stable: assert property( @(posedge clk_i) (slv_ar_valid && !slv_ar_ready)
                               |=> $stable(slv_ar_chan)) else
      $fatal(1, "slv_aw_chan_select unstable with valid set.");
    `endif
    // pragma translate_on
  end

  // pragma translate_off
  `ifndef VERILATOR
    initial begin: p_assertions
      NoPorts:  assert (NoMstPorts > 0) else $fatal("Number of master ports must be at least 1!");
      MaxTnx:   assert (MaxTrans   > 0) else $fatal("Number of transactions must be at least 1!");
    end
  `endif
  // pragma translate_on
endmodule

`include "axi/assign.svh"
`include "axi/typedef.svh"

module axi_lite_demux_intf #(
  parameter int unsigned AxiAddrWidth = 32'd0,
  parameter int unsigned AxiDataWidth = 32'd0,
  parameter int unsigned NoMstPorts   = 32'd0,
  parameter int unsigned MaxTrans     = 32'd0,
  parameter bit          FallThrough  = 1'b0,
  parameter bit          SpillAw      = 1'b1,
  parameter bit          SpillW       = 1'b0,
  parameter bit          SpillB       = 1'b0,
  parameter bit          SpillAr      = 1'b1,
  parameter bit          SpillR       = 1'b0,
  // Dependent parameters, DO NOT OVERRIDE!
  parameter type         select_t     = logic [$clog2(NoMstPorts)-1:0]
) (
  input  logic     clk_i,               // Clock
  input  logic     rst_ni,              // Asynchronous reset active low
  input  logic     test_i,              // Testmode enable
  input  select_t  slv_aw_select_i,     // has to be stable, when aw_valid
  input  select_t  slv_ar_select_i,     // has to be stable, when ar_valid
  AXI_LITE.Slave   slv,                 // slave port
  AXI_LITE.Master  mst [NoMstPorts-1:0] // master ports
);
  typedef logic [AxiAddrWidth-1:0]   addr_t;
  typedef logic [AxiDataWidth-1:0]   data_t;
  typedef logic [AxiDataWidth/8-1:0] strb_t;
  `AXI_LITE_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t)
  `AXI_LITE_TYPEDEF_W_CHAN_T(w_chan_t, data_t, strb_t)
  `AXI_LITE_TYPEDEF_B_CHAN_T(b_chan_t)
  `AXI_LITE_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t)
  `AXI_LITE_TYPEDEF_R_CHAN_T(r_chan_t, data_t)
  `AXI_LITE_TYPEDEF_REQ_T(req_t, aw_chan_t, w_chan_t, ar_chan_t)
  `AXI_LITE_TYPEDEF_RESP_T(resp_t, b_chan_t, r_chan_t)

  req_t                   slv_req;
  resp_t                  slv_resp;
  req_t  [NoMstPorts-1:0] mst_reqs;
  resp_t [NoMstPorts-1:0] mst_resps;

  `AXI_LITE_ASSIGN_TO_REQ(slv_req, slv)
  `AXI_LITE_ASSIGN_FROM_RESP(slv, slv_resp)

  for (genvar i = 0; i < NoMstPorts; i++) begin : gen_assign_mst_ports
    `AXI_LITE_ASSIGN_FROM_REQ(mst[i], mst_reqs[i])
    `AXI_LITE_ASSIGN_TO_RESP(mst_resps[i], mst[i])
  end

  axi_lite_demux #(
    .aw_chan_t   ( aw_chan_t   ),
    .w_chan_t    (  w_chan_t   ),
    .b_chan_t    (  b_chan_t   ),
    .ar_chan_t   ( ar_chan_t   ),
    .r_chan_t    (  r_chan_t   ),
    .req_t       (     req_t   ),
    .resp_t      (    resp_t   ),
    .NoMstPorts  ( NoMstPorts  ),
    .MaxTrans    ( MaxTrans    ),
    .FallThrough ( FallThrough ),
    .SpillAw     ( SpillAw     ),
    .SpillW      ( SpillW      ),
    .SpillB      ( SpillB      ),
    .SpillAr     ( SpillAr     ),
    .SpillR      ( SpillR      )
  ) i_axi_demux (
    .clk_i,
    .rst_ni,
    .test_i,
    // slave Port
    .slv_req_i       ( slv_req         ),
    .slv_aw_select_i ( slv_aw_select_i ), // must be stable while slv_aw_valid_i
    .slv_ar_select_i ( slv_ar_select_i ), // must be stable while slv_ar_valid_i
    .slv_resp_o      ( slv_resp        ),
    // mster ports
    .mst_reqs_o      ( mst_reqs        ),
    .mst_resps_i     ( mst_resps       )
  );

  // pragma translate_off
  `ifndef VERILATOR
    initial begin: p_assertions
      AddrWidth: assert (AxiAddrWidth > 0) else $fatal("Axi Parmeter has to be > 0!");
      DataWidth: assert (AxiDataWidth > 0) else $fatal("Axi Parmeter has to be > 0!");
    end
  `endif
  // pragma translate_on
endmodule
