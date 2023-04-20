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
// - Thomas Benz <tbenz@iis.ee.ethz.ch>

`include "axi/assign.svh"
/// Synthesizable test module comparing two AXI channels of the same type
/// This module is meant to be used in FPGA-based verification.
module axi_bus_compare #(
    /// ID width of the AXI4+ATOP interface
    parameter int unsigned AxiIdWidth = 32'd0,
    /// FIFO depth
    parameter int unsigned FifoDepth  = 32'd0,
    /// AW channel type of the AXI4+ATOP interface
    parameter type axi_aw_chan_t = logic,
    /// W channel type of the AXI4+ATOP interface
    parameter type axi_w_chan_t  = logic,
    /// B channel type of the AXI4+ATOP interface
    parameter type axi_b_chan_t  = logic,
    /// AR channel type of the AXI4+ATOP interface
    parameter type axi_ar_chan_t = logic,
    /// R channel type of the AXI4+ATOP interface
    parameter type axi_r_chan_t  = logic,
    /// Request struct type of the AXI4+ATOP slave port
    parameter type axi_req_t     = logic,
    /// Response struct type of the AXI4+ATOP slave port
    parameter type axi_rsp_t     = logic,
    /// ID type (*do not overwrite*)
    parameter type id_t          = logic [2**AxiIdWidth-1:0]
)(
    /// Clock
    input  logic     clk_i,
    /// Asynchronous reset, active low
    input  logic     rst_ni,
    /// Testmode
    input  logic     testmode_i,
    /// AXI4+ATOP A channel request in
    input  axi_req_t axi_a_req_i,
    /// AXI4+ATOP A channel response out
    output axi_rsp_t axi_a_rsp_o,
    /// AXI4+ATOP A channel request out
    output axi_req_t axi_a_req_o,
    /// AXI4+ATOP A channel response in
    input  axi_rsp_t axi_a_rsp_i,
    /// AXI4+ATOP B channel request in
    input  axi_req_t axi_b_req_i,
    /// AXI4+ATOP B channel response out
    output axi_rsp_t axi_b_rsp_o,
    /// AXI4+ATOP B channel request out
    output axi_req_t axi_b_req_o,
    /// AXI4+ATOP B channel response in
    input  axi_rsp_t axi_b_rsp_i,
    /// AW mismatch
    output id_t      aw_mismatch_o,
    /// W mismatch
    output logic     w_mismatch_o,
    /// B mismatch
    output id_t      b_mismatch_o,
    /// AR mismatch
    output id_t      ar_mismatch_o,
    /// R mismatch
    output id_t      r_mismatch_o,
    /// General mismatch
    output logic     mismatch_o,
    /// Unit is busy
    output logic     busy_o
);


    //-----------------------------------
    // Channel Signals
    //-----------------------------------
    // assign request payload A

    `AXI_ASSIGN_AW_STRUCT(axi_a_req_o.aw, axi_a_req_i.aw)
    `AXI_ASSIGN_W_STRUCT(axi_a_req_o.w, axi_a_req_i.w)
    `AXI_ASSIGN_AR_STRUCT(axi_a_req_o.ar, axi_a_req_i.ar)

    // assign response payload A
    `AXI_ASSIGN_R_STRUCT(axi_a_rsp_o.r, axi_a_rsp_i.r)
    `AXI_ASSIGN_B_STRUCT(axi_a_rsp_o.b, axi_a_rsp_i.b)

    // assign request payload B
    `AXI_ASSIGN_AW_STRUCT(axi_b_req_o.aw, axi_b_req_i.aw)
    `AXI_ASSIGN_W_STRUCT(axi_b_req_o.w, axi_b_req_i.w)
    `AXI_ASSIGN_AR_STRUCT(axi_b_req_o.ar, axi_b_req_i.ar)

    // assign response payload B
    `AXI_ASSIGN_R_STRUCT(axi_b_rsp_o.r, axi_b_rsp_i.r)
    `AXI_ASSIGN_B_STRUCT(axi_b_rsp_o.b, axi_b_rsp_i.b)

    // fifo handshaking signals A
    id_t  fifo_valid_aw_a, fifo_ready_aw_a;
    id_t  fifo_valid_b_a,  fifo_ready_b_a;
    id_t  fifo_valid_ar_a, fifo_ready_ar_a;
    id_t  fifo_valid_r_a,  fifo_ready_r_a;

    logic fifo_sel_valid_aw_a, fifo_sel_ready_aw_a;
    logic fifo_sel_valid_w_a,  fifo_sel_ready_w_a;
    logic fifo_sel_valid_b_a,  fifo_sel_ready_b_a;
    logic fifo_sel_valid_ar_a, fifo_sel_ready_ar_a;
    logic fifo_sel_valid_r_a,  fifo_sel_ready_r_a;

    // fifo handshaking signals B
    id_t  fifo_valid_aw_b, fifo_ready_aw_b;
    id_t  fifo_valid_b_b,  fifo_ready_b_b;
    id_t  fifo_valid_ar_b, fifo_ready_ar_b;
    id_t  fifo_valid_r_b,  fifo_ready_r_b;

    logic fifo_sel_valid_aw_b, fifo_sel_ready_aw_b;
    logic fifo_sel_valid_w_b,  fifo_sel_ready_w_b;
    logic fifo_sel_valid_b_b,  fifo_sel_ready_b_b;
    logic fifo_sel_valid_ar_b, fifo_sel_ready_ar_b;
    logic fifo_sel_valid_r_b,  fifo_sel_ready_r_b;


    //-----------------------------------
    // FIFO Output Signals
    //-----------------------------------
    id_t  fifo_cmp_valid_aw_a;
    logic fifo_cmp_valid_w_a;
    id_t  fifo_cmp_valid_b_a;
    id_t  fifo_cmp_valid_ar_a;
    id_t  fifo_cmp_valid_r_a;

    id_t  fifo_cmp_valid_aw_b;
    logic fifo_cmp_valid_w_b;
    id_t  fifo_cmp_valid_b_b;
    id_t  fifo_cmp_valid_ar_b;
    id_t  fifo_cmp_valid_r_b;

    axi_aw_chan_t [2**AxiIdWidth-1:0] fifo_cmp_data_aw_a;
    axi_w_chan_t                      fifo_cmp_data_w_a;
    axi_b_chan_t  [2**AxiIdWidth-1:0] fifo_cmp_data_b_a;
    axi_ar_chan_t [2**AxiIdWidth-1:0] fifo_cmp_data_ar_a;
    axi_r_chan_t  [2**AxiIdWidth-1:0] fifo_cmp_data_r_a;

    axi_aw_chan_t [2**AxiIdWidth-1:0] fifo_cmp_data_aw_b;
    axi_w_chan_t                      fifo_cmp_data_w_b;
    axi_b_chan_t  [2**AxiIdWidth-1:0] fifo_cmp_data_b_b;
    axi_ar_chan_t [2**AxiIdWidth-1:0] fifo_cmp_data_ar_b;
    axi_r_chan_t  [2**AxiIdWidth-1:0] fifo_cmp_data_r_b;


    //-----------------------------------
    // Channel A stream forks
    //-----------------------------------
    stream_fork #(
        .N_OUP ( 32'd2 )
    ) i_stream_fork_aw_a (
        .clk_i,
        .rst_ni,
        .valid_i ( axi_a_req_i.aw_valid                        ),
        .ready_o ( axi_a_rsp_o.aw_ready                        ),
        .valid_o ( {fifo_sel_valid_aw_a, axi_a_req_o.aw_valid} ),
        .ready_i ( {fifo_sel_ready_aw_a, axi_a_rsp_i.aw_ready} )
    );

    stream_fork #(
        .N_OUP ( 32'd2 )
    ) i_stream_fork_w_a (
        .clk_i,
        .rst_ni,
        .valid_i ( axi_a_req_i.w_valid                       ),
        .ready_o ( axi_a_rsp_o.w_ready                       ),
        .valid_o ( {fifo_sel_valid_w_a, axi_a_req_o.w_valid} ),
        .ready_i ( {fifo_sel_ready_w_a, axi_a_rsp_i.w_ready} )
    );

    stream_fork #(
        .N_OUP ( 32'd2 )
    ) i_stream_fork_b_a (
        .clk_i,
        .rst_ni,
        .valid_i ( axi_a_rsp_i.b_valid                       ),
        .ready_o ( axi_a_req_o.b_ready                       ),
        .valid_o ( {fifo_sel_valid_b_a, axi_a_rsp_o.b_valid} ),
        .ready_i ( {fifo_sel_ready_b_a, axi_a_req_i.b_ready} )
    );

    stream_fork #(
        .N_OUP ( 32'd2 )
    ) i_stream_fork_ar_a (
        .clk_i,
        .rst_ni,
        .valid_i ( axi_a_req_i.ar_valid                        ),
        .ready_o ( axi_a_rsp_o.ar_ready                        ),
        .valid_o ( {fifo_sel_valid_ar_a, axi_a_req_o.ar_valid} ),
        .ready_i ( {fifo_sel_ready_ar_a, axi_a_rsp_i.ar_ready} )
    );

    stream_fork #(
        .N_OUP ( 32'd2 )
    ) i_stream_fork_r_a (
        .clk_i,
        .rst_ni,
        .valid_i ( axi_a_rsp_i.r_valid                       ),
        .ready_o ( axi_a_req_o.r_ready                       ),
        .valid_o ( {fifo_sel_valid_r_a, axi_a_rsp_o.r_valid} ),
        .ready_i ( {fifo_sel_ready_r_a, axi_a_req_i.r_ready} )
    );


    //-----------------------------------
    // Channel A FIFOs
    //-----------------------------------
    for (genvar id = 0; id < 2**AxiIdWidth; id++) begin : gen_fifos_a

        stream_fifo #(
            .FALL_THROUGH ( 1'b0          ),
            .DATA_WIDTH   ( 1'b0          ),
            .DEPTH        ( FifoDepth     ),
            .T            ( axi_aw_chan_t )
        ) i_stream_fifo_aw_a (
            .clk_i,
            .rst_ni,
            .testmode_i,
            .flush_i    ( 1'b0                                                ),
            .usage_o    ( /* NOT CONNECTED */                                 ),
            .data_i     ( axi_a_req_i.aw                                      ),
            .valid_i    ( fifo_valid_aw_a     [id]                            ),
            .ready_o    ( fifo_ready_aw_a     [id]                            ),
            .data_o     ( fifo_cmp_data_aw_a  [id]                            ),
            .valid_o    ( fifo_cmp_valid_aw_a [id]                            ),
            .ready_i    ( fifo_cmp_valid_aw_a [id] & fifo_cmp_valid_aw_b [id] )
        );

        stream_fifo #(
            .FALL_THROUGH ( 1'b0          ),
            .DATA_WIDTH   ( 1'b0          ),
            .DEPTH        ( FifoDepth     ),
            .T            ( axi_b_chan_t  )
        ) i_stream_fifo_b_a (
            .clk_i,
            .rst_ni,
            .testmode_i,
            .flush_i    ( 1'b0                                              ),
            .usage_o    ( /* NOT CONNECTED */                               ),
            .data_i     ( axi_a_rsp_i.b                                     ),
            .valid_i    ( fifo_valid_b_a     [id]                           ),
            .ready_o    ( fifo_ready_b_a     [id]                           ),
            .data_o     ( fifo_cmp_data_b_a  [id]                           ),
            .valid_o    ( fifo_cmp_valid_b_a [id]                           ),
            .ready_i    ( fifo_cmp_valid_b_a [id] & fifo_cmp_valid_b_b [id] )
        );

        stream_fifo #(
            .FALL_THROUGH ( 1'b0          ),
            .DATA_WIDTH   ( 1'b0          ),
            .DEPTH        ( FifoDepth     ),
            .T            ( axi_ar_chan_t )
        ) i_stream_fifo_ar_a (
            .clk_i,
            .rst_ni,
            .testmode_i,
            .flush_i    ( 1'b0                                                ),
            .usage_o    ( /* NOT CONNECTED */                                 ),
            .data_i     ( axi_a_req_i.ar                                      ),
            .valid_i    ( fifo_valid_ar_a     [id]                            ),
            .ready_o    ( fifo_ready_ar_a     [id]                            ),
            .data_o     ( fifo_cmp_data_ar_a  [id]                            ),
            .valid_o    ( fifo_cmp_valid_ar_a [id]                            ),
            .ready_i    ( fifo_cmp_valid_ar_a [id] & fifo_cmp_valid_ar_b [id] )
        );

        stream_fifo #(
            .FALL_THROUGH ( 1'b0          ),
            .DATA_WIDTH   ( 1'b0          ),
            .DEPTH        ( FifoDepth     ),
            .T            ( axi_r_chan_t  )
        ) i_stream_fifo_r_a (
            .clk_i,
            .rst_ni,
            .testmode_i,
            .flush_i    ( 1'b0                                              ),
            .usage_o    ( /* NOT CONNECTED */                               ),
            .data_i     ( axi_a_rsp_i.r                                     ),
            .valid_i    ( fifo_valid_r_a     [id]                           ),
            .ready_o    ( fifo_ready_r_a     [id]                           ),
            .data_o     ( fifo_cmp_data_r_a  [id]                           ),
            .valid_o    ( fifo_cmp_valid_r_a [id]                           ),
            .ready_i    ( fifo_cmp_valid_r_a [id] & fifo_cmp_valid_r_b [id] )
        );
    end

    stream_fifo #(
        .FALL_THROUGH ( 1'b0          ),
        .DATA_WIDTH   ( 1'b0          ),
        .DEPTH        ( FifoDepth     ),
        .T            ( axi_w_chan_t  )
    ) i_stream_fifo_w_a (
        .clk_i,
        .rst_ni,
        .testmode_i,
        .flush_i    ( 1'b0                                    ),
        .usage_o    ( /* NOT CONNECTED */                     ),
        .data_i     ( axi_a_req_i.w                           ),
        .valid_i    ( fifo_sel_valid_w_a                      ),
        .ready_o    ( fifo_sel_ready_w_a                      ),
        .data_o     ( fifo_cmp_data_w_a                       ),
        .valid_o    ( fifo_cmp_valid_w_a                      ),
        .ready_i    ( fifo_cmp_valid_w_a & fifo_cmp_valid_w_b )
    );


    //-----------------------------------
    // Input Handshaking A
    //-----------------------------------
    always_comb begin : gen_handshaking_a
        // aw
        // defaults
        fifo_valid_aw_a     = '0;
        fifo_sel_ready_aw_a = '0;
        // assign according id
        fifo_valid_aw_a [axi_a_req_i.aw.id] = fifo_sel_valid_aw_a;
        fifo_sel_ready_aw_a                 = fifo_ready_aw_a[axi_a_req_i.aw.id];


        // b
        // defaults
        fifo_valid_b_a      = '0;
        fifo_sel_ready_b_a  = '0;
        // assign according id
        fifo_valid_b_a [axi_a_rsp_i.b.id] = fifo_sel_valid_b_a;
        fifo_sel_ready_b_a                = fifo_ready_b_a[axi_a_rsp_i.b.id];

        // ar
        // defaults
        fifo_valid_ar_a     = '0;
        fifo_sel_ready_ar_a = '0;
        // assign according id
        fifo_valid_ar_a [axi_a_req_i.ar.id] = fifo_sel_valid_ar_a;
        fifo_sel_ready_ar_a                 = fifo_ready_ar_a[axi_a_req_i.ar.id];

        // b
        // defaults
        fifo_valid_r_a      = '0;
        fifo_sel_ready_r_a  = '0;
        // assign according id
        fifo_valid_r_a [axi_a_rsp_i.r.id] = fifo_sel_valid_r_a;
        fifo_sel_ready_r_a                = fifo_ready_r_a[axi_a_rsp_i.r.id];
    end


    //-----------------------------------
    // Channel B stream forks
    //-----------------------------------
    stream_fork #(
        .N_OUP ( 32'd2 )
    ) i_stream_fork_aw_b (
        .clk_i,
        .rst_ni,
        .valid_i ( axi_b_req_i.aw_valid                        ),
        .ready_o ( axi_b_rsp_o.aw_ready                        ),
        .valid_o ( {fifo_sel_valid_aw_b, axi_b_req_o.aw_valid} ),
        .ready_i ( {fifo_sel_ready_aw_b, axi_b_rsp_i.aw_ready} )
    );

    stream_fork #(
        .N_OUP ( 32'd2 )
    ) i_stream_fork_w_b (
        .clk_i,
        .rst_ni,
        .valid_i ( axi_b_req_i.w_valid                       ),
        .ready_o ( axi_b_rsp_o.w_ready                       ),
        .valid_o ( {fifo_sel_valid_w_b, axi_b_req_o.w_valid} ),
        .ready_i ( {fifo_sel_ready_w_b, axi_b_rsp_i.w_ready} )
    );

    stream_fork #(
        .N_OUP ( 32'd2 )
    ) i_stream_fork_b_b (
        .clk_i,
        .rst_ni,
        .valid_i ( axi_b_rsp_i.b_valid                       ),
        .ready_o ( axi_b_req_o.b_ready                       ),
        .valid_o ( {fifo_sel_valid_b_b, axi_b_rsp_o.b_valid} ),
        .ready_i ( {fifo_sel_ready_b_b, axi_b_req_i.b_ready} )
    );

    stream_fork #(
        .N_OUP ( 32'd2 )
    ) i_stream_fork_ar_b (
        .clk_i,
        .rst_ni,
        .valid_i ( axi_b_req_i.ar_valid                        ),
        .ready_o ( axi_b_rsp_o.ar_ready                        ),
        .valid_o ( {fifo_sel_valid_ar_b, axi_b_req_o.ar_valid} ),
        .ready_i ( {fifo_sel_ready_ar_b, axi_b_rsp_i.ar_ready} )
    );

    stream_fork #(
        .N_OUP ( 32'd2 )
    ) i_stream_fork_r_b (
        .clk_i,
        .rst_ni,
        .valid_i ( axi_b_rsp_i.r_valid                       ),
        .ready_o ( axi_b_req_o.r_ready                       ),
        .valid_o ( {fifo_sel_valid_r_b, axi_b_rsp_o.r_valid} ),
        .ready_i ( {fifo_sel_ready_r_b, axi_b_req_i.r_ready} )
    );


    //-----------------------------------
    // Channel B FIFOs
    //-----------------------------------
    for (genvar id = 0; id < 2**AxiIdWidth; id++) begin : gen_fifos_b

        stream_fifo #(
            .FALL_THROUGH ( 1'b0          ),
            .DATA_WIDTH   ( 1'b0          ),
            .DEPTH        ( FifoDepth     ),
            .T            ( axi_aw_chan_t )
        ) i_stream_fifo_aw_b (
            .clk_i,
            .rst_ni,
            .testmode_i,
            .flush_i    ( 1'b0                                                ),
            .usage_o    ( /* NOT CONNECTED */                                 ),
            .data_i     ( axi_b_req_i.aw                                      ),
            .valid_i    ( fifo_valid_aw_b     [id]                            ),
            .ready_o    ( fifo_ready_aw_b     [id]                            ),
            .data_o     ( fifo_cmp_data_aw_b  [id]                            ),
            .valid_o    ( fifo_cmp_valid_aw_b [id]                            ),
            .ready_i    ( fifo_cmp_valid_aw_a [id] & fifo_cmp_valid_aw_b [id] )
        );

        stream_fifo #(
            .FALL_THROUGH ( 1'b0          ),
            .DATA_WIDTH   ( 1'b0          ),
            .DEPTH        ( FifoDepth     ),
            .T            ( axi_b_chan_t  )
        ) i_stream_fifo_b_b (
            .clk_i,
            .rst_ni,
            .testmode_i,
            .flush_i    ( 1'b0                                               ),
            .usage_o    ( /* NOT CONNECTED */                                ),
            .data_i     ( axi_b_rsp_i.b                                      ),
            .valid_i    ( fifo_valid_b_b      [id]                           ),
            .ready_o    ( fifo_ready_b_b      [id]                           ),
            .data_o     ( fifo_cmp_data_b_b   [id]                           ),
            .valid_o    ( fifo_cmp_valid_b_b  [id]                           ),
            .ready_i    ( fifo_cmp_valid_b_a  [id] & fifo_cmp_valid_b_b [id] )
        );

        stream_fifo #(
            .FALL_THROUGH ( 1'b0          ),
            .DATA_WIDTH   ( 1'b0          ),
            .DEPTH        ( FifoDepth     ),
            .T            ( axi_ar_chan_t )
        ) i_stream_fifo_ar_b (
            .clk_i,
            .rst_ni,
            .testmode_i,
            .flush_i    ( 1'b0                                                ),
            .usage_o    ( /* NOT CONNECTED */                                 ),
            .data_i     ( axi_b_req_i.ar                                      ),
            .valid_i    ( fifo_valid_ar_b     [id]                            ),
            .ready_o    ( fifo_ready_ar_b     [id]                            ),
            .data_o     ( fifo_cmp_data_ar_b  [id]                            ),
            .valid_o    ( fifo_cmp_valid_ar_b [id]                            ),
            .ready_i    ( fifo_cmp_valid_ar_a [id] & fifo_cmp_valid_ar_b [id] )
        );

        stream_fifo #(
            .FALL_THROUGH ( 1'b0          ),
            .DATA_WIDTH   ( 1'b0          ),
            .DEPTH        ( FifoDepth     ),
            .T            ( axi_r_chan_t  )
        ) i_stream_fifo_r_b (
            .clk_i,
            .rst_ni,
            .testmode_i,
            .flush_i    ( 1'b0                                               ),
            .usage_o    ( /* NOT CONNECTED */                                ),
            .data_i     ( axi_b_rsp_i.r                                      ),
            .valid_i    ( fifo_valid_r_b      [id]                           ),
            .ready_o    ( fifo_ready_r_b      [id]                           ),
            .data_o     ( fifo_cmp_data_r_b   [id]                           ),
            .valid_o    ( fifo_cmp_valid_r_b  [id]                           ),
            .ready_i    ( fifo_cmp_valid_r_a  [id] & fifo_cmp_valid_r_b [id] )
        );
    end

    stream_fifo #(
        .FALL_THROUGH ( 1'b0          ),
        .DATA_WIDTH   ( 1'b0          ),
        .DEPTH        ( FifoDepth     ),
        .T            ( axi_w_chan_t  )
    ) i_stream_fifo_w_b (
        .clk_i,
        .rst_ni,
        .testmode_i,
        .flush_i    ( 1'b0                                    ),
        .usage_o    ( /* NOT CONNECTED */                     ),
        .data_i     ( axi_b_req_i.w                           ),
        .valid_i    ( fifo_sel_valid_w_b                      ),
        .ready_o    ( fifo_sel_ready_w_b                      ),
        .data_o     ( fifo_cmp_data_w_b                       ),
        .valid_o    ( fifo_cmp_valid_w_b                      ),
        .ready_i    ( fifo_cmp_valid_w_a & fifo_cmp_valid_w_b )
    );


    //-----------------------------------
    // Input Handshaking B
    //-----------------------------------
    always_comb begin : gen_handshaking_b
        // aw
        // defaults
        fifo_valid_aw_b     = '0;
        fifo_sel_ready_aw_b = '0;
        // assign according id
        fifo_valid_aw_b [axi_b_req_i.aw.id] = fifo_sel_valid_aw_b;
        fifo_sel_ready_aw_b                 = fifo_ready_aw_b[axi_b_req_i.aw.id];


        // b
        // defaults
        fifo_valid_b_b      = '0;
        fifo_sel_ready_b_b  = '0;
        // assign according id
        fifo_valid_b_b [axi_b_rsp_i.b.id] = fifo_sel_valid_b_b;
        fifo_sel_ready_b_b                = fifo_ready_b_b[axi_b_rsp_i.b.id];

        // ar
        // defaults
        fifo_valid_ar_b     = '0;
        fifo_sel_ready_ar_b = '0;
        // assign according id
        fifo_valid_ar_b [axi_b_req_i.ar.id] = fifo_sel_valid_ar_b;
        fifo_sel_ready_ar_b                 = fifo_ready_ar_b[axi_b_req_i.ar.id];

        // b
        // defaults
        fifo_valid_r_b      = '0;
        fifo_sel_ready_r_b  = '0;
        // assign according id
        fifo_valid_r_b [axi_b_rsp_i.r.id] = fifo_sel_valid_r_b;
        fifo_sel_ready_r_b                = fifo_ready_r_b[axi_b_rsp_i.r.id];
    end


    //-----------------------------------
    // Comparison
    //-----------------------------------
    for (genvar id = 0; id < 2**AxiIdWidth; id++) begin : gen_cmp
        assign aw_mismatch_o [id] = (fifo_cmp_valid_aw_a [id] & fifo_cmp_valid_aw_b [id]) ?
                                     fifo_cmp_data_aw_a  [id] == fifo_cmp_data_aw_b [id] : '0;
        assign b_mismatch_o  [id] = (fifo_cmp_valid_b_a  [id] & fifo_cmp_valid_b_b  [id]) ?
                                     fifo_cmp_data_b_a   [id] == fifo_cmp_data_b_b  [id] : '0;
        assign ar_mismatch_o [id] = (fifo_cmp_valid_ar_a [id] & fifo_cmp_valid_ar_b [id]) ?
                                     fifo_cmp_data_ar_a  [id] == fifo_cmp_data_ar_b [id] : '0;
        assign r_mismatch_o  [id] = (fifo_cmp_valid_r_a  [id] & fifo_cmp_valid_r_b  [id]) ?
                                     fifo_cmp_data_r_a   [id] == fifo_cmp_data_r_b  [id] : '0;
    end

    assign w_mismatch_o  = (fifo_cmp_valid_w_a  & fifo_cmp_valid_w_b ) ?
                            fifo_cmp_data_w_a  != fifo_cmp_data_w_b  : '0;


    //-----------------------------------
    // Outputs
    //-----------------------------------
    assign busy_o = (|fifo_cmp_valid_aw_a) | (|fifo_cmp_valid_aw_b) |
                    (|fifo_cmp_valid_w_a)  | (|fifo_cmp_valid_w_b)  |
                    (|fifo_cmp_valid_b_a)  | (|fifo_cmp_valid_b_b)  |
                    (|fifo_cmp_valid_ar_a) | (|fifo_cmp_valid_ar_b) |
                    (|fifo_cmp_valid_r_a)  | (|fifo_cmp_valid_r_b);


    assign mismatch_o = (|aw_mismatch_o) | (|w_mismatch_o) | (|b_mismatch_o) |
                        (|ar_mismatch_o) | (|r_mismatch_o);

endmodule
