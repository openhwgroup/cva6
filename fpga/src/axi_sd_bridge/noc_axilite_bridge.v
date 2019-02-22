// ========== Copyright Header Begin ============================================
// Copyright (c) 2015 Princeton University
// All rights reserved.
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are met:
//     * Redistributions of source code must retain the above copyright
//       notice, this list of conditions and the following disclaimer.
//     * Redistributions in binary form must reproduce the above copyright
//       notice, this list of conditions and the following disclaimer in the
//       documentation and/or other materials provided with the distribution.
//     * Neither the name of Princeton University nor the
//       names of its contributors may be used to endorse or promote products
//       derived from this software without specific prior written permission.
//
// THIS SOFTWARE IS PROVIDED BY PRINCETON UNIVERSITY "AS IS" AND
// ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
// WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
// DISCLAIMED. IN NO EVENT SHALL PRINCETON UNIVERSITY BE LIABLE FOR ANY
// DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
// (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
// LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
// ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
// (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
// SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
// ========== Copyright Header End ============================================

//==================================================================================================
//  Filename      : axi_lite_bridge.v
//  Created On    : 2015-10-20
//  Revision      :
//  Author        : Xiaohua Liang & Matthew Matl
//  Company       : Princeton University
//  Email         : xiaohua@princeton.edu & mmatl@princeton.edu
//
//  Description   : Translate the incoming message (in the Piton Messaging
//                  Protocol, via a val/rdy interface) to a series of AXI-Lite
//                  requests.
//==================================================================================================

`include "piton_sd_define.vh"
`define C_M_AXI_LITE_DATA_WIDTH  `NOC_DATA_WIDTH
`define C_M_AXI_LITE_ADDR_WIDTH  `NOC_DATA_WIDTH
`define C_M_AXI_LITE_RESP_WIDTH  2

module noc_axilite_bridge #(
    parameter SLAVE_RESP_BYTEWIDTH = 4,
    parameter SWAP_ENDIANESS       = 0
) (
    // Clock + Reset
    input  wire                                   clk,
    input  wire                                   rst,

    // Memory Splitter -> AXI SPI
    input  wire                                   splitter_bridge_val,
    input  wire [`NOC_DATA_WIDTH-1:0]             splitter_bridge_data,
    output wire                                   bridge_splitter_rdy,

    // Memory Splitter <- AXI SPI
    output  reg                                   bridge_splitter_val,
    output  reg  [`NOC_DATA_WIDTH-1:0]            bridge_splitter_data,
    input  wire                                   splitter_bridge_rdy,

    // AXI Write Address Channel Signals
    output  reg  [`C_M_AXI_LITE_ADDR_WIDTH-1:0]   m_axi_awaddr,
    output  reg                                   m_axi_awvalid,
    input  wire                                   m_axi_awready,

    // AXI Write Data Channel Signals
    output wire  [`C_M_AXI_LITE_DATA_WIDTH-1:0]   m_axi_wdata,
    output  reg  [`C_M_AXI_LITE_DATA_WIDTH/8-1:0] m_axi_wstrb,
    output  reg                                   m_axi_wvalid,
    input  wire                                   m_axi_wready,

    // AXI Read Address Channel Signals
    output  reg  [`C_M_AXI_LITE_ADDR_WIDTH-1:0]   m_axi_araddr,
    output  reg                                   m_axi_arvalid,
    input                                         m_axi_arready,

    // AXI Read Data Channel Signals
    input  wire [`C_M_AXI_LITE_DATA_WIDTH-1:0]    m_axi_rdata,
    input  wire [`C_M_AXI_LITE_RESP_WIDTH-1:0]    m_axi_rresp,
    input  wire                                   m_axi_rvalid,
    output  reg                                   m_axi_rready,

    // AXI Write Response Channel Signals
    input  wire [`C_M_AXI_LITE_RESP_WIDTH-1:0]    m_axi_bresp,
    input  wire                                   m_axi_bvalid,
    output reg                                    m_axi_bready
);

//==============================================================================
// Local Parameters
//==============================================================================

// States for Incoming Piton Messages
localparam MSG_STATE_INVAL      = 3'd0; // Invalid Message
localparam MSG_STATE_HEADER_0   = 3'd1; // Header 0
localparam MSG_STATE_HEADER_1   = 3'd2; // Header 1
localparam MSG_STATE_HEADER_2   = 3'd3; // Header 2
localparam MSG_STATE_DATA       = 3'd4; // Data Lines

// Types for Incoming Piton Messages
localparam MSG_TYPE_INVAL       = 2'd0; // Invalid Message
localparam MSG_TYPE_LOAD        = 2'd1; // Load Request
localparam MSG_TYPE_STORE       = 2'd2; // Store Request

// States for Buffer Status
localparam BUF_STATUS_INCOMP    = 2'd0; // Buffer not yet filled by one complete request/response
localparam BUF_STATUS_COMP      = 2'd1; // Buffer contains a complete but unsent request
localparam BUF_STATUS_WAITRESP  = 2'd2; // Request sent via AXI, waiting on response
localparam BUF_STATUS_RESPSEND  = 2'd3; // Response waiting to forward back to memory splitter

// ACK's
localparam LOAD_ACK = 1'd0;
localparam STORE_ACK = 1'd1;

//==============================================================================
// Local Variables
//==============================================================================

// Meta-registers for tracking incoming Piton packets (used in parsing)
 reg  [2:0]                          splitter_io_msg_state_f;
 reg  [1:0]                          splitter_io_msg_type_f;
 reg  [`MSG_LENGTH_WIDTH-1:0]        splitter_io_msg_counter_f;

// Buffer registers for load requests
 reg  [`NOC_DATA_WIDTH-1:0]          r_req_buf_header0_f;
 reg  [`NOC_DATA_WIDTH-1:0]          r_req_buf_header1_f;
 reg  [`NOC_DATA_WIDTH-1:0]          r_req_buf_header2_f;
 reg  [1:0]                          r_req_buf_status_f;

// Buffer registers for store requests
 reg  [`NOC_DATA_WIDTH-1:0]          w_req_buf_header0_f;
 reg  [`NOC_DATA_WIDTH-1:0]          w_req_buf_header1_f;
 reg  [`NOC_DATA_WIDTH-1:0]          w_req_buf_header2_f;
 reg  [`NOC_DATA_WIDTH-1:0]          w_req_buf_data0_f;
 wire [1:0]                          w_req_buf_status;
 reg  [1:0]                          w_addr_req_buf_status_f;
 reg  [1:0]                          w_data_req_buf_status_f;

// Buffer registers for load responses
 reg  [`NOC_DATA_WIDTH-1:0]          r_resp_buf_header0_f;
 reg  [`C_M_AXI_LITE_DATA_WIDTH-1:0] r_resp_buf_data0_f;
 reg  [`C_M_AXI_LITE_RESP_WIDTH-1:0] r_resp_buf_rresp_f;
 reg  [1:0]                          r_resp_buf_status_f;

// Buffer registers for store responses
 reg  [`NOC_DATA_WIDTH-1:0]          w_resp_buf_header0_f;
 reg  [`C_M_AXI_LITE_RESP_WIDTH-1:0] w_resp_buf_bresp_f;
 wire [1:0]                          w_resp_buf_status;
 reg  [1:0]                          w_addr_resp_buf_status_f;
 reg  [1:0]                          w_data_resp_buf_status_f;

// Helper Signals for saving requests
 wire                         splitter_io_go;
 wire                         splitter_io_load_go;
 wire                         splitter_io_store_go;

 wire                         splitter_io_msg_is_load;
 wire                         splitter_io_msg_is_store;
 wire                         splitter_io_msg_is_load_next;
 wire                         splitter_io_msg_is_store_next;

 wire [2:0]                   splitter_io_msg_state_next;
 wire [2:0]                   splitter_io_msg_type_mux_out;
 wire [2:0]                   splitter_io_msg_type_next;
 wire [`MSG_LENGTH_WIDTH-1:0] splitter_io_msg_counter_next;

// Helper Signals for sending responses
 wire                         m_axi_ar_go;
 wire                         m_axi_w_go;
 wire                         m_axi_aw_go;

 wire                         m_axi_b_go;
 wire                         m_axi_r_go;
 reg  [`NOC_DATA_WIDTH-1:0]   a_axi_rdata_shifted;
 wire [`NOC_DATA_WIDTH-1:0]   a_axi_rdata_masked;

 wire [`NOC_DATA_WIDTH-1:0]   r_resp_buf_header0_next;
 wire [`NOC_DATA_WIDTH-1:0]   w_resp_buf_header0_next;

 reg  [`MSG_LENGTH_WIDTH-1:0] io_splitter_ack_load_counter_f;
 reg                          io_splitter_arb_f;
 reg                          io_splitter_ack_mux_sel;

 wire                         r_resp_buf_val;
 wire                         w_resp_buf_val;
 wire [`NOC_DATA_WIDTH-1:0]   io_splitter_ack_store;
 wire [`NOC_DATA_WIDTH-1:0]   io_splitter_ack_load;
 wire                         io_splitter_ack_load_go;
 wire                         io_splitter_ack_store_go;

//==============================================================================
// Read Requests From Splitter
//==============================================================================

    // What type of message is arriving currently?
    assign splitter_io_msg_type_mux_out =
        (!splitter_bridge_val) ? MSG_TYPE_INVAL :
        (((splitter_bridge_data[`MSG_TYPE] == `MSG_TYPE_LOAD_REQ   )  ||
          (splitter_bridge_data[`MSG_TYPE] == `MSG_TYPE_NC_LOAD_REQ)  ||
          (splitter_bridge_data[`MSG_TYPE] == `MSG_TYPE_LOAD_MEM   )     ) ? MSG_TYPE_LOAD  :
         ((splitter_bridge_data[`MSG_TYPE] == `MSG_TYPE_STORE_REQ   ) ||
          (splitter_bridge_data[`MSG_TYPE] == `MSG_TYPE_NC_STORE_REQ) ||
          (splitter_bridge_data[`MSG_TYPE] == `MSG_TYPE_STORE_MEM   )    ) ? MSG_TYPE_STORE :
                                                                            MSG_TYPE_INVAL );

    // What type of message will we be receiving?
    assign splitter_io_msg_type_next =
        (splitter_io_msg_state_next == MSG_STATE_INVAL   ) ? MSG_TYPE_INVAL               :
        (splitter_io_msg_state_next == MSG_STATE_HEADER_0) ? splitter_io_msg_type_mux_out :
                                                             splitter_io_msg_type_f       ;
    // Is the current message a load or a store?
    assign splitter_io_msg_is_load       = (splitter_io_msg_type_f    == MSG_TYPE_LOAD );
    assign splitter_io_msg_is_store      = (splitter_io_msg_type_f    == MSG_TYPE_STORE);

    // Is the incoming message a load or a store?
    assign splitter_io_msg_is_load_next  = (splitter_io_msg_type_next == MSG_TYPE_LOAD );
    assign splitter_io_msg_is_store_next = (splitter_io_msg_type_next == MSG_TYPE_STORE);

    // Should we read data from splitter_bridge_data?
    assign splitter_io_go = splitter_bridge_val && bridge_splitter_rdy;

    // Should we read a load request (store request)?
    assign splitter_io_load_go  = splitter_io_msg_is_load_next  && splitter_io_go && (r_req_buf_status_f == BUF_STATUS_INCOMP);
    assign splitter_io_store_go = splitter_io_msg_is_store_next && splitter_io_go && (w_req_buf_status   == BUF_STATUS_INCOMP);

    // Next-State logic for incoming message parser
    assign splitter_io_msg_state_next =
        (splitter_io_msg_state_f == MSG_STATE_INVAL   ) ? MSG_STATE_HEADER_0  :
        (splitter_io_msg_state_f == MSG_STATE_HEADER_0) ? MSG_STATE_HEADER_1  :
        (splitter_io_msg_state_f == MSG_STATE_HEADER_1) ? MSG_STATE_HEADER_2  :
        (splitter_io_msg_counter_f == 0               ) ? MSG_STATE_HEADER_0  :
        (splitter_io_msg_state_f == MSG_STATE_HEADER_2) ? MSG_STATE_DATA      :
        (splitter_io_msg_state_f == MSG_STATE_DATA    ) ? MSG_STATE_DATA      :
                                                          MSG_STATE_INVAL     ;

    // Next-value logic for message counter
    assign splitter_io_msg_counter_next =
        (splitter_io_msg_state_next == MSG_STATE_HEADER_0) ? splitter_bridge_data[`MSG_LENGTH] :
                                                             splitter_io_msg_counter_f - 1'b1  ;

    //--------------------------------------------------------------------------
    // Sequential Block for Splitter FSM State
    //--------------------------------------------------------------------------
    always @(posedge clk) begin
        if (rst) begin
            splitter_io_msg_state_f   <= MSG_STATE_INVAL;
            splitter_io_msg_type_f    <= MSG_TYPE_INVAL;
            splitter_io_msg_counter_f <= {`MSG_LENGTH_WIDTH{1'b0}};
        end
        else begin
            splitter_io_msg_state_f   <= splitter_io_go ? splitter_io_msg_state_next
                                                        : splitter_io_msg_state_f;
            splitter_io_msg_type_f    <= splitter_io_go ? splitter_io_msg_type_next
                                                        : splitter_io_msg_type_f;
            splitter_io_msg_counter_f <= splitter_io_go ? splitter_io_msg_counter_next
                                                        : splitter_io_msg_counter_f;
        end
    end

    //--------------------------------------------------------------------------
    // Read headers and data for a load request
    //--------------------------------------------------------------------------
    always @(posedge clk) begin
        if (rst) begin
            r_req_buf_header0_f <= {`NOC_DATA_WIDTH{1'b0}};
            r_req_buf_header1_f <= {`NOC_DATA_WIDTH{1'b0}};
            r_req_buf_header2_f <= {`NOC_DATA_WIDTH{1'b0}};
            r_req_buf_status_f  <= BUF_STATUS_INCOMP;
        end
        else begin
            r_req_buf_header0_f <= (splitter_io_load_go &
                                    (splitter_io_msg_state_next == MSG_STATE_HEADER_0)) ? splitter_bridge_data :
                                                                                          r_req_buf_header0_f  ;
            r_req_buf_header1_f <= (splitter_io_load_go &
                                    (splitter_io_msg_state_next == MSG_STATE_HEADER_1)) ? splitter_bridge_data :
                                                                                          r_req_buf_header1_f  ;
            r_req_buf_header2_f <= (splitter_io_load_go &
                                    (splitter_io_msg_state_next == MSG_STATE_HEADER_2)) ? splitter_bridge_data :
                                                                                          r_req_buf_header2_f  ;
            r_req_buf_status_f  <= (splitter_io_load_go &
                                    (splitter_io_msg_state_next == MSG_STATE_HEADER_2)) ? BUF_STATUS_COMP      :
                                   (m_axi_ar_go)                                        ? BUF_STATUS_INCOMP    :
                                                                                          r_req_buf_status_f   ;
        end
    end

    //--------------------------------------------------------------------------
    // Read headers and data for a store request
    //--------------------------------------------------------------------------
    wire    w_status_update;
    assign  w_status_update =   splitter_io_store_go &
                                (splitter_io_msg_state_next == MSG_STATE_DATA) &
                                (splitter_io_msg_counter_f == `MSG_LENGTH_WIDTH'd1);

    always @(posedge clk) begin
        if (rst) begin
            w_req_buf_header0_f     <= {`NOC_DATA_WIDTH{1'b0}};
            w_req_buf_header1_f     <= {`NOC_DATA_WIDTH{1'b0}};
            w_req_buf_header2_f     <= {`NOC_DATA_WIDTH{1'b0}};
            w_req_buf_data0_f       <= {`NOC_DATA_WIDTH{1'b0}};
            w_addr_req_buf_status_f <= BUF_STATUS_INCOMP;
            w_data_req_buf_status_f <= BUF_STATUS_INCOMP;
        end
        else begin
            w_req_buf_header0_f     <= (splitter_io_store_go &
                                        (splitter_io_msg_state_next == MSG_STATE_HEADER_0)) ? splitter_bridge_data    :
                                                                                              w_req_buf_header0_f     ;
            w_req_buf_header1_f     <= (splitter_io_store_go &
                                        (splitter_io_msg_state_next == MSG_STATE_HEADER_1)) ? splitter_bridge_data    :
                                                                                              w_req_buf_header1_f     ;
            w_req_buf_header2_f     <= (splitter_io_store_go &
                                        (splitter_io_msg_state_next == MSG_STATE_HEADER_2)) ? splitter_bridge_data    :
                                                                                              w_req_buf_header2_f     ;
            w_req_buf_data0_f       <= (splitter_io_store_go &
                                        (splitter_io_msg_state_next == MSG_STATE_DATA))     ? splitter_bridge_data    :
                                                                                              w_req_buf_data0_f       ;
            w_addr_req_buf_status_f <= w_status_update                                      ? BUF_STATUS_COMP         :
                                       m_axi_aw_go                                          ? BUF_STATUS_INCOMP       :
                                                                                              w_addr_req_buf_status_f ;
            w_data_req_buf_status_f <= w_status_update                                      ? BUF_STATUS_COMP         :
                                       m_axi_w_go                                           ? BUF_STATUS_INCOMP       :
                                                                                              w_data_req_buf_status_f ;
        end
    end

    // Calculate Store Request Status
    assign w_req_buf_status =
        ((w_addr_req_buf_status_f == BUF_STATUS_INCOMP) &&
         (w_data_req_buf_status_f == BUF_STATUS_INCOMP)    ) ? BUF_STATUS_INCOMP :
                                                               BUF_STATUS_COMP   ;

//==============================================================================
// Forward Requests to AXI
//==============================================================================

    wire [`NOC_DATA_WIDTH-1:0]          paddings;
    reg  [`C_M_AXI_LITE_DATA_WIDTH-1:0] m_axi_wdata_tmp;

    assign paddings = 0;


    // Calculate Valid, Addr, Data signals
    always @ (*) begin
        // Write Address Channel
        m_axi_awvalid = (w_req_buf_status == BUF_STATUS_COMP) && (w_addr_resp_buf_status_f == BUF_STATUS_INCOMP);
        m_axi_awaddr = {paddings[`NOC_DATA_WIDTH-1:`PHY_ADDR_WIDTH], w_req_buf_header1_f[`MSG_ADDR_HI_:`MSG_ADDR_HI_-39]};

        // Write Data Channel
        m_axi_wvalid    = (w_req_buf_status == BUF_STATUS_COMP) && (w_data_resp_buf_status_f == BUF_STATUS_INCOMP);
        m_axi_wdata_tmp = w_req_buf_data0_f[`C_M_AXI_LITE_DATA_WIDTH-1:0];

        // Read Address Channel
        m_axi_arvalid = (r_req_buf_status_f == BUF_STATUS_COMP) && (r_resp_buf_status_f == BUF_STATUS_INCOMP);
        m_axi_araddr = {paddings[`NOC_DATA_WIDTH-1:`PHY_ADDR_WIDTH], r_req_buf_header1_f[`MSG_ADDR_HI_:`MSG_ADDR_HI_-39]};
    end

    // Calculate data size (which bytes are valid in our word)
    always @ (*) begin
        if (w_req_buf_header1_f[`MSG_DATA_SIZE_] == `MSG_DATA_SIZE_0B) begin
            m_axi_wstrb = 8'b00000000;
        end
        else if (w_req_buf_header1_f[`MSG_DATA_SIZE_] == `MSG_DATA_SIZE_1B) begin
            m_axi_wstrb = 8'b00000001;
        end
        else if (w_req_buf_header1_f[`MSG_DATA_SIZE_] == `MSG_DATA_SIZE_2B) begin
            m_axi_wstrb = 8'b00000011;
        end
        else if (w_req_buf_header1_f[`MSG_DATA_SIZE_] == `MSG_DATA_SIZE_4B) begin
            m_axi_wstrb = 8'b00001111;
        end
        else if (w_req_buf_header1_f[`MSG_DATA_SIZE_] == `MSG_DATA_SIZE_8B) begin
            m_axi_wstrb = 8'b11111111;
        end
        else begin
            m_axi_wstrb = 8'b11111111;
        end
    end

    generate
        if (SWAP_ENDIANESS) begin
            initial begin : p_endianess_check
              if (!(`C_M_AXI_LITE_DATA_WIDTH == 64 && `NOC_DATA_WIDTH == 64))
                  $fatal(1,"swapped endianess only works for 64bit NOC and AXI bus");
            end
            // this only works for 64bits
            // the byte enables are already generated correctly and need not be swapped
            assign m_axi_wdata[56 +: 8] = m_axi_wdata_tmp[ 0 +: 8];
            assign m_axi_wdata[48 +: 8] = m_axi_wdata_tmp[ 8 +: 8];
            assign m_axi_wdata[40 +: 8] = m_axi_wdata_tmp[16 +: 8];
            assign m_axi_wdata[32 +: 8] = m_axi_wdata_tmp[24 +: 8];
            assign m_axi_wdata[24 +: 8] = m_axi_wdata_tmp[32 +: 8];
            assign m_axi_wdata[16 +: 8] = m_axi_wdata_tmp[40 +: 8];
            assign m_axi_wdata[ 8 +: 8] = m_axi_wdata_tmp[48 +: 8];
            assign m_axi_wdata[ 0 +: 8] = m_axi_wdata_tmp[56 +: 8];
        end else begin
            assign m_axi_wdata = m_axi_wdata_tmp;
        end
    endgenerate

    assign m_axi_ar_go = m_axi_arvalid && m_axi_arready;
    assign m_axi_w_go  = m_axi_wvalid & m_axi_wready;
    assign m_axi_aw_go = m_axi_awvalid & m_axi_awready;

//==============================================================================
// Receive AXI Response and Create Piton Response
//==============================================================================

    // Set ready signals
    always @( * ) begin
        m_axi_rready = (r_resp_buf_status_f == BUF_STATUS_WAITRESP);
        m_axi_bready = (w_resp_buf_status == BUF_STATUS_WAITRESP);
    end

    // Create response header
    assign r_resp_buf_header0_next[`MSG_DST_CHIPID] = r_req_buf_header2_f[`MSG_SRC_CHIPID_];
    assign r_resp_buf_header0_next[`MSG_DST_X]      = r_req_buf_header2_f[`MSG_SRC_X_];
    assign r_resp_buf_header0_next[`MSG_DST_Y]      = r_req_buf_header2_f[`MSG_SRC_Y_];
    assign r_resp_buf_header0_next[`MSG_DST_FBITS]  = r_req_buf_header2_f[`MSG_SRC_FBITS_]; //TODO check this...
    assign r_resp_buf_header0_next[`MSG_LENGTH]     = `MSG_LENGTH_WIDTH'd8; //none loads always return 8 words // TODO
    assign r_resp_buf_header0_next[`MSG_TYPE]       = (r_req_buf_header0_f[`MSG_TYPE] == `MSG_TYPE_NC_LOAD_REQ) ? `MSG_TYPE_NC_LOAD_MEM_ACK :
                                                      (r_req_buf_header0_f[`MSG_TYPE] == `MSG_TYPE_LOAD_MEM) ? `MSG_TYPE_LOAD_MEM_ACK :
                                                      `MSG_TYPE_WIDTH'dx;
    assign r_resp_buf_header0_next[`MSG_MSHRID]     = r_req_buf_header0_f[`MSG_MSHRID];//TODO check this...
    assign r_resp_buf_header0_next[`MSG_OPTIONS_1]  = `MSG_OPTIONS_1_WIDTH'd0; //reserved bits

    assign w_resp_buf_header0_next[`MSG_DST_CHIPID] = w_req_buf_header2_f[`MSG_SRC_CHIPID_];
    assign w_resp_buf_header0_next[`MSG_DST_X]      = w_req_buf_header2_f[`MSG_SRC_X_];
    assign w_resp_buf_header0_next[`MSG_DST_Y]      = w_req_buf_header2_f[`MSG_SRC_Y_];
    assign w_resp_buf_header0_next[`MSG_DST_FBITS]  = w_req_buf_header2_f[`MSG_SRC_FBITS_]; //TODO check this...
    assign w_resp_buf_header0_next[`MSG_LENGTH]     = `MSG_LENGTH_WIDTH'd0;
    assign w_resp_buf_header0_next[`MSG_TYPE]       = (w_req_buf_header0_f[`MSG_TYPE] == `MSG_TYPE_NC_STORE_REQ) ? `MSG_TYPE_NC_STORE_MEM_ACK :
                                                      (w_req_buf_header0_f[`MSG_TYPE] == `MSG_TYPE_STORE_MEM) ? `MSG_TYPE_STORE_MEM_ACK :
                                                      `MSG_TYPE_WIDTH'dx;
    assign w_resp_buf_header0_next[`MSG_MSHRID]     = w_req_buf_header0_f[`MSG_MSHRID];//TODO check this...
    assign w_resp_buf_header0_next[`MSG_OPTIONS_1]  = `MSG_OPTIONS_1_WIDTH'd0; //reserved bits

    // Calculate whether we're ready to accept a response
    assign m_axi_b_go = m_axi_bready && m_axi_bvalid;
    assign m_axi_r_go = m_axi_rready && m_axi_rvalid;


    // Shift AXI read data over so that the desired data is at the lowest bits
    always @( * ) begin
        a_axi_rdata_shifted = (m_axi_rdata >> {m_axi_araddr[2:0], 3'b000});
    end

    `define PITON_FIXED_REQSIZE 1

    `ifndef PITON_FIXED_REQSIZE
        // Select and clone the desired bytes
        always @( * ) begin
            case (r_req_buf_header1_f[`MSG_DATA_SIZE_])
                `MSG_DATA_SIZE_0B: begin
                    a_axi_rdata_masked = {8{8'd0}};
                end
                `MSG_DATA_SIZE_1B: begin
                    a_axi_rdata_masked = {8{a_axi_rdata_shifted[7:0]}};
                end
                `MSG_DATA_SIZE_2B: begin
                    a_axi_rdata_masked = {4{a_axi_rdata_shifted[15:0]}};
                end
                `MSG_DATA_SIZE_4B: begin
                    a_axi_rdata_masked = {2{a_axi_rdata_shifted[31:0]}};
                end
                `MSG_DATA_SIZE_8B: begin
                    a_axi_rdata_masked = a_axi_rdata_shifted;
                end
                default: begin
                    a_axi_rdata_masked = a_axi_rdata_shifted;
                end
            endcase
        end
    `else

        reg  [`NOC_DATA_WIDTH-1:0]   a_axi_rdata_masked_tmp;

        generate
            if (SLAVE_RESP_BYTEWIDTH == 1) begin
                always @( * ) begin
                    a_axi_rdata_masked_tmp = {8{m_axi_rdata[7:0]}};
                end
            end else if (SLAVE_RESP_BYTEWIDTH == 2) begin
                always @( * ) begin
                    a_axi_rdata_masked_tmp = {4{m_axi_rdata[15:0]}};
                end
            end else if (SLAVE_RESP_BYTEWIDTH == 4) begin
                always @( * ) begin
                    a_axi_rdata_masked_tmp = {2{m_axi_rdata[31:0]}};
                end
            end else if (SLAVE_RESP_BYTEWIDTH == 8) begin
                always @( * ) begin
                    a_axi_rdata_masked_tmp = m_axi_rdata;
                end
            end else begin
                always @( * ) begin
                    a_axi_rdata_masked_tmp = m_axi_rdata;
                end
            end
        endgenerate

        generate
            if (SWAP_ENDIANESS) begin
                assign a_axi_rdata_masked[56 +: 8] = a_axi_rdata_masked_tmp[ 0 +: 8];
                assign a_axi_rdata_masked[48 +: 8] = a_axi_rdata_masked_tmp[ 8 +: 8];
                assign a_axi_rdata_masked[40 +: 8] = a_axi_rdata_masked_tmp[16 +: 8];
                assign a_axi_rdata_masked[32 +: 8] = a_axi_rdata_masked_tmp[24 +: 8];
                assign a_axi_rdata_masked[24 +: 8] = a_axi_rdata_masked_tmp[32 +: 8];
                assign a_axi_rdata_masked[16 +: 8] = a_axi_rdata_masked_tmp[40 +: 8];
                assign a_axi_rdata_masked[ 8 +: 8] = a_axi_rdata_masked_tmp[48 +: 8];
                assign a_axi_rdata_masked[ 0 +: 8] = a_axi_rdata_masked_tmp[56 +: 8];
            end else begin
                assign a_axi_rdata_masked = a_axi_rdata_masked_tmp;
            end
        endgenerate
    `endif


    //--------------------------------------------------------------------------
    // Create Store Response
    //--------------------------------------------------------------------------
    always @(posedge clk) begin
        if (rst) begin
            w_resp_buf_header0_f     <=  {`NOC_DATA_WIDTH{1'b0}};
            w_resp_buf_bresp_f       <=  {`C_M_AXI_LITE_RESP_WIDTH{1'b0}};
            w_addr_resp_buf_status_f <=  BUF_STATUS_INCOMP;
            w_data_resp_buf_status_f <=  BUF_STATUS_INCOMP;
        end
        else begin
            w_resp_buf_header0_f     <=  m_axi_aw_go              ? w_resp_buf_header0_next  :
                                                                    w_resp_buf_header0_f     ;
            w_resp_buf_bresp_f       <=  m_axi_b_go               ? m_axi_bresp              :
                                                                    w_resp_buf_bresp_f       ;
            w_addr_resp_buf_status_f <=  m_axi_aw_go              ? BUF_STATUS_WAITRESP      :
                                         m_axi_b_go               ? BUF_STATUS_RESPSEND      :
                                         io_splitter_ack_store_go ? BUF_STATUS_INCOMP        :
                                                                    w_addr_resp_buf_status_f ;
            w_data_resp_buf_status_f <=  m_axi_w_go               ? BUF_STATUS_WAITRESP      :
                                         m_axi_b_go               ? BUF_STATUS_RESPSEND      :
                                         io_splitter_ack_store_go ? BUF_STATUS_INCOMP        :
                                                                    w_data_resp_buf_status_f ;
        end
    end

    // Calculate Store Response Status
    assign w_resp_buf_status =
        ((w_addr_resp_buf_status_f == BUF_STATUS_INCOMP  ) ||
         (w_data_resp_buf_status_f == BUF_STATUS_INCOMP  )    ) ? BUF_STATUS_INCOMP   :
        ((w_addr_resp_buf_status_f == BUF_STATUS_COMP    ) ||
         (w_data_resp_buf_status_f == BUF_STATUS_COMP    )    ) ? BUF_STATUS_COMP     :
        ((w_addr_resp_buf_status_f == BUF_STATUS_WAITRESP) ||
         (w_data_resp_buf_status_f == BUF_STATUS_WAITRESP)    ) ? BUF_STATUS_WAITRESP :
                                                                  BUF_STATUS_RESPSEND ;

    //--------------------------------------------------------------------------
    // Create Load Response
    //--------------------------------------------------------------------------
    always @(posedge clk) begin
        if (rst) begin
            r_resp_buf_header0_f <= {`NOC_DATA_WIDTH{1'b0}};
            r_resp_buf_data0_f   <= {`C_M_AXI_LITE_DATA_WIDTH{1'b0}};
            r_resp_buf_rresp_f   <= {`C_M_AXI_LITE_RESP_WIDTH{1'b0}};
            r_resp_buf_status_f  <= BUF_STATUS_INCOMP;
        end
        else begin
            r_resp_buf_header0_f <= m_axi_ar_go                                        ? r_resp_buf_header0_next :
                                                                                         r_resp_buf_header0_f    ;
            r_resp_buf_data0_f   <= m_axi_r_go                                         ? a_axi_rdata_masked      :
                                                                                         r_resp_buf_data0_f      ;
            r_resp_buf_rresp_f   <= m_axi_r_go                                         ? m_axi_rresp             :
                                                                                         r_resp_buf_rresp_f      ;
            r_resp_buf_status_f  <= m_axi_ar_go                                        ? BUF_STATUS_WAITRESP     :
                                    m_axi_r_go                                         ? BUF_STATUS_RESPSEND     :
                                    (io_splitter_ack_load_go                       &
                                     (io_splitter_ack_load_counter_f == 0)         &
                                     ~(r_resp_buf_status_f == BUF_STATUS_WAITRESP)   ) ? BUF_STATUS_INCOMP       :
                                                                                         r_resp_buf_status_f     ;
        end
    end




//==============================================================================
// Send Piton Response Back to NOCs
//==============================================================================

    assign  r_resp_buf_val = (r_resp_buf_status_f == BUF_STATUS_RESPSEND);
    assign  w_resp_buf_val = (w_resp_buf_status == BUF_STATUS_RESPSEND);

    assign  io_splitter_ack_store = w_resp_buf_header0_f;
    assign  io_splitter_ack_load = (io_splitter_ack_load_counter_f == r_resp_buf_header0_f[`MSG_LENGTH]) ? r_resp_buf_header0_f
                                                       : r_resp_buf_data0_f;

    assign  io_splitter_ack_load_go = (io_splitter_ack_mux_sel == LOAD_ACK) && (r_resp_buf_val) && splitter_bridge_rdy;
    assign  io_splitter_ack_store_go = (io_splitter_ack_mux_sel == STORE_ACK) && (w_resp_buf_val) && splitter_bridge_rdy;

    always @( * ) begin
        // val flag and output to splitter
        if (io_splitter_ack_mux_sel == LOAD_ACK) begin
            bridge_splitter_val = r_resp_buf_val;
            bridge_splitter_data = io_splitter_ack_load;
        end
        else begin
            bridge_splitter_val = w_resp_buf_val;
            bridge_splitter_data = io_splitter_ack_store;
        end
    end

    // Select whether to send a load ACK or a store ACK
    always @( * ) begin
        if (r_resp_buf_val && (!w_resp_buf_val)) begin
            io_splitter_ack_mux_sel = LOAD_ACK;
        end
        else if (w_resp_buf_val && (!r_resp_buf_val)) begin
            io_splitter_ack_mux_sel = STORE_ACK;
        end
        else if (w_resp_buf_val && r_resp_buf_val) begin
            if(io_splitter_ack_load_counter_f == r_resp_buf_header0_f[`MSG_LENGTH]) begin
                io_splitter_ack_mux_sel = io_splitter_arb_f;
            end
            else begin
                io_splitter_ack_mux_sel = LOAD_ACK;
            end
        end
        else begin
            io_splitter_ack_mux_sel = LOAD_ACK;
        end
    end

    // Sequential updates to the arbitration selector and load flit counter
    always @(posedge clk) begin
        if (rst) begin
                io_splitter_arb_f <= 0;
                io_splitter_ack_load_counter_f <= 0;
        end
        else begin
            // Update Arbitration Reg
            if (w_resp_buf_val && r_resp_buf_val && io_splitter_ack_load_go) begin
                io_splitter_arb_f <= STORE_ACK;
            end
            else if (w_resp_buf_val && r_resp_buf_val && io_splitter_ack_store_go) begin
                io_splitter_arb_f <= LOAD_ACK;
            end

            // Update Load Flit Counter
            if (r_resp_buf_status_f == BUF_STATUS_WAITRESP) begin
                io_splitter_ack_load_counter_f <= r_resp_buf_header0_f[`MSG_LENGTH];
            end
            else if(io_splitter_ack_load_go) begin
                if (io_splitter_ack_load_counter_f != 0) begin
                    io_splitter_ack_load_counter_f <= io_splitter_ack_load_counter_f - 1;
                end
            end

        end
    end

    assign bridge_splitter_rdy =
        ((splitter_io_msg_type_next == MSG_TYPE_INVAL) ||
         (splitter_io_msg_is_load_next && (r_req_buf_status_f == BUF_STATUS_INCOMP)) ||
         (splitter_io_msg_is_store_next && (w_req_buf_status == BUF_STATUS_INCOMP)));


endmodule
