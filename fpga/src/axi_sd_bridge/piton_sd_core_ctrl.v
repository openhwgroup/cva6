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
//  Filename      : piton_sd_core_ctrl.v
//  Created On    : 2017-07-17
//  Last Modified : 2017-09-15 15:59:25
//  Revision      :
//  Author        : Ang Li
//  Company       : Princeton University
//  Email         : angl@princeton.edu
//
//  Description   : 
//==================================================================================================

`include "sd_defines.h"
`include "piton_sd_define.vh"

module piton_sd_core_ctrl (
    // Clock + Reset
    input  wire                         clk,
    input  wire                         rst,

    // NOC interface
    input  wire                         splitter_bridge_val,
    input  wire [`NOC_DATA_BITS]        splitter_bridge_data,
    output reg                          bridge_splitter_rdy,

    output reg                          bridge_splitter_val,
    output reg  [`NOC_DATA_BITS]        bridge_splitter_data,
    input  wire                         splitter_bridge_rdy,

    // Buffer
    output reg  [31:0]                  core_buffer_addr,
    output reg                          core_buffer_ce,
    output reg                          core_buffer_wr,
    output reg  [1:0]                   core_buffer_sz,
    input  wire [`NOC_DATA_BITS]        buffer_core_data,
    output reg  [`NOC_DATA_BITS]        core_buffer_data,

    // Cache Manager
    output reg                          cache_lock_acquire,
    output reg                          cache_lock_release,
    input  wire                         cache_lock_status,

    output reg                          core_cache_we,
    output reg  [`PHY_BLOCK_BITS]       core_cache_addr,
    input  wire                         cache_core_rdy,
    input  wire [`CACHE_ENTRY_BITS]     cache_core_entry
    );

    // ------ Local Parameters ------ //
    // NOC states
    localparam  NOC_RST                 = 4'hf;
    localparam  NOC_IDLE                = 4'h0;

    localparam  NOC_IN_HEADER_1         = 4'h1;
    localparam  NOC_IN_HEADER_2         = 4'h2;
    localparam  NOC_IN_DATA             = 4'h3;

    localparam  NOC_WAITING             = 4'h4;
    localparam  NOC_THROWING            = 4'h5;

    localparam  NOC_OUT_HEADER          = 4'h6;
    localparam  NOC_OUT_DATA            = 4'h7;

    // ------ Signals Declarations ------ //
    reg [3:0]   state;
    reg [3:0]   state_next;

    reg [7:0]   counter;
    reg         counter_en;
    reg         counter_rst;

    reg [2:0]   offset;
    reg         offset_en;
    reg         offset_rst;

    reg [7:0]                   msg_data_val;
    reg [`NOC_DATA_BITS]        msg_data_buf    [7:0];

    reg                         cache_re_f;
    reg [2:0]                   offset_f;

    reg [`MSG_TYPE]             type;
    reg [`MSG_LENGTH]           payload;
    reg [`MSG_MSHRID]           mshr;
    reg [`PHY_ADDR_BITS]        addr;
    reg [`MSG_DATA_SIZE_]       data_sz;
    reg [`MSG_SRC_CHIPID_]      chipid;
    reg [`MSG_SRC_X_]           srcx;
    reg [`MSG_SRC_Y_]           srcy;

    // ------ Static Logic ------ //
    wire    splitter_bridge_go  =   bridge_splitter_rdy && splitter_bridge_val;
    wire    bridge_splitter_go  =   splitter_bridge_rdy && bridge_splitter_val;

    wire    store       =   (type == `MSG_TYPE_STORE_REQ) ||
                            (type == `MSG_TYPE_STORE_MEM);
    wire    ncstore     =   (type == `MSG_TYPE_NC_STORE_REQ);
    wire    wr          =   store || ncstore;
    wire    load        =   (type == `MSG_TYPE_LOAD_REQ) ||
                            (type == `MSG_TYPE_LOAD_MEM);
    wire    ncload      =   (type == `MSG_TYPE_NC_LOAD_REQ);
    wire    rd          =   load || ncload;

    `ifndef SDCTRL_TEST
    // Now we have a bug. Always return 64 bytes when read.
        wire    [7:0]   resp_payload    =   wr  ? 8'd0 : 8'd8;
    `else /* `ifndef SDCTRL_TEST */
        wire    [7:0]   resp_payload = wr       ? 8'd0
            : (data_sz == `MSG_DATA_SIZE_1B)    ? 8'd1
            : (data_sz == `MSG_DATA_SIZE_2B)    ? 8'd1
            : (data_sz == `MSG_DATA_SIZE_4B)    ? 8'd1
            : (data_sz == `MSG_DATA_SIZE_8B)    ? 8'd1
            : (data_sz == `MSG_DATA_SIZE_16B)   ? 8'd2
            : (data_sz == `MSG_DATA_SIZE_32B)   ? 8'd4
            : (data_sz == `MSG_DATA_SIZE_64B)   ? 8'd8
            :                                     8'd0;
    `endif /* `ifndef SDCTRL_TEST */

    wire    [2:0]   actual_resp_payload_mask    =   wr  ?   3'h0
        : (data_sz  ==  `MSG_DATA_SIZE_1B)              ?   3'h0
        : (data_sz  ==  `MSG_DATA_SIZE_2B)              ?   3'h0
        : (data_sz  ==  `MSG_DATA_SIZE_4B)              ?   3'h0
        : (data_sz  ==  `MSG_DATA_SIZE_8B)              ?   3'h0
        : (data_sz  ==  `MSG_DATA_SIZE_16B)             ?   3'h1
        : (data_sz  ==  `MSG_DATA_SIZE_32B)             ?   3'h3
        : (data_sz  ==  `MSG_DATA_SIZE_64B)             ?   3'h7
        :                                                   3'h0;

    wire    [7:0]   resp_msg_type   = store   ? `MSG_TYPE_STORE_MEM_ACK
                                    : ncstore ? `MSG_TYPE_NC_STORE_MEM_ACK
                                    : load    ? `MSG_TYPE_LOAD_MEM_ACK
                                    : ncload  ? `MSG_TYPE_NC_LOAD_MEM_ACK
                                    :           `MSG_TYPE_ERROR;

    `ifndef SDCTRL_TEST
        wire    [3:0]   resp_fbits  =   4'h0;
    `else /* `ifndef SDCTRL_TEST */
        wire    [3:0]   resp_fbits  =   4'ha;
    `endif /* `ifndef SDCTRL_TEST */

    wire    [`NOC_DATA_BITS]    resp_header =
        {chipid, srcx, srcy, resp_fbits,
            resp_payload,   resp_msg_type,  mshr,   6'h0};

    wire    [`PHY_ADDR_BITS]    addr_remapped   =
        (splitter_bridge_data[51:44] ==  8'hff)   ?
        {12'h0, splitter_bridge_data[43:16]}    :
        {4'h0, splitter_bridge_data[51:16]};

    // ------ Sequential Logic ------ //
    always @(posedge clk or posedge rst) begin
        if (rst) begin
            state               <=  NOC_RST;
            counter             <=  0;
            offset              <=  0;
            type                <=  0;
            payload             <=  0;
            mshr                <=  0;
            addr                <=  0;
            data_sz             <=  0;
            chipid              <=  0;
            srcx                <=  0;
            srcy                <=  0;
            
            msg_data_val        <=  0;
            msg_data_buf[0]     <=  0;
            msg_data_buf[1]     <=  0;
            msg_data_buf[2]     <=  0;
            msg_data_buf[3]     <=  0;
            msg_data_buf[4]     <=  0;
            msg_data_buf[5]     <=  0;
            msg_data_buf[6]     <=  0;
            msg_data_buf[7]     <=  0;
        end
        else begin
            state   <=  state_next;

            if (counter_rst) begin
                counter <=  0;
            end
            else if (counter_en) begin
                counter <=  counter + 1;
            end

            if (offset_rst) begin
                offset <=  0;
            end
            else if (offset_en) begin
                offset <=  offset + 1;
            end

            if (state   ==  NOC_IDLE && splitter_bridge_go) begin
                type    <=  splitter_bridge_data[`MSG_TYPE];
                payload <=  splitter_bridge_data[`MSG_LENGTH];
                mshr    <=  splitter_bridge_data[`MSG_MSHRID];
            end

            if (state   ==  NOC_IN_HEADER_1 && splitter_bridge_go && (rd || wr)) begin
                addr    <=  addr_remapped;
                data_sz <=  splitter_bridge_data[`MSG_DATA_SIZE_];
            end

            if (state   ==  NOC_IN_HEADER_2 && splitter_bridge_go) begin
                chipid  <=  splitter_bridge_data[`MSG_SRC_CHIPID_];
                srcx    <=  splitter_bridge_data[`MSG_SRC_X_];
                srcy    <=  splitter_bridge_data[`MSG_SRC_Y_];
            end

            if (state   ==  NOC_IN_DATA && splitter_bridge_go) begin
                msg_data_val[counter[2:0]]  <=  1'b1;
                msg_data_buf[counter[2:0]]  <=  splitter_bridge_data;
            end
            else if (cache_re_f) begin
                msg_data_val[offset_f]      <=  1'b1;
                msg_data_buf[offset_f]      <=  buffer_core_data;
            end
            else if (state  ==  NOC_IDLE) begin
                msg_data_val                <=  0;
            end
        end
    end

    // ------ FSM Transitions ------ //
    always @* begin
        state_next  =   state;

        case    (state)
            NOC_RST: begin
                state_next  =   NOC_IDLE;
            end
            NOC_IDLE: begin
                if (splitter_bridge_go) begin
                    state_next  =   NOC_IN_HEADER_1;
                    // Do not know if it's a valid MSG yet.
                end
            end
            NOC_IN_HEADER_1: begin
                // Check if it's a valid LOAD/STORE request.
                if (rd || wr) begin
                    if (splitter_bridge_go) begin
                        state_next  =   NOC_IN_HEADER_2;
                    end
                end
                else begin
                    if (payload == 8'd0) begin
                        state_next  =   NOC_IDLE;
                    end
                    else begin
                        state_next  =   NOC_THROWING;
                    end
                end
            end
            NOC_IN_HEADER_2: begin
                if (splitter_bridge_go) begin
                    if (wr) begin
                        state_next  =   NOC_IN_DATA;
                    end
                    else begin
                        if (cache_lock_status && cache_core_rdy) begin
                            state_next  =   NOC_OUT_HEADER;
                        end
                        else begin
                            state_next  =   NOC_WAITING;
                        end
                    end
                end
            end
            NOC_IN_DATA: begin
                if (splitter_bridge_go && counter == payload - 3) begin
                    state_next  =   NOC_WAITING;
                end
            end
            NOC_WAITING: begin
                if (cache_lock_status && cache_core_rdy) begin
                    if ((wr  &&   offset  ==  payload - 3)  ||  rd) begin
                        state_next  =   NOC_OUT_HEADER;
                    end
                end
            end
            NOC_THROWING: begin
                if (splitter_bridge_go && counter == payload - 1) begin
                    state_next  =   NOC_IDLE;
                end
            end
            NOC_OUT_HEADER: begin
                if (bridge_splitter_go) begin
                    if (resp_payload    ==  0) begin
                        state_next  =   NOC_IDLE;
                    end
                    else begin
                        state_next  =   NOC_OUT_DATA;
                    end
                end
            end
            NOC_OUT_DATA: begin
                if (bridge_splitter_go && counter == resp_payload - 1) begin
                    state_next  =   NOC_IDLE;
                end
            end
        endcase
    end

    always @* begin
        bridge_splitter_rdy     =   1'b0;
        bridge_splitter_val     =   1'b0;
        bridge_splitter_data    =   0;
        core_cache_we           =   wr;
        core_cache_addr         =   addr[`PHY_BLOCK_BITS];
        counter_en              =   1'b0;
        counter_rst             =   1'b0;

        case    (state)
            NOC_IDLE: begin
                bridge_splitter_rdy =   1'b1;
                counter_rst         =   1'b1;
            end
            NOC_IN_HEADER_1: begin
                bridge_splitter_rdy =   rd || wr;
                counter_rst         =   1'b1;
                core_cache_addr     =   addr_remapped[`PHY_BLOCK_BITS];
            end
            NOC_IN_HEADER_2: begin
                bridge_splitter_rdy =   1'b1;
                counter_rst         =   1'b1;
            end
            NOC_IN_DATA: begin
                bridge_splitter_rdy =   1'b1;
                counter_en          =   splitter_bridge_go;
            end
            NOC_WAITING: begin
                counter_rst         =   1'b1;
            end
            NOC_THROWING: begin
                bridge_splitter_rdy =   1'b1;
                counter_en          =   splitter_bridge_go;
            end
            NOC_OUT_HEADER: begin
                bridge_splitter_val     =   1'b1;
                counter_rst             =   1'b1;
                bridge_splitter_data    =   resp_header;
            end
            NOC_OUT_DATA: begin
                bridge_splitter_val     =   msg_data_val[counter[2:0] & actual_resp_payload_mask];
                bridge_splitter_data    =   msg_data_buf[counter[2:0] & actual_resp_payload_mask];
                counter_en              =   bridge_splitter_go;
            end
        endcase
    end

    // ------ Cache & Buffer ------ //
    localparam  CB_IDLE         =   3'h0;
    localparam  CB_BUFFER2CACHE =   3'h1;
    localparam  CB_CACHE2BUFFER =   3'h2;
    localparam  CB_UNLOCK       =   3'h3;

    reg     [2:0]   cb_state;
    reg     [2:0]   cb_state_next;

    always @(posedge clk or posedge rst) begin
        if (rst) begin
            cb_state    <=  CB_IDLE;
            cache_re_f  <=  1'b0;
            offset_f    <=  0;
        end
        else begin
            cb_state    <=  cb_state_next;
            cache_re_f  <=  core_buffer_ce &&  ~core_buffer_wr;
            offset_f    <=  offset;
        end
    end

    always @* begin
        cb_state_next   =   cb_state;

        case (cb_state)
            CB_IDLE:    begin
                if (cache_lock_acquire) begin
                    if (wr) begin
                        cb_state_next   =   CB_BUFFER2CACHE;
                    end
                    else begin
                        cb_state_next   =   CB_CACHE2BUFFER;
                    end
                end
            end
            CB_BUFFER2CACHE:    begin
                if (offset  ==  payload - 3 && core_buffer_ce) begin
                    cb_state_next   =   CB_UNLOCK;
                end
            end
            CB_CACHE2BUFFER:    begin
                if (offset  ==  actual_resp_payload_mask && core_buffer_ce) begin
                    cb_state_next   =   CB_UNLOCK;
                end
            end
            CB_UNLOCK:  begin
                if (cache_lock_release    &&  ~cache_lock_status) begin
                    cb_state_next   =   CB_IDLE;
                end
            end
        endcase
    end

    always @* begin
        core_buffer_ce          =   1'b0;
        core_buffer_wr          =   1'b0;
        core_buffer_data        =   0;
        cache_lock_acquire      =   1'b0;
        cache_lock_release      =   1'b0;
        offset_en               =   1'b0;
        offset_rst              =   1'b0;

        case (cb_state)
            CB_IDLE:    begin
                cache_lock_acquire  =   (state  ==  NOC_IN_HEADER_1)    &&  splitter_bridge_go;
                offset_rst          =   1'b1;
            end
            CB_BUFFER2CACHE:    begin
                cache_lock_acquire  =   ~cache_lock_status;
                if (cache_lock_status   &&  cache_core_rdy) begin
                    core_buffer_ce      =   msg_data_val[offset];
                    core_buffer_wr      =   1'b1;
                    core_buffer_data    =   msg_data_buf[offset];
                    offset_en           =   msg_data_val[offset];
                end
            end
            CB_CACHE2BUFFER:    begin
                cache_lock_acquire  =   ~cache_lock_status;
                if (cache_lock_status   &&  cache_core_rdy) begin
                    core_buffer_ce      =   1'b1;
                    core_buffer_wr      =   1'b0;
                    offset_en           =   1'b1;
                end
            end
            CB_UNLOCK:  begin
                cache_lock_release  =   1'b1;
            end
        endcase
    end

    always @* begin
        core_buffer_addr    =   
            {{(32 - `SD_BLOCK_OFFSET_WIDTH - `CACHE_ENTRY_WIDTH){1'b0}},
                cache_core_entry, addr[`SD_BLOCK_OFFSET_WIDTH-1:0]};

        case (data_sz)
            `MSG_DATA_SIZE_1B: begin
                core_buffer_sz          =   2'd0;
            end
            `MSG_DATA_SIZE_2B: begin
                core_buffer_sz          =   2'd1;
                core_buffer_addr[0]     =   1'b0;
            end
            `MSG_DATA_SIZE_4B: begin
                core_buffer_sz          =   2'd2;
                core_buffer_addr[1:0]   =   2'b0;
            end
            `MSG_DATA_SIZE_8B: begin
                core_buffer_sz          =   2'd3;
                core_buffer_addr[2:0]   =   3'b0;
            end
            `MSG_DATA_SIZE_16B: begin
                core_buffer_sz          =   2'd3;
                core_buffer_addr[3:0]   =   {offset[0],         3'b0};
            end
            `MSG_DATA_SIZE_32B: begin
                core_buffer_sz          =   2'd3;
                core_buffer_addr[4:0]   =   {offset[1:0],       3'b0};
            end
            `MSG_DATA_SIZE_64B: begin
                core_buffer_sz          =   2'd3;
                core_buffer_addr[5:0]   =   {offset[2:0],       3'b0};
            end
            default: begin
                core_buffer_sz          =   2'd3;
                core_buffer_addr[5:0]   =   {offset[2:0],       3'b0};
            end
        endcase
    end

endmodule
