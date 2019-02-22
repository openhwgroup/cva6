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
//  Filename      : piton_sd_cache_manager.v
//  Created On    : 2017-07-25
//  Last Modified : 2017-08-29 16:00:04
//  Revision      :
//  Author        : Ang Li
//  Company       : Princeton University
//  Email         : angl@princeton.edu
//
//  Description   : 
//==================================================================================================

`include "sd_defines.h"
`include "piton_sd_define.vh"

`timescale 1ns/1ps

module piton_sd_cache_manager (
    input  wire                         clk,
    input  wire                         rst,

    // interface with core
    input  wire                         lock_acquire,
    input  wire                         lock_release,
    output reg                          lock_status,

    input  wire                         core_cache_we,
    input  wire [`PHY_BLOCK_BITS]       core_cache_addr,
    output reg                          cache_core_rdy,
    output reg  [`CACHE_ENTRY_BITS]     cache_core_entry,

    // interface with transaction manager
    output wire [31:0]                  cache_tm_addr_sd,
    output wire [31:0]                  cache_tm_addr_dma,
    output reg                          cache_tm_wr,
    output reg                          cache_tm_val,
    input  wire                         tm_cache_rdy,

    input  wire                         tm_cache_ok,
    input  wire                         tm_cache_val,
    output reg                          cache_tm_rdy,

    input  wire                         is_hcxc
    );

    parameter   FLUSH_WAIT_TIME         =   24'hffffff;

    // cache states
    localparam  CACHE_IDLE              = 4'h0;
    localparam  CACHE_LOOKUP            = 4'h1;

    localparam  CACHE_WRITEBACK_ISSUE   = 4'h2;
    localparam  CACHE_WRITEBACK_WAIT    = 4'h3;
    localparam  CACHE_FILL_ISSUE        = 4'h4;
    localparam  CACHE_FILL_WAIT         = 4'h5;

    localparam  CACHE_UPDATE            = 4'h6;
    localparam  CACHE_LOCK              = 4'h7;

    localparam  CACHE_FLUSH_SCAN        = 4'h8;
    localparam  CACHE_FLUSH_ISSUE       = 4'h9;
    localparam  CACHE_FLUSH_WAIT        = 4'ha;
    localparam  CACHE_FLUSH_UPDATE      = 4'hb;

    // ------ Signals Declarations ------ //
    reg [3:0]   state;
    reg [3:0]   state_next;

    reg [1:0]   cache_tm_addr_sd_sel;   // 2'b0 for req, 2'b1 for wb, 2'b2 for flush
    reg         cache_tm_addr_dma_sel;  // 1'b0 for lkp, 1'b1 for query
    reg         cache_we;
    reg         cache_update_sel;       // 1'b0 for lkp, 1'b1 for flush

    reg                             core_cache_we_f;
    reg     [`PHY_BLOCK_BITS]       core_cache_addr_f;

    reg                             cache_hit_lkp;
    reg                             cache_dirty_lkp;
    reg     [`PHY_BLOCK_BITS]       cache_addr_lkp_f;
    reg     [`CACHE_ENTRY_BITS]     cache_entry_lkp_f;

    reg     [23:0]                  flush_timer;
    reg     [`CACHE_ENTRY_BITS]     cache_entry_scan;

    reg                             cache_dirty_query;
    reg     [`PHY_BLOCK_BITS]       cache_addr_query_f;
    reg     [`CACHE_ENTRY_BITS]     cache_entry_query_f;

    // ------ Static Logic ------ //
    wire    lock    =   lock_acquire    &   ~lock_status;
    wire    unlock  =   lock_release    &   lock_status;

    wire    tm_cache_go = cache_tm_rdy && tm_cache_val;
    wire    cache_tm_go = tm_cache_rdy && cache_tm_val;

    wire    [`CACHE_INDEX_BITS]     index_query =   cache_entry_scan[`CACHE_INDEX_BITS];

    wire    [31:0]  cache_tm_addr_dma_lkp           =
        {{(32 - `SD_BLOCK_OFFSET_WIDTH - `CACHE_ENTRY_WIDTH){1'b0}},
            cache_entry_lkp_f,
            {`SD_BLOCK_OFFSET_WIDTH{1'b0}}};

    wire    [31:0]  cache_tm_addr_dma_query         =
        {{(32 - `SD_BLOCK_OFFSET_WIDTH - `CACHE_ENTRY_WIDTH){1'b0}},
            cache_entry_query_f,
            {`SD_BLOCK_OFFSET_WIDTH{1'b0}}};

    wire    [31:0]  req_addr    =
        is_hcxc ? {{(`PHY_ADDR_WIDTH+`SD_BLOCK_OFFSET_WIDTH-32){1'b0}},
            core_cache_addr_f[`PHY_BLOCK_BITS]}
        : {core_cache_addr_f[31:`SD_BLOCK_OFFSET_WIDTH],
            {`SD_BLOCK_OFFSET_WIDTH{1'b0}}};

    wire    [31:0]  wb_addr     =
        is_hcxc ? {{(`PHY_ADDR_WIDTH+`SD_BLOCK_OFFSET_WIDTH-32){1'b0}},
            cache_addr_lkp_f[`PHY_BLOCK_BITS]}
        : {cache_addr_lkp_f[31:`SD_BLOCK_OFFSET_WIDTH],
            {`SD_BLOCK_OFFSET_WIDTH{1'b0}}};

    wire    [31:0]  flush_addr     =
        is_hcxc ? {{(`PHY_ADDR_WIDTH+`SD_BLOCK_OFFSET_WIDTH-32){1'b0}},
            cache_addr_query_f[`PHY_BLOCK_BITS]}
        : {cache_addr_query_f[31:`SD_BLOCK_OFFSET_WIDTH],
            {`SD_BLOCK_OFFSET_WIDTH{1'b0}}};

    assign  cache_tm_addr_dma   =
        cache_tm_addr_dma_sel   ?   cache_tm_addr_dma_query :   cache_tm_addr_dma_lkp;

    assign  cache_tm_addr_sd        =
        (cache_tm_addr_sd_sel       ==  2'h0)   ?   req_addr
        :   (cache_tm_addr_sd_sel   ==  2'h1)   ?   wb_addr
        :   (cache_tm_addr_sd_sel   ==  2'h2)   ?   flush_addr
        :                                           0;

    // ------ Sequential Logic ------ //
    always @(posedge clk or posedge rst) begin
        if (rst) begin
            state               <=  CACHE_IDLE;
            lock_status         <=  1'b0;
            core_cache_we_f     <=  1'b0;
            core_cache_addr_f   <=  0;
            flush_timer         <=  0;
            cache_entry_scan    <=  0;
            cache_addr_query_f  <=  0;
            cache_entry_query_f <=  0;
        end
        else begin
            state           <=  state_next;

            if (state       ==  CACHE_IDLE) begin
                flush_timer <=  flush_timer +   1;
            end
            else begin
                flush_timer <=  0;
            end

            if (state       ==  CACHE_UPDATE) begin
                cache_entry_scan    <=  cache_entry_lkp_f;
            end
            else if (state  ==  CACHE_FLUSH_SCAN) begin
                cache_entry_scan    <=  cache_entry_scan    +   1;
            end

            if (state       ==  CACHE_IDLE
                ||  state   ==  CACHE_FLUSH_SCAN) begin
                lock_status     <=  lock_acquire;
            end
            else if (state  ==  CACHE_LOCK) begin
                lock_status     <=  ~lock_release;
            end

            if ((state      ==  CACHE_IDLE 
                ||  state   ==  CACHE_FLUSH_SCAN) && lock) begin
                core_cache_we_f     <=  core_cache_we;
                core_cache_addr_f   <=  core_cache_addr;
            end

            if (state       ==  CACHE_FLUSH_SCAN) begin
                cache_entry_query_f <=  cache_entry_scan;
                cache_addr_query_f  <=  {addr_query_indexed[index_query],   index_query};
            end
        end
    end

    // ------ FSM Transition ------ //
    always @* begin //{{{
        state_next  =   state;

        case (state)
            CACHE_IDLE: begin
                if (lock) begin
                    state_next  =   CACHE_LOOKUP;
                end
                else if (flush_timer    ==  FLUSH_WAIT_TIME) begin
                    state_next  =   CACHE_FLUSH_SCAN;
                end
            end
            CACHE_LOOKUP: begin
                if (cache_hit_lkp) begin
                    state_next  =   CACHE_UPDATE;
                end
                else begin
                    if (cache_dirty_lkp) begin
                        state_next  =   CACHE_WRITEBACK_ISSUE;
                    end
                    else begin
                        state_next  =   CACHE_FILL_ISSUE;
                    end
                end
            end
            CACHE_WRITEBACK_ISSUE: begin
                if (cache_tm_go) begin
                    state_next      =   CACHE_WRITEBACK_WAIT;
                end
            end
            CACHE_WRITEBACK_WAIT: begin
                if (tm_cache_go) begin
                    if (tm_cache_ok) begin
                        state_next      =   CACHE_FILL_ISSUE;
                    end
                    else begin
                        state_next      =   CACHE_WRITEBACK_ISSUE;
                    end
                end
            end
            CACHE_FILL_ISSUE: begin
                if (cache_tm_go) begin
                    state_next      =   CACHE_FILL_WAIT;
                end
            end
            CACHE_FILL_WAIT: begin
                if (tm_cache_go) begin
                    if (tm_cache_ok) begin
                        state_next      =   CACHE_UPDATE;
                    end
                    else begin
                        state_next      =   CACHE_FILL_ISSUE;
                    end
                end
            end
            CACHE_UPDATE: begin
                state_next  =   CACHE_LOCK;
            end
            CACHE_LOCK: begin
                if (unlock) begin
                    state_next  =   CACHE_IDLE;
                end
            end
            CACHE_FLUSH_SCAN: begin
                if (lock) begin
                    state_next  =   CACHE_LOOKUP;
                end
                else if (cache_dirty_query) begin
                    state_next  =   CACHE_FLUSH_ISSUE;
                end
                else if (cache_entry_scan   ==  cache_entry_lkp_f - 1) begin
                    state_next  =   CACHE_IDLE;
                end
            end
            CACHE_FLUSH_ISSUE: begin
                if (cache_tm_go) begin
                    state_next      =   CACHE_FLUSH_WAIT;
                end
            end
            CACHE_FLUSH_WAIT: begin
                if (tm_cache_go) begin
                    if (tm_cache_ok) begin
                        state_next      =   CACHE_FLUSH_UPDATE;
                    end
                    else begin
                        state_next      =   CACHE_FLUSH_ISSUE;
                    end
                end
            end
            CACHE_FLUSH_UPDATE: begin
                if (cache_entry_scan    ==  cache_entry_lkp_f) begin
                    state_next  =   CACHE_IDLE;
                end
                else begin
                    state_next  =   CACHE_FLUSH_SCAN;
                end
            end
        endcase
    end //}}}

    // ------ FSM Output ------ //
    always @* begin
        cache_core_rdy          =   1'b0;
        cache_core_entry        =   cache_entry_lkp_f;
        cache_tm_wr             =   1'b0;
        cache_tm_val            =   1'b0;
        cache_tm_rdy            =   1'b0;
        cache_tm_addr_sd_sel    =   2'h0;
        cache_tm_addr_dma_sel   =   1'b0;
        cache_we                =   1'b0;
        cache_update_sel        =   1'b0;

        case (state)
            CACHE_WRITEBACK_ISSUE:  begin
                cache_tm_val            =   1'b1;
                cache_tm_wr             =   1'b1;
                cache_tm_addr_sd_sel    =   2'h1;
                cache_tm_addr_dma_sel   =   1'b0;
            end
            CACHE_FILL_ISSUE:   begin
                cache_tm_val            =   1'b1;
                cache_tm_wr             =   1'b0;
                cache_tm_addr_sd_sel    =   2'h0;
                cache_tm_addr_dma_sel   =   1'b0;
            end
            CACHE_FLUSH_ISSUE:  begin
                cache_tm_val            =   1'b1;
                cache_tm_wr             =   1'b1;
                cache_tm_addr_sd_sel    =   2'h2;
                cache_tm_addr_dma_sel   =   1'b1;
            end
            CACHE_WRITEBACK_WAIT,
            CACHE_FILL_WAIT,
            CACHE_FLUSH_WAIT:    begin
                cache_tm_rdy        =   1'b1;
            end
            CACHE_UPDATE:   begin
                cache_core_rdy      =   1'b1;
                cache_we            =   1'b1;
            end
            CACHE_LOCK: begin
                cache_core_rdy      =   1'b1;
            end
            CACHE_FLUSH_UPDATE: begin
                cache_we            =   1'b1;
                cache_update_sel    =   1'b1;
            end
        endcase
    end

    // ------ Sub-module Instantiation ------ //

    wire    [`CACHE_INDEX_BITS]             index_lkp   =   core_cache_addr_f[`CACHE_INDEX_BITS];
    wire    [`CACHE_BLOCK_PLACEMENT_BITS]   tag_lkp     =   core_cache_addr_f[`CACHE_BLOCK_PLACEMENT_BITS];

    wire    [`CACHE_INDEXES-1:0]            hit_lkp_indexed;
    wire    [`CACHE_ENTRY_INDEXED_BITS]     entry_lkp_indexed   [`CACHE_INDEXES-1:0];
    wire    [`CACHE_INDEXES-1:0]            dirty_lkp_indexed;
    wire    [`CACHE_BLOCK_PLACEMENT_BITS]   addr_lkp_indexed    [`CACHE_INDEXES-1:0];

    reg     [`CACHE_BLOCK_PLACEMENT_BITS]   addr_lkp_indexed_f  [`CACHE_INDEXES-1:0];
    reg     [`CACHE_ENTRY_INDEXED_BITS]     entry_lkp_indexed_f [`CACHE_INDEXES-1:0];

    wire    [`CACHE_INDEXES-1:0]            dirty_query_indexed;
    wire    [`CACHE_BLOCK_PLACEMENT_BITS]   addr_query_indexed  [`CACHE_INDEXES-1:0];

    wire    [`CACHE_ENTRY_BITS]     update_entry
        =   cache_update_sel ?   cache_entry_query_f :   cache_entry_lkp_f;
    wire    [`CACHE_BLOCK_PLACEMENT_BITS]   update_addr
        =   cache_update_sel ?   cache_addr_query_f[`CACHE_BLOCK_PLACEMENT_BITS]  :   tag_lkp;
    wire    update_dirty
        =   cache_update_sel ?   1'b0    :   core_cache_we_f;

    genvar i;
    generate for (i = 0; i < `CACHE_INDEXES; i = i + 1) begin : index_block
        piton_sd_cache_tag index(
            .clk                    (clk),
            .rst                    (rst),
            .addr_i                 (tag_lkp),

            .hit_lkp                (hit_lkp_indexed[i]),
            .entry_lkp              (entry_lkp_indexed[i]),
            .dirty_lkp              (dirty_lkp_indexed[i]),
            .addr_lkp               (addr_lkp_indexed[i]),

            .we                     (cache_we && update_entry[`CACHE_INDEX_BITS] == i),
            .addr_w                 (update_addr),
            .entry_w                (update_entry[`CACHE_ENTRY_INDEXED_BITS]),
            .dirty_w                (update_dirty),

            .entry_query            (cache_entry_scan[`CACHE_ENTRY_INDEXED_BITS]),
            .dirty_query            (dirty_query_indexed[i]),
            .addr_query             (addr_query_indexed[i])
            );

        always @(posedge clk) begin
            addr_lkp_indexed_f[i]   <=  addr_lkp_indexed[i];
            entry_lkp_indexed_f[i]  <=  entry_lkp_indexed[i];
        end

    end endgenerate

    always @* begin
        cache_hit_lkp       =   hit_lkp_indexed[index_lkp];
        cache_dirty_lkp     =   dirty_lkp_indexed[index_lkp];
        cache_addr_lkp_f    =   {addr_lkp_indexed_f[index_lkp], index_lkp};
        cache_entry_lkp_f   =   {entry_lkp_indexed_f[index_lkp], index_lkp};

        cache_dirty_query   =   dirty_query_indexed[index_query];
    end

endmodule
