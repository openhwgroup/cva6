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
//  Filename      : piton_sd_cache_tag.v
//  Created On    : 2017-08-29
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

module piton_sd_cache_tag (
    input  wire                                     clk,
    input  wire                                     rst,

    // lookup interface
    input  wire [`CACHE_BLOCK_PLACEMENT_BITS]       addr_i,

    // lookup interface
    output reg                                      hit_lkp,
    output reg  [`CACHE_ENTRY_INDEXED_BITS]         entry_lkp,
    output reg                                      dirty_lkp,
    output reg  [`CACHE_BLOCK_PLACEMENT_BITS]       addr_lkp,

    // write interface
    input  wire                                     we,
    input  wire [`CACHE_BLOCK_PLACEMENT_BITS]       addr_w,
    input  wire [`CACHE_ENTRY_INDEXED_BITS]         entry_w,
    input  wire                                     dirty_w,

    // query interface
    input  wire [`CACHE_ENTRY_INDEXED_BITS]         entry_query,
    output reg                                      dirty_query,
    output reg  [`CACHE_BLOCK_PLACEMENT_BITS]       addr_query
    );

    reg     [`CACHE_BLOCK_PLACEMENT_BITS]       cached_addr     [`CACHE_ENTRIES_INDEXED-1:0];
    reg     [`CACHE_ENTRIES_INDEXED-1:0]        cache_valid;
    reg     [`CACHE_ENTRIES_INDEXED-1:0]        cache_dirty;
    reg     [`CACHE_ENTRY_INDEXED_BITS]         cache_lru       [`CACHE_ENTRIES_INDEXED-1:0];

    wire    [`CACHE_ENTRIES_INDEXED-1:0]        cache_hit;

    integer j,  k,  l;
    always @* begin
        entry_lkp   =   0;
        // any hit?
        if (|cache_hit) begin
            for (j = 0; j < `CACHE_ENTRIES_INDEXED; j = j + 1) begin
                if (cache_hit[j]) begin
                    entry_lkp   =   j;
                end
            end
        end
        // any invalid slot?
        else if (|(~cache_valid)) begin
            for (k = 0; k < `CACHE_ENTRIES_INDEXED; k = k + 1) begin
                if (~cache_valid[k]) begin
                    entry_lkp   =   k;
                end
            end
        end
        // lru slot
        else begin
            for (l = 0; l < `CACHE_ENTRIES_INDEXED; l = l + 1) begin
                if (cache_lru[l] == 0) begin
                    entry_lkp   =   l;
                end
            end
        end

        hit_lkp     =   |cache_hit;
        addr_lkp    =   cached_addr[entry_lkp];
        dirty_lkp   =   cache_dirty[entry_lkp]  &   cache_valid[entry_lkp];

        dirty_query =   cache_valid[entry_query] &  cache_dirty[entry_query];
        addr_query  =   cached_addr[entry_query];
    end

    genvar  i;
    generate    for (i = 0; i < `CACHE_ENTRIES_INDEXED; i = i + 1) begin: entry_block
        assign  cache_hit[i]    =   cache_valid[i]  && cached_addr[i]   ==  addr_i;

        always @(posedge clk or posedge rst) begin
            if (rst) begin
                cached_addr[i]  <=  0;
                cache_valid[i]  <=  1'b0;
                cache_dirty[i]  <=  1'b0;
                cache_lru[i]    <=  0;
            end
            else begin
                if (we) begin
                    if (entry_w == i) begin
                        // updating me!
                        cached_addr[i]  <=  addr_w;
                        cache_valid[i]  <=  1'b1;
                        cache_dirty[i]  <=  dirty_w;
                        cache_lru[i]    <=  `CACHE_ENTRIES_INDEXED-1;
                    end
                    else begin
                        // updating someone else
                        if (cache_lru[i] > cache_lru[entry_w]) begin
                            cache_lru[i]    <=  cache_lru[i] - 1;
                        end
                    end
                end
            end
        end
    end endgenerate

endmodule
