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
//  Filename      : piton_sd_define.vh
//  Created On    : 2017-03-15
//  Last Modified : 2018-11-21 22:12:24
//  Revision      :
//  Author        : Ang Li
//  Company       : Princeton University
//  Email         : angl@princeton.edu
//
//  Description   :
//==================================================================================================

// ------ Configurable Parameters ------ //
`define CACHE_ENTRY_WIDTH       3   // Need to re-configure BRAM in the SD cache if set larger than 3
`define CACHE_INDEX_WIDTH       1   // Must be smaller than CACHE_ENTRY_WIDTH

// ------ DO NOT TOUCH ------ //
`define PHY_ADDR_BITS           `PHY_ADDR_WIDTH-1:0

`define SD_ADDR_WIDTH           32
`define SD_BLOCK_OFFSET_WIDTH   9

`define PHY_BLOCK_BITS          `PHY_ADDR_WIDTH-1:`SD_BLOCK_OFFSET_WIDTH


`define CACHE_ENTRY_BITS        (`SD_BLOCK_OFFSET_WIDTH+`CACHE_ENTRY_WIDTH-1):`SD_BLOCK_OFFSET_WIDTH

`define CACHE_ENTRIES           (2 ** `CACHE_ENTRY_WIDTH)

`define CACHE_INDEXES           (2 ** `CACHE_INDEX_WIDTH)
`define CACHE_ENTRY_INDEXED_WIDTH   (`CACHE_ENTRY_WIDTH-`CACHE_INDEX_WIDTH)
`define CACHE_ENTRY_INDEXED_BITS    (`SD_BLOCK_OFFSET_WIDTH+`CACHE_ENTRY_WIDTH-1):(`SD_BLOCK_OFFSET_WIDTH+`CACHE_INDEX_WIDTH)
`define CACHE_ENTRIES_INDEXED   (2 ** `CACHE_ENTRY_INDEXED_WIDTH)
`define CACHE_INDEX_BITS        (`SD_BLOCK_OFFSET_WIDTH+`CACHE_INDEX_WIDTH-1):`SD_BLOCK_OFFSET_WIDTH
`define CACHE_BLOCK_PLACEMENT_BITS  `PHY_ADDR_WIDTH-1:(`SD_BLOCK_OFFSET_WIDTH+`CACHE_INDEX_WIDTH)

`define ADDR_LINE_BITS          (`CACHE_ENTRY_WIDTH+`SD_BLOCK_OFFSET_WIDTH-1):3

`define NOC_DATA_BITS           63:0
