/*
 *  Copyright 2023 CEA*
 *  *Commissariat a l'Energie Atomique et aux Energies Alternatives (CEA)
 *
 *  SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
 *
 *  Licensed under the Solderpad Hardware License v 2.1 (the “License”); you
 *  may not use this file except in compliance with the License, or, at your
 *  option, the Apache License version 2.0. You may obtain a copy of the
 *  License at
 *
 *  https://solderpad.org/licenses/SHL-2.1/
 *
 *  Unless required by applicable law or agreed to in writing, any work
 *  distributed under the License is distributed on an “AS IS” BASIS, WITHOUT
 *  WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
 *  License for the specific language governing permissions and limitations
 *  under the License.
 */
/*
 *  Authors       : Cesar Fuguet
 *  Creation Date : April, 2023
 *  Description   : Generic parameters package for the HPDcache. All parameters
 *                  can be overriden by Verilog preprocessor definitions.
 *  History       :
 */
`ifdef PITON_ARIANE
  `include "l15.tmp.h"
  `include "define.tmp.h"
`endif
package hpdcache_params_pkg;
    //  Definition of global constants for the HPDcache data and directory
    //  {{{
    `ifndef CONF_HPDCACHE_PA_WIDTH
        `define CONF_HPDCACHE_PA_WIDTH 49
    `endif
    localparam int unsigned PARAM_PA_WIDTH = `CONF_HPDCACHE_PA_WIDTH;

    //  HPDcache number of sets
    `ifndef CONF_HPDCACHE_SETS
        `define CONF_HPDCACHE_SETS 128
    `endif

    `ifdef PITON_ARIANE
        `ifndef CONFIG_L1D_SIZE
            localparam int unsigned PARAM_SETS = 128;
        `else 
            localparam int unsigned PARAM_SETS = (`CONFIG_L1D_SIZE/`CONFIG_L1D_ASSOCIATIVITY)/(`CONFIG_L1D_CACHELINE_WIDTH/8);
        `endif
    `else
        localparam int unsigned PARAM_SETS = `CONF_HPDCACHE_SETS;
    `endif

    //  HPDcache number of ways
    `ifndef CONF_HPDCACHE_WAYS
        `define CONF_HPDCACHE_WAYS 4
    `endif

    `ifdef PITON_ARIANE
        `ifndef CONFIG_L1D_ASSOCIATIVITY
            localparam int unsigned PARAM_WAYS = 4;
        `else
            localparam int unsigned PARAM_WAYS = `CONFIG_L1D_ASSOCIATIVITY; 
        `endif
    `else 
        localparam int unsigned PARAM_WAYS = `CONF_HPDCACHE_WAYS;
    `endif

    //  HPDcache word width (bits)
    `ifndef CONF_HPDCACHE_WORD_WIDTH
        `define CONF_HPDCACHE_WORD_WIDTH 64
    `endif
    localparam int unsigned PARAM_WORD_WIDTH = `CONF_HPDCACHE_WORD_WIDTH;

    //  HPDcache cache-line width (bits)
    `ifndef CONF_HPDCACHE_CL_WORDS
        `define CONF_HPDCACHE_CL_WORDS 8
    `endif

    `ifdef PITON_ARIANE
        localparam int unsigned PARAM_CL_WORDS = `CONFIG_L1D_CACHELINE_WIDTH/PARAM_WORD_WIDTH; //16 Bytes per cache-line harcoded
    `else
        localparam int unsigned PARAM_CL_WORDS = `CONF_HPDCACHE_CL_WORDS;
    `endif

    //  HPDcache number of words in the request data channels (request and response)
    `ifndef CONF_HPDCACHE_REQ_WORDS
        `define CONF_HPDCACHE_REQ_WORDS 1
    `endif
    localparam int unsigned PARAM_REQ_WORDS = `CONF_HPDCACHE_REQ_WORDS;

    //  HPDcache request transaction ID width (bits)
    `ifndef CONF_HPDCACHE_REQ_TRANS_ID_WIDTH
        `define CONF_HPDCACHE_REQ_TRANS_ID_WIDTH 7
    `endif
    localparam int unsigned PARAM_REQ_TRANS_ID_WIDTH = `CONF_HPDCACHE_REQ_TRANS_ID_WIDTH;

    //  HPDcache request source ID width (bits)
    `ifndef CONF_HPDCACHE_REQ_SRC_ID_WIDTH
        `define CONF_HPDCACHE_REQ_SRC_ID_WIDTH 3
    `endif
    localparam int unsigned PARAM_REQ_SRC_ID_WIDTH = `CONF_HPDCACHE_REQ_SRC_ID_WIDTH;

    //  HPDcache victim select
    `ifndef CONF_HPDCACHE_VICTIM_SEL
        `define CONF_HPDCACHE_VICTIM_SEL 1
    `endif
    localparam int unsigned PARAM_VICTIM_SEL = `CONF_HPDCACHE_VICTIM_SEL;
    //  }}}

    //  Definition of constants and types for HPDcache data memory
    //  {{{
    `ifndef CONF_HPDCACHE_DATA_WAYS_PER_RAM_WORD
        `define CONF_HPDCACHE_DATA_WAYS_PER_RAM_WORD 2
    `endif
    localparam int unsigned PARAM_DATA_WAYS_PER_RAM_WORD = `CONF_HPDCACHE_DATA_WAYS_PER_RAM_WORD;

    `ifndef CONF_HPDCACHE_DATA_SETS_PER_RAM
        `define CONF_HPDCACHE_DATA_SETS_PER_RAM PARAM_SETS
    `endif
    localparam int unsigned PARAM_DATA_SETS_PER_RAM = `CONF_HPDCACHE_DATA_SETS_PER_RAM;

    //  HPDcache DATA RAM macros implement write byte enable
    //  -  Write byte enable (1'b1)
    //  -  Write bit mask (1'b0)
    `ifndef CONF_HPDCACHE_DATA_RAM_WBYTEENABLE
        `define CONF_HPDCACHE_DATA_RAM_WBYTEENABLE 0
    `endif
    localparam bit PARAM_DATA_RAM_WBYTEENABLE = `CONF_HPDCACHE_DATA_RAM_WBYTEENABLE;

    //  Define the number of memory contiguous words that can be accessed
    //  simultaneously from the cache.
    //  -  This limits the maximum width for the data channel from requesters
    //  -  This impacts the refill latency (more ACCESS_WORDS -> less REFILL LATENCY)
    `ifndef CONF_HPDCACHE_ACCESS_WORDS
        `define CONF_HPDCACHE_ACCESS_WORDS 4
    `endif

    `ifdef PITON_ARIANE
        localparam int unsigned PARAM_ACCESS_WORDS = 2;
    `else
        localparam int unsigned PARAM_ACCESS_WORDS = `CONF_HPDCACHE_ACCESS_WORDS;
    `endif
    //  }}}

    //  Definition of constants and types for the Miss Status Holding Register (MSHR)
    //  {{{
    //  HPDcache MSHR number of sets
    `ifndef CONF_HPDCACHE_MSHR_SETS
        `define CONF_HPDCACHE_MSHR_SETS 64
    `endif

    `ifdef PITON_ARIANE
        localparam int unsigned PARAM_MSHR_SETS = 1;
    `else
        localparam int unsigned PARAM_MSHR_SETS = `CONF_HPDCACHE_MSHR_SETS;
    `endif

    //  HPDcache MSHR number of ways
    `ifndef CONF_HPDCACHE_MSHR_WAYS
        `define CONF_HPDCACHE_MSHR_WAYS 2
    `endif
    localparam int unsigned PARAM_MSHR_WAYS = `CONF_HPDCACHE_MSHR_WAYS;

    //  HPDcache MSHR number of ways in the same SRAM word
    `ifndef CONF_HPDCACHE_MSHR_WAYS_PER_RAM_WORD
        `define CONF_HPDCACHE_MSHR_WAYS_PER_RAM_WORD 2
    `endif
    localparam int unsigned PARAM_MSHR_WAYS_PER_RAM_WORD = `CONF_HPDCACHE_MSHR_WAYS_PER_RAM_WORD;

    //  HPDcache MSHR number of sets in the same SRAM
    `ifndef CONF_HPDCACHE_MSHR_SETS_PER_RAM
        `define CONF_HPDCACHE_MSHR_SETS_PER_RAM PARAM_MSHR_SETS
    `endif
    localparam int unsigned PARAM_MSHR_SETS_PER_RAM = `CONF_HPDCACHE_MSHR_SETS_PER_RAM;

    //  HPDcache MSHR macros implement write byte enable
    //  -  Write byte enable (1'b1)
    //  -  Write bit mask (1'b0)
    `ifndef CONF_HPDCACHE_MSHR_RAM_WBYTEENABLE
        `define CONF_HPDCACHE_MSHR_RAM_WBYTEENABLE 0
    `endif
    localparam bit PARAM_MSHR_RAM_WBYTEENABLE = `CONF_HPDCACHE_MSHR_RAM_WBYTEENABLE;
    
    //  HPDcache MSHR whether uses FFs or SRAM
    `ifndef CONF_HPDCACHE_MSHR_USE_REGBANK
        `define CONF_HPDCACHE_MSHR_USE_REGBANK 0
    `endif
    localparam bit PARAM_MSHR_USE_REGBANK = `CONF_HPDCACHE_MSHR_USE_REGBANK;

    //  HPDcache feedthrough FIFOs from the refill handler to the core
    `ifndef CONF_HPDCACHE_REFILL_CORE_RSP_FEEDTHROUGH
        `define CONF_HPDCACHE_REFILL_CORE_RSP_FEEDTHROUGH 1'b1
    `endif
    localparam bit PARAM_REFILL_CORE_RSP_FEEDTHROUGH = `CONF_HPDCACHE_REFILL_CORE_RSP_FEEDTHROUGH;

    //  HPDcache depth of the refill FIFO
    `ifndef CONF_HPDCACHE_REFILL_FIFO_DEPTH
        `define CONF_HPDCACHE_REFILL_FIFO_DEPTH 32'd2
    `endif
    
    `ifdef PITON_ARIANE
         /* FIXME: Should we increase it even more? */
        localparam int PARAM_REFILL_FIFO_DEPTH = (PARAM_MSHR_SETS*PARAM_MSHR_WAYS) + 32'd10;
    `else
        localparam int PARAM_REFILL_FIFO_DEPTH = `CONF_HPDCACHE_REFILL_FIFO_DEPTH
    `endif
    //  }}}

    //  Definition of constants and types for the Write Buffer (WBUF)
    //  {{{
    //  HPDcache Write-Buffer number of entries in the directory
    `ifndef CONF_HPDCACHE_WBUF_DIR_ENTRIES
        `define CONF_HPDCACHE_WBUF_DIR_ENTRIES 16
    `endif
    `ifdef PITON_ARIANE
        localparam int unsigned PARAM_WBUF_DIR_ENTRIES = 4;
    `else
        localparam int unsigned PARAM_WBUF_DIR_ENTRIES = `CONF_HPDCACHE_WBUF_DIR_ENTRIES;
    `endif

    //  HPDcache Write-Buffer number of entries in the data buffer
    `ifndef CONF_HPDCACHE_WBUF_DATA_ENTRIES
        `define CONF_HPDCACHE_WBUF_DATA_ENTRIES 4
    `endif
    localparam int unsigned PARAM_WBUF_DATA_ENTRIES = `CONF_HPDCACHE_WBUF_DATA_ENTRIES;

    //  HPDcache Write-Buffer number of words per entry
    `ifndef CONF_HPDCACHE_WBUF_WORDS
        `define CONF_HPDCACHE_WBUF_WORDS PARAM_REQ_WORDS
    `endif
    
    `ifdef PITON_ARIANE
        localparam int unsigned PARAM_WBUF_WORDS = 1;
    `else
        localparam int unsigned PARAM_WBUF_WORDS = `CONF_HPDCACHE_WBUF_WORDS;
    `endif

    //  HPDcache Write-Buffer threshold counter width (in bits)
    `ifndef CONF_HPDCACHE_WBUF_TIMECNT_WIDTH
        `define CONF_HPDCACHE_WBUF_TIMECNT_WIDTH 4
    `endif
    localparam int unsigned PARAM_WBUF_TIMECNT_WIDTH = `CONF_HPDCACHE_WBUF_TIMECNT_WIDTH;
    //  }}}

    //  HPDCACHE feedthrough FIFOs from the write-buffer to the NoC
    `ifndef CONF_HPDCACHE_WBUF_SEND_FEEDTHROUGH
        // Currently WBUF FIFOs don't support feedthrough
        `define CONF_HPDCACHE_WBUF_SEND_FEEDTHROUGH 1'b0
    `endif
    localparam bit PARAM_WBUF_SEND_FEEDTHROUGH = `CONF_HPDCACHE_WBUF_SEND_FEEDTHROUGH;

    //  Definition of constants and types for the Replay Table (RTAB)
    //  {{{
    `ifndef CONF_HPDCACHE_RTAB_ENTRIES
        `define CONF_HPDCACHE_RTAB_ENTRIES 8
    `endif
    localparam int PARAM_RTAB_ENTRIES = `CONF_HPDCACHE_RTAB_ENTRIES;
    //  }}}

endpackage
