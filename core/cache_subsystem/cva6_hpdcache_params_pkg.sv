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
 *  Description   : Package with parameters for the HPDcache in a CVA6 platform
 *  History       :
 */
package hpdcache_params_pkg;
    //  Imports from the CVA6 configuration package
    //  {{{
    import cva6_config_pkg::CVA6ConfigXlen;
    import cva6_config_pkg::CVA6ConfigDcacheByteSize;
    import cva6_config_pkg::CVA6ConfigDcacheSetAssoc;
    import cva6_config_pkg::CVA6ConfigDcacheLineWidth;
    import cva6_config_pkg::CVA6ConfigDcacheIdWidth;
    import cva6_config_pkg::CVA6ConfigWtDcacheWbufDepth;
    //  }}}

    //  Definition of constants used only in this file
    //  {{{
    localparam int unsigned __BYTES_PER_WAY =
        CVA6ConfigDcacheByteSize/CVA6ConfigDcacheSetAssoc;

    localparam int unsigned __BYTES_PER_CACHELINE =
        CVA6ConfigDcacheLineWidth/8;
    //  }}}

    //  Definition of global constants for the HPDcache data and directory
    //  {{{
    //  HPDcache physical address width (in bits)
    localparam int unsigned PARAM_PA_WIDTH = riscv::PLEN;

    //  HPDcache number of sets
    localparam int unsigned PARAM_SETS = __BYTES_PER_WAY/__BYTES_PER_CACHELINE;

    //  HPDcache number of ways
    localparam int unsigned PARAM_WAYS = CVA6ConfigDcacheSetAssoc;

    //  HPDcache word width (bits)
    localparam int unsigned PARAM_WORD_WIDTH = CVA6ConfigXlen;

    //  HPDcache cache-line width (bits)
    localparam int unsigned PARAM_CL_WORDS = CVA6ConfigDcacheLineWidth/PARAM_WORD_WIDTH;

    //  HPDcache number of words in the request data channels (request and response)
    `ifndef CONF_HPDCACHE_REQ_WORDS
        `define CONF_HPDCACHE_REQ_WORDS 1
    `endif
    localparam int unsigned PARAM_REQ_WORDS = `CONF_HPDCACHE_REQ_WORDS;

    //  HPDcache request transaction ID width (bits)
    localparam int unsigned PARAM_REQ_TRANS_ID_WIDTH = CVA6ConfigDcacheIdWidth;

    //  HPDcache request source ID width (bits)
    `ifndef CONF_HPDCACHE_REQ_SRC_ID_WIDTH
        `define CONF_HPDCACHE_REQ_SRC_ID_WIDTH 3
    `endif
    localparam int unsigned PARAM_REQ_SRC_ID_WIDTH = `CONF_HPDCACHE_REQ_SRC_ID_WIDTH;
    //  }}}

    //  Definition of constants and types for HPDcache data memory
    //  {{{
    `ifndef CONF_HPDCACHE_DATA_WAYS_PER_RAM_WORD
        `define CONF_HPDCACHE_DATA_WAYS_PER_RAM_WORD 128/PARAM_WORD_WIDTH
    `endif
    localparam int unsigned PARAM_DATA_WAYS_PER_RAM_WORD = `CONF_HPDCACHE_DATA_WAYS_PER_RAM_WORD;

    `ifndef CONF_HPDCACHE_DATA_SETS_PER_RAM
        `define CONF_HPDCACHE_DATA_SETS_PER_RAM PARAM_SETS
    `endif
    localparam int unsigned PARAM_DATA_SETS_PER_RAM = `CONF_HPDCACHE_DATA_SETS_PER_RAM;

    //  HPDcache DATA RAM implements write byte enable
    `ifndef CONF_HPDCACHE_DATA_RAM_WBYTEENABLE
        `define CONF_HPDCACHE_DATA_RAM_WBYTEENABLE 1'b0
    `endif
    localparam bit PARAM_DATA_RAM_WBYTEENABLE = `CONF_HPDCACHE_DATA_RAM_WBYTEENABLE;

    //  Define the number of memory contiguous words that can be accessed
    //  simultaneously from the cache.
    //  -  This limits the maximum width for the data channel from requesters
    //  -  This impacts the refill latency
    `ifndef CONF_HPDCACHE_ACCESS_WORDS
        `define CONF_HPDCACHE_ACCESS_WORDS PARAM_CL_WORDS/2
    `endif
    localparam int unsigned PARAM_ACCESS_WORDS = `CONF_HPDCACHE_ACCESS_WORDS;
    //  }}}

    //  Definition of constants and types for the Miss Status Holding Register (MSHR)
    //  {{{
    `ifndef CONF_HPDCACHE_MSHR_SETS
        `define CONF_HPDCACHE_MSHR_SETS 2
    `endif
    localparam int unsigned PARAM_MSHR_SETS = `CONF_HPDCACHE_MSHR_SETS;

    //  HPDcache MSHR number of ways
    `ifndef CONF_HPDCACHE_MSHR_WAYS
        `define CONF_HPDCACHE_MSHR_WAYS 4
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

    //  HPDcache MSHR implements write byte enable
    `ifndef CONF_HPDCACHE_MSHR_RAM_WBYTEENABLE
        `define CONF_HPDCACHE_MSHR_RAM_WBYTEENABLE 1'b0
    `endif
    localparam bit PARAM_MSHR_RAM_WBYTEENABLE = `CONF_HPDCACHE_MSHR_RAM_WBYTEENABLE;

    `ifndef CONF_HPDCACHE_MSHR_USE_REGBANK
        `define CONF_HPDCACHE_MSHR_USE_REGBANK 0
    `endif
    localparam bit PARAM_MSHR_USE_REGBANK = `CONF_HPDCACHE_MSHR_USE_REGBANK;
    //  }}}

    //  Definition of constants and types for the Write Buffer (WBUF)
    //  {{{
    `ifndef CONF_HPDCACHE_WBUF_DATA_ENTRIES
        `define __WBUF_DATA_ENTRIES_DESIRED (CVA6ConfigWtDcacheWbufDepth/2)
        `define __WBUF_DATA_ENTRIES_MAX     (CVA6ConfigWtDcacheWbufDepth)
        `define CONF_HPDCACHE_WBUF_DATA_ENTRIES \
              ((`__WBUF_DATA_ENTRIES_DESIRED) < 1 ? 1 : \
              ((`__WBUF_DATA_ENTRIES_DESIRED) < (`__WBUF_DATA_ENTRIES_MAX) ? \
               (`__WBUF_DATA_ENTRIES_DESIRED) : (`__WBUF_DATA_ENTRIES_MAX)))
    `endif
    localparam int unsigned PARAM_WBUF_DIR_ENTRIES = CVA6ConfigWtDcacheWbufDepth;
    localparam int unsigned PARAM_WBUF_DATA_ENTRIES = `CONF_HPDCACHE_WBUF_DATA_ENTRIES;

    `ifndef CONF_HPDCACHE_WBUF_WORDS
        `define CONF_HPDCACHE_WBUF_WORDS PARAM_REQ_WORDS
    `endif
    localparam int unsigned PARAM_WBUF_WORDS = `CONF_HPDCACHE_WBUF_WORDS;

    `ifndef CONF_HPDCACHE_WBUF_TIMECNT_WIDTH
        `define CONF_HPDCACHE_WBUF_TIMECNT_WIDTH 4
    `endif
    localparam int unsigned PARAM_WBUF_TIMECNT_WIDTH = `CONF_HPDCACHE_WBUF_TIMECNT_WIDTH;
    //  }}}

    //  Definition of constants and types for the Replay Table (RTAB)
    //  {{{
    `ifndef CONF_HPDCACHE_RTAB_ENTRIES
        `define CONF_HPDCACHE_RTAB_ENTRIES 4
    `endif
    localparam int PARAM_RTAB_ENTRIES = `CONF_HPDCACHE_RTAB_ENTRIES;
    //  }}}

endpackage
