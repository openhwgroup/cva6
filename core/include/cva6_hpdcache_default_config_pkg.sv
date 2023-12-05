// Copyright 2023 Commissariat a l'Energie Atomique et aux Energies
//                Alternatives (CEA)
//
// Licensed under the Solderpad Hardware License, Version 2.1 (the “License”);
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Authors: Cesar Fuguet
// Date: February, 2023
// Description:
//   Default package with parameters for the HPDcache in a CVA6 platform.
//   Users can copy this file, rename it, and adapt the configuration values as
//   needed.

package hpdcache_params_pkg;
  //  Imports from the CVA6 configuration package
  //  {{{
  import cva6_config_pkg::CVA6ConfigXlen;
  import cva6_config_pkg::CVA6ConfigDcacheByteSize;
  import cva6_config_pkg::CVA6ConfigDcacheSetAssoc;
  import cva6_config_pkg::CVA6ConfigDcacheLineWidth;
  import cva6_config_pkg::CVA6ConfigDcacheIdWidth;
  import cva6_config_pkg::CVA6ConfigWtDcacheWbufDepth;
  import cva6_config_pkg::CVA6ConfigNrLoadBufEntries;
  //  }}}

  //  Definition of constants used only in this file
  //  {{{
  localparam int unsigned __BYTES_PER_WAY = CVA6ConfigDcacheByteSize / CVA6ConfigDcacheSetAssoc;

  localparam int unsigned __BYTES_PER_CACHELINE = CVA6ConfigDcacheLineWidth / 8;
  //  }}}

  //  Definition of global constants for the HPDcache data and directory
  //  {{{
  //  HPDcache physical address width (in bits)
  localparam int unsigned PARAM_PA_WIDTH = riscv::PLEN;

  //  HPDcache number of sets
  localparam int unsigned PARAM_SETS = __BYTES_PER_WAY / __BYTES_PER_CACHELINE;

  //  HPDcache number of ways
  localparam int unsigned PARAM_WAYS = CVA6ConfigDcacheSetAssoc;

  //  HPDcache word width (bits)
  localparam int unsigned PARAM_WORD_WIDTH = CVA6ConfigXlen;

  //  HPDcache cache-line width (bits)
  localparam int unsigned PARAM_CL_WORDS = CVA6ConfigDcacheLineWidth / PARAM_WORD_WIDTH;

  //  HPDcache number of words in the request data channels (request and response)
  localparam int unsigned PARAM_REQ_WORDS = 1;

  //  HPDcache request transaction ID width (bits)
  localparam int unsigned PARAM_REQ_TRANS_ID_WIDTH = CVA6ConfigDcacheIdWidth;

  //  HPDcache request source ID width (bits)
  localparam int unsigned PARAM_REQ_SRC_ID_WIDTH = 3;
  //  }}}

  //  Definition of constants and types for HPDcache data memory
  //  {{{
  localparam int unsigned PARAM_DATA_WAYS_PER_RAM_WORD = 128 / PARAM_WORD_WIDTH;
  localparam int unsigned PARAM_DATA_SETS_PER_RAM = PARAM_SETS;

  //  HPDcache DATA RAM macros whether implements:
  //  -  Write byte enable (1'b1)
  //  -  Write bit mask (1'b0)
  localparam bit PARAM_DATA_RAM_WBYTEENABLE = 1'b1;

  //  Define the number of memory contiguous words that can be accessed
  //  simultaneously from the cache.
  //  -  This limits the maximum width for the data channel from requesters
  //  -  This impacts the refill latency (more ACCESS_WORDS -> less REFILL LATENCY)
  localparam int unsigned PARAM_ACCESS_WORDS = PARAM_CL_WORDS / 2;
  //  }}}

  //  Definition of constants and types for the Miss Status Holding Register (MSHR)
  //  {{{
  //  HPDcache MSHR number of sets
  localparam int unsigned PARAM_MSHR_SETS = 2;

  //  HPDcache MSHR number of ways
  localparam int unsigned PARAM_MSHR_WAYS = (CVA6ConfigNrLoadBufEntries > 4) ? 4 : 2;

  //  HPDcache MSHR number of ways in the same SRAM word
  localparam int unsigned PARAM_MSHR_WAYS_PER_RAM_WORD = (PARAM_MSHR_WAYS > 1) ? 2 : 1;

  //  HPDcache MSHR number of sets in the same SRAM
  localparam int unsigned PARAM_MSHR_SETS_PER_RAM = PARAM_MSHR_SETS;

  //  HPDcache MSHR RAM whether implements:
  //  -  Write byte enable (1'b1)
  //  -  Write bit mask (1'b0)
  localparam bit PARAM_MSHR_RAM_WBYTEENABLE = 1'b1;

  //  HPDcache MSHR whether uses FFs or SRAM
  localparam bit PARAM_MSHR_USE_REGBANK = (PARAM_MSHR_SETS * PARAM_MSHR_WAYS) <= 16;
  localparam bit PARAM_REFILL_CORE_RSP_FEEDTHROUGH = 1'b1;
  //  }}}

  //  Definition of constants and types for the Write Buffer (WBUF)
  //  {{{
  //  HPDcache Write-Buffer number of entries in the directory
  localparam int unsigned PARAM_WBUF_DIR_ENTRIES = CVA6ConfigWtDcacheWbufDepth;

  //  HPDcache Write-Buffer number of entries in the data buffer
  localparam int unsigned PARAM_WBUF_DATA_ENTRIES = CVA6ConfigWtDcacheWbufDepth;

  //  HPDcache Write-Buffer number of words per entry
  localparam int unsigned PARAM_WBUF_WORDS = PARAM_REQ_WORDS;

  //  HPDcache Write-Buffer threshold counter width (in bits)
  localparam int unsigned PARAM_WBUF_TIMECNT_WIDTH = 3;
  localparam bit PARAM_WBUF_SEND_FEEDTHROUGH = 1'b0;
  //  }}}

  //  Definition of constants and types for the Replay Table (RTAB)
  //  {{{
  localparam int PARAM_RTAB_ENTRIES = 4;
  //  }}}
endpackage
