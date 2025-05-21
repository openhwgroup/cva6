/**
 *  Copyright 2023,2024 CEA*
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
/**
 *  Author     : Cesar Fuguet
 *  Date       : October, 2024
 *  Description: HPDCACHE test global definitions
 */
#ifndef __HPDCACHE_TEST_DEFS_H__
#define __HPDCACHE_TEST_DEFS_H__

#include <systemc>

#define HPDCACHE_TEST_DEFS_LOG2(x) \
  (x <= 1 ? 0 : \
   x <= 2 ? 1 : \
   x <= 4 ? 2 : \
   x <= 8 ? 3 : \
   x <= 16 ? 4 : \
   x <= 32 ? 5 : \
   x <= 64 ? 6 : \
   x <= 128 ? 7 : \
   x <= 256 ? 8 : \
   x <= 512 ? 9 : \
   x <= 1024 ? 10 : \
   x <= 2048 ? 11 : \
   x <= 4096 ? 12 : \
   x <= 8192 ? 13 : \
   x <= 16384 ? 14 : 0)

#define SCOREBOARD_RAM_SIZE              (16 << 20) // Bytes

#ifndef CONF_HPDCACHE_WAYS
#define HPDCACHE_WAYS                    8
#else
#define HPDCACHE_WAYS                    (CONF_HPDCACHE_WAYS)
#endif

#ifndef CONF_HPDCACHE_SETS
#define HPDCACHE_SETS                    64
#else
#define HPDCACHE_SETS                    (CONF_HPDCACHE_SETS)
#endif

#ifndef CONF_HPDCACHE_CL_WORDS
#define HPDCACHE_CL_WORDS                8
#else
#define HPDCACHE_CL_WORDS                (CONF_HPDCACHE_CL_WORDS)
#endif

#ifndef CONF_HPDCACHE_WORD_WIDTH
#define HPDCACHE_WORD_WIDTH              64
#else
#define HPDCACHE_WORD_WIDTH              (CONF_HPDCACHE_WORD_WIDTH)
#endif

#ifndef CONF_HPDCACHE_MSHR_SETS
#define HPDCACHE_MSHR_SETS               1
#else
#define HPDCACHE_MSHR_SETS               (CONF_HPDCACHE_MSHR_SETS)
#endif

#ifndef CONF_HPDCACHE_MSHR_WAYS
#define HPDCACHE_MSHR_WAYS               8
#else
#define HPDCACHE_MSHR_WAYS               (CONF_HPDCACHE_MSHR_WAYS)
#endif

#ifndef CONF_HPDCACHE_PA_WIDTH
#define HPDCACHE_PA_WIDTH                49
#else
#define HPDCACHE_PA_WIDTH                (CONF_HPDCACHE_PA_WIDTH)
#endif

#ifndef CONF_HPDCACHE_REQ_WORDS
#define HPDCACHE_REQ_WORDS               1
#else
#define HPDCACHE_REQ_WORDS               (CONF_HPDCACHE_REQ_WORDS)
#endif

#define HPDCACHE_REQ_DATA_WIDTH          ((HPDCACHE_REQ_WORDS)*(HPDCACHE_WORD_WIDTH))

#ifndef CONF_HPDCACHE_MEM_DATA_WIDTH
#define HPDCACHE_MEM_DATA_WIDTH          512
#else
#define HPDCACHE_MEM_DATA_WIDTH          (CONF_HPDCACHE_MEM_DATA_WIDTH)
#endif

#ifndef CONF_HPDCACHE_MEM_ID_WIDTH
#define HPDCACHE_MEM_ID_WIDTH            4
#else
#define HPDCACHE_MEM_ID_WIDTH            (CONF_HPDCACHE_MEM_ID_WIDTH)
#endif

#ifndef CONF_HPDCACHE_WBUF_WORDS
#define HPDCACHE_WBUF_WORDS              2
#else
#define HPDCACHE_WBUF_WORDS              (CONF_HPDCACHE_WBUF_WORDS)
#endif

#ifndef CONF_HPDCACHE_WBUF_DIR_ENTRIES
#define HPDCACHE_WBUF_DIR_ENTRIES        8
#else
#define HPDCACHE_WBUF_DIR_ENTRIES        (CONF_HPDCACHE_WBUF_DIR_ENTRIES)
#endif

#ifndef CONF_HPDCACHE_WBUF_DATA_ENTRIES
#define HPDCACHE_WBUF_DATA_ENTRIES       4
#else
#define HPDCACHE_WBUF_DATA_ENTRIES       (CONF_HPDCACHE_WBUF_DATA_ENTRIES)
#endif

#ifndef CONF_HPDCACHE_REQ_SRC_ID_WIDTH
#define HPDCACHE_REQ_SRC_ID_WIDTH        3
#else
#define HPDCACHE_REQ_SRC_ID_WIDTH        (CONF_HPDCACHE_REQ_SRC_ID_WIDTH)
#endif

#ifndef CONF_HPDCACHE_REQ_TRANS_ID_WIDTH
#define HPDCACHE_REQ_TRANS_ID_WIDTH      6
#else
#define HPDCACHE_REQ_TRANS_ID_WIDTH      (CONF_HPDCACHE_REQ_TRANS_ID_WIDTH)
#endif

#define NREQUESTERS                      8

#define HPDCACHE_SET_WIDTH               HPDCACHE_TEST_DEFS_LOG2(HPDCACHE_SETS)
#define HPDCACHE_CL_OFFSET_WIDTH         HPDCACHE_TEST_DEFS_LOG2(((HPDCACHE_CL_WORDS)*(HPDCACHE_WORD_WIDTH))/8)
#define HPDCACHE_NLINE_WIDTH             ((HPDCACHE_PA_WIDTH) - (HPDCACHE_CL_OFFSET_WIDTH))
#define HPDCACHE_TAG_WIDTH               ((HPDCACHE_NLINE_WIDTH) - (HPDCACHE_SET_WIDTH))
#define HPDCACHE_ADDR_OFFSET_WIDTH       ((HPDCACHE_PA_WIDTH) - (HPDCACHE_TAG_WIDTH))

#define HPDCACHE_REQ_OP_WIDTH            5
#define HPDCACHE_REQ_SIZE_WIDTH          3
#define HPDCACHE_REQ_PMA_WIDTH           5
#define HPDCACHE_REQ_NEED_RSP_WIDTH      1
#define HPDCACHE_REQ_PHYS_INDEXED_WIDTH  1
#define HPDCACHE_RSP_ERROR_WIDTH         1
#define HPDCACHE_RSP_ABORTED_WIDTH       1

#define HPDCACHE_CORE_REQ_WIDTH          ((HPDCACHE_ADDR_OFFSET_WIDTH) + \
                                          (HPDCACHE_REQ_DATA_WIDTH) + \
                                          (HPDCACHE_REQ_OP_WIDTH) + \
                                          ((HPDCACHE_REQ_DATA_WIDTH)/8) + \
                                          (HPDCACHE_REQ_SIZE_WIDTH) + \
                                          (HPDCACHE_REQ_SRC_ID_WIDTH) + \
                                          (HPDCACHE_REQ_TRANS_ID_WIDTH) + \
                                          (HPDCACHE_REQ_NEED_RSP_WIDTH) + \
                                          (HPDCACHE_REQ_PHYS_INDEXED_WIDTH) + \
                                          (HPDCACHE_TAG_WIDTH) + \
                                          (HPDCACHE_REQ_PMA_WIDTH))

#define HPDCACHE_CORE_RSP_WIDTH          ((HPDCACHE_REQ_DATA_WIDTH) + \
                                          (HPDCACHE_REQ_SRC_ID_WIDTH) + \
                                          (HPDCACHE_REQ_TRANS_ID_WIDTH) + \
                                          (HPDCACHE_RSP_ERROR_WIDTH) + \
                                          (HPDCACHE_RSP_ABORTED_WIDTH))

#endif // __HPDCACHE_TEST_DEFS_H__
