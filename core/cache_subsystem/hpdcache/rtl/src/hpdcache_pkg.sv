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
 *  Creation Date : April, 2021
 *  Description   : Write-Through (WT), High-Throughput (HTPUT) HPDcache Package
 *  History       :
 */
package hpdcache_pkg;
    //  Utility definitions
    //  {{{
    typedef logic unsigned [7:0]  hpdcache_uint8;
    typedef logic signed   [7:0]  hpdcache_int8;
    typedef logic unsigned [31:0] hpdcache_uint32;
    typedef logic signed   [31:0] hpdcache_int32;
    typedef logic unsigned [63:0] hpdcache_uint64;
    typedef logic signed   [63:0] hpdcache_int64;
    typedef hpdcache_uint32       hpdcache_uint;
    typedef hpdcache_int32        hpdcache_int;
    //  }}}

    //  Definition of constants and types for HPDcache directory memory
    //  {{{
    //      Victim selection policy
    typedef enum logic {
        HPDCACHE_VICTIM_RANDOM = 1'b0,
        HPDCACHE_VICTIM_PLRU   = 1'b1
    } hpdcache_victim_sel_policy_t;
    //  }}}

    //  Definition of interface with requesters
    //  {{{
    typedef logic [2:0] hpdcache_req_size_t;

    //      Definition of operation codes
    //      {{{
    typedef enum logic [4:0] {
        HPDCACHE_REQ_LOAD                  = 5'h00,
        HPDCACHE_REQ_STORE                 = 5'h01,
        // RESERVED                        = 5'h02,
        // RESERVED                        = 5'h03,
        HPDCACHE_REQ_AMO_LR                = 5'h04,
        HPDCACHE_REQ_AMO_SC                = 5'h05,
        HPDCACHE_REQ_AMO_SWAP              = 5'h06,
        HPDCACHE_REQ_AMO_ADD               = 5'h07,
        HPDCACHE_REQ_AMO_AND               = 5'h08,
        HPDCACHE_REQ_AMO_OR                = 5'h09,
        HPDCACHE_REQ_AMO_XOR               = 5'h0a,
        HPDCACHE_REQ_AMO_MAX               = 5'h0b,
        HPDCACHE_REQ_AMO_MAXU              = 5'h0c,
        HPDCACHE_REQ_AMO_MIN               = 5'h0d,
        HPDCACHE_REQ_AMO_MINU              = 5'h0e,
        // RESERVED                        = 5'h0f,
        HPDCACHE_REQ_CMO_FENCE             = 5'h10,
        HPDCACHE_REQ_CMO_PREFETCH          = 5'h11,
        HPDCACHE_REQ_CMO_INVAL_NLINE       = 5'h12,
        HPDCACHE_REQ_CMO_INVAL_ALL         = 5'h13,
        HPDCACHE_REQ_CMO_FLUSH_NLINE       = 5'h14,
        HPDCACHE_REQ_CMO_FLUSH_ALL         = 5'h15,
        HPDCACHE_REQ_CMO_FLUSH_INVAL_NLINE = 5'h16,
        HPDCACHE_REQ_CMO_FLUSH_INVAL_ALL   = 5'h17
    } hpdcache_req_op_t;
    //      }}}

    //      Definition of Write Policy Hint
    //      {{{
    typedef enum logic[2:0] {
        HPDCACHE_WR_POLICY_AUTO = 3'b001,
        HPDCACHE_WR_POLICY_WB   = 3'b010,
        HPDCACHE_WR_POLICY_WT   = 3'b100
    } hpdcache_wr_policy_hint_t;
    //      }}}

    //      Definition of PMA flags
    //      {{{
    typedef struct packed
    {
        logic uncacheable;
        logic io; //  FIXME: for future use

        //  Write Policy Hint
        hpdcache_wr_policy_hint_t wr_policy_hint;
    } hpdcache_pma_t;
    //      }}}

    //      Definition of functions
    //      {{{
    function automatic int unsigned hpdcache_max(int unsigned x, int unsigned y);
        return (x < y) ? y : x;
    endfunction

    function automatic int unsigned hpdcache_min(int unsigned x, int unsigned y);
        return (x < y) ? x : y;
    endfunction

    function automatic logic is_load(input hpdcache_req_op_t op);
        case (op)
            HPDCACHE_REQ_LOAD: return 1'b1;
            default:           return 1'b0;
        endcase
    endfunction

    function automatic logic is_store(input hpdcache_req_op_t op);
        case (op)
            HPDCACHE_REQ_STORE: return 1'b1;
            default:            return 1'b0;
        endcase
    endfunction

    function automatic logic is_amo(input hpdcache_req_op_t op);
        case (op)
            HPDCACHE_REQ_AMO_LR,
            HPDCACHE_REQ_AMO_SC,
            HPDCACHE_REQ_AMO_SWAP,
            HPDCACHE_REQ_AMO_ADD,
            HPDCACHE_REQ_AMO_AND,
            HPDCACHE_REQ_AMO_OR,
            HPDCACHE_REQ_AMO_XOR,
            HPDCACHE_REQ_AMO_MAX,
            HPDCACHE_REQ_AMO_MAXU,
            HPDCACHE_REQ_AMO_MIN,
            HPDCACHE_REQ_AMO_MINU:
                return 1'b1;
            default:
                return 1'b0;
        endcase
    endfunction

    function automatic logic is_amo_lr(input hpdcache_req_op_t op);
        case (op)
            HPDCACHE_REQ_AMO_LR: return 1'b1;
            default:             return 1'b0;
        endcase
    endfunction

    function automatic logic is_amo_sc(input hpdcache_req_op_t op);
        case (op)
            HPDCACHE_REQ_AMO_SC: return 1'b1;
            default:             return 1'b0;
        endcase
    endfunction

    function automatic logic is_amo_swap(input hpdcache_req_op_t op);
        case (op)
            HPDCACHE_REQ_AMO_SWAP: return 1'b1;
            default:               return 1'b0;
        endcase
    endfunction

    function automatic logic is_amo_add(input hpdcache_req_op_t op);
        case (op)
            HPDCACHE_REQ_AMO_ADD: return 1'b1;
            default:              return 1'b0;
        endcase
    endfunction

    function automatic logic is_amo_and(input hpdcache_req_op_t op);
        case (op)
            HPDCACHE_REQ_AMO_AND: return 1'b1;
            default:              return 1'b0;
        endcase
    endfunction

    function automatic logic is_amo_or(input hpdcache_req_op_t op);
        case (op)
            HPDCACHE_REQ_AMO_OR:  return 1'b1;
            default:              return 1'b0;
        endcase
    endfunction

    function automatic logic is_amo_xor(input hpdcache_req_op_t op);
        case (op)
            HPDCACHE_REQ_AMO_XOR: return 1'b1;
            default:              return 1'b0;
        endcase
    endfunction

    function automatic logic is_amo_max(input hpdcache_req_op_t op);
        case (op)
            HPDCACHE_REQ_AMO_MAX: return 1'b1;
            default:              return 1'b0;
        endcase
    endfunction

    function automatic logic is_amo_maxu(input hpdcache_req_op_t op);
        case (op)
            HPDCACHE_REQ_AMO_MAXU: return 1'b1;
            default:               return 1'b0;
        endcase
    endfunction

    function automatic logic is_amo_min(input hpdcache_req_op_t op);
        case (op)
            HPDCACHE_REQ_AMO_MIN: return 1'b1;
            default:              return 1'b0;
        endcase
    endfunction

    function automatic logic is_amo_minu(input hpdcache_req_op_t op);
        case (op)
            HPDCACHE_REQ_AMO_MINU: return 1'b1;
            default:               return 1'b0;
        endcase
    endfunction

    function automatic logic is_cmo_inval(input hpdcache_req_op_t op);
        return (op inside {HPDCACHE_REQ_CMO_INVAL_NLINE, HPDCACHE_REQ_CMO_INVAL_ALL});
    endfunction

    function automatic logic is_cmo_flush(input hpdcache_req_op_t op);
        return (op inside {HPDCACHE_REQ_CMO_FLUSH_NLINE,
                           HPDCACHE_REQ_CMO_FLUSH_ALL,
                           HPDCACHE_REQ_CMO_FLUSH_INVAL_NLINE,
                           HPDCACHE_REQ_CMO_FLUSH_INVAL_ALL});
    endfunction

    function automatic logic is_cmo_fence(input hpdcache_req_op_t op);
        return (op == HPDCACHE_REQ_CMO_FENCE);
    endfunction

    function automatic logic is_cmo_prefetch(input hpdcache_req_op_t op);
        return (op == HPDCACHE_REQ_CMO_PREFETCH);
    endfunction

    function automatic logic is_cmo_inval_by_nline(input hpdcache_req_op_t op);
        return (op == HPDCACHE_REQ_CMO_INVAL_NLINE);
    endfunction

    function automatic logic is_cmo_inval_all(input hpdcache_req_op_t op);
        return (op == HPDCACHE_REQ_CMO_INVAL_ALL);
    endfunction

    function automatic logic is_cmo_flush_by_nline(input hpdcache_req_op_t op);
        return (op == HPDCACHE_REQ_CMO_FLUSH_NLINE);
    endfunction

    function automatic logic is_cmo_flush_all(input hpdcache_req_op_t op);
        return (op == HPDCACHE_REQ_CMO_FLUSH_ALL);
    endfunction

    function automatic logic is_cmo_flush_inval_by_nline(input hpdcache_req_op_t op);
        return (op == HPDCACHE_REQ_CMO_FLUSH_INVAL_NLINE);
    endfunction

    function automatic logic is_cmo_flush_inval_all(input hpdcache_req_op_t op);
        return (op == HPDCACHE_REQ_CMO_FLUSH_INVAL_ALL);
    endfunction

    function automatic logic is_cmo(input hpdcache_req_op_t op);
        return (is_cmo_flush(op) ||
                is_cmo_fence(op) ||
                is_cmo_inval(op) ||
                is_cmo_prefetch(op));
    endfunction

    //      }}}
    //  }}}

    //  Definition of interface with memory
    //  {{{
    typedef logic [7:0]                           hpdcache_mem_len_t;
    typedef logic [2:0]                           hpdcache_mem_size_t;

    typedef enum logic [1:0] {
        HPDCACHE_MEM_RESP_OK  = 2'b00,
        HPDCACHE_MEM_RESP_NOK = 2'b01
    } hpdcache_mem_error_e;

    typedef enum logic [1:0] {
        HPDCACHE_MEM_READ     = 2'b00,
        HPDCACHE_MEM_WRITE    = 2'b01,
        HPDCACHE_MEM_ATOMIC   = 2'b10
        //  Reserved        = 2'b11 - TODO: CMO ?
    } hpdcache_mem_command_e;

    typedef enum logic [3:0] {
        HPDCACHE_MEM_ATOMIC_ADD  = 4'b0000,
        HPDCACHE_MEM_ATOMIC_CLR  = 4'b0001,
        HPDCACHE_MEM_ATOMIC_SET  = 4'b0010,
        HPDCACHE_MEM_ATOMIC_EOR  = 4'b0011,
        HPDCACHE_MEM_ATOMIC_SMAX = 4'b0100,
        HPDCACHE_MEM_ATOMIC_SMIN = 4'b0101,
        HPDCACHE_MEM_ATOMIC_UMAX = 4'b0110,
        HPDCACHE_MEM_ATOMIC_UMIN = 4'b0111,
        HPDCACHE_MEM_ATOMIC_SWAP = 4'b1000,
        //  Reserved           = 4'b1001,
        //  Reserved           = 4'b1010,
        //  Reserved           = 4'b1011,
        HPDCACHE_MEM_ATOMIC_LDEX = 4'b1100,
        HPDCACHE_MEM_ATOMIC_STEX = 4'b1101
        //  Reserved           = 4'b1110,
        //  Reserved           = 4'b1111
    } hpdcache_mem_atomic_e;

    function automatic hpdcache_mem_size_t get_hpdcache_mem_size(int unsigned bytes);
        if      (bytes ==   0) return 0;
        else if (bytes <=   2) return 1;
        else if (bytes <=   4) return 2;
        else if (bytes <=   8) return 3;
        else if (bytes <=  16) return 4;
        else if (bytes <=  32) return 5;
        else if (bytes <=  64) return 6;
        else if (bytes <= 128) return 7;
        else begin
`ifndef HPDCACHE_ASSERT_OFF
            assert (1) $error("hpdcache: unsupported number of bytes");
`endif
            return 0;
        end
    endfunction
    //  }}}

    //  Definition of constants and types for the uncacheable request handler (UC)
    //  {{{
    typedef struct packed {
        logic is_ld;
        logic is_st;
        logic is_amo_lr;
        logic is_amo_sc;
        logic is_amo_swap;
        logic is_amo_add;
        logic is_amo_and;
        logic is_amo_or;
        logic is_amo_xor;
        logic is_amo_max;
        logic is_amo_maxu;
        logic is_amo_min;
        logic is_amo_minu;
    } hpdcache_uc_op_t;
    //  }}}

    //  Definition of constants and types for the CMO request handler (CMOH)
    //  {{{
    typedef struct packed {
        logic is_flush_inval_by_nline;
        logic is_flush_inval_all;
        logic is_flush_by_nline;
        logic is_flush_all;
        logic is_inval_by_nline;
        logic is_inval_all;
        logic is_fence;
    } hpdcache_cmoh_op_t;
    //  }}}

    //  Definition Replay Table (RTAB) dependencies
    //  {{{
    typedef struct packed {
        logic mshr_hit;
        logic mshr_full;
        logic mshr_ready;
        logic write_miss;
        logic wbuf_hit;
        logic wbuf_not_ready;
        logic dir_unavailable;
        logic dir_fetch;
        logic flush_hit;
        logic flush_not_ready;
    } hpdcache_rtab_deps_t;
    //  }}}

    //  Definition of parameters
    //  {{{
    typedef struct packed {
        //  Number of requesters
        int unsigned nRequesters;
        //  Physical Address Width
        int unsigned paWidth;
        //  Word width (bits)
        int unsigned wordWidth;
        //  Number of sets
        int unsigned sets;
        //  Number of ways
        int unsigned ways;
        //  Cache-Line width (bits)
        int unsigned clWords;
        //  Number of words in the request data channels (request and response)
        int unsigned reqWords;
        //  Request transaction ID width (bits)
        int unsigned reqTransIdWidth;
        //  Request source ID width (bits)
        int unsigned reqSrcIdWidth;
        //  Victim select
        hpdcache_victim_sel_policy_t victimSel;
        //  Number of ways per RAM entry
        int unsigned dataWaysPerRamWord;
        //  Number of sets per RAM
        int unsigned dataSetsPerRam;
        //  DATA RAM macros implement write byte enable
        //  -  Write byte enable (1'b1)
        //  -  Write bit mask (1'b0)
        bit dataRamByteEnable;
        //  Define the number of memory contiguous words that can be accessed
        //  simultaneously from the cache.
        //  -  This limits the maximum width for the data channel from requesters
        //  -  This impacts the refill latency (more ACCESS_WORDS -> less REFILL LATENCY)
        int unsigned accessWords;
        //  MSHR number of sets
        int unsigned mshrSets;
        //  MSHR number of ways
        int unsigned mshrWays;
        //  MSHR number of ways in the same SRAM word (entry)
        int unsigned mshrWaysPerRamWord;
        //  MSHR number of sets in the same SRAM
        int unsigned mshrSetsPerRam;
        //  MSHR macros implement write byte enable
        //  -  Write byte enable (1'b1)
        //  -  Write bit mask (1'b0)
        bit mshrRamByteEnable;
        //  MSHR uses whether FFs or SRAM
        bit mshrUseRegbank;
        //  Use feedthrough FIFOs from the refill handler to the core
        bit refillCoreRspFeedthrough;
        //  Depth of the refill FIFO
        int refillFifoDepth;
        //  Write-Buffer number of entries in the directory
        int unsigned wbufDirEntries;
        //  Write-Buffer number of entries in the data buffer
        int unsigned wbufDataEntries;
        //  Write-Buffer number of words per entry
        int unsigned wbufWords;
        //  Write-Buffer threshold counter width (in bits)
        int unsigned wbufTimecntWidth;
        //  Number of entries in the replay table
        int unsigned rtabEntries;
        //  Number of entries in the flush directory
        int unsigned flushEntries;
        //  Depth of the flush FIFO
        int unsigned flushFifoDepth;
        //  Width of the address in the memory interface
        int unsigned memAddrWidth;
        //  Width of the ID in the memory interface
        int unsigned memIdWidth;
        //  Width of the data in the memory interface
        int unsigned memDataWidth;
        //  Enable support for the write-through policy
        bit wtEn;
        //  Enable support for the write-back policy
        bit wbEn;
    } hpdcache_user_cfg_t;

    typedef struct packed {
        //  User configuration parameters
        hpdcache_user_cfg_t u;

        //  Internal parameters
        int unsigned clWidth;
        int unsigned clWordIdxWidth;
        int unsigned clOffsetWidth;
        int unsigned wordByteIdxWidth;
        int unsigned wayIndexWidth;
        int unsigned setWidth;
        int unsigned nlineWidth;
        int unsigned tagWidth;
        int unsigned reqWordIdxWidth;
        int unsigned reqOffsetWidth;
        int unsigned reqDataWidth;
        int unsigned reqDataBytes;
        int unsigned mshrSetWidth;
        int unsigned mshrWayWidth;
        int unsigned wbufDataWidth;
        int unsigned wbufDirPtrWidth;
        int unsigned wbufDataPtrWidth;
        int unsigned accessWidth;
    } hpdcache_cfg_t;

    function automatic hpdcache_cfg_t hpdcacheBuildConfig(input hpdcache_user_cfg_t p);
        hpdcache_cfg_t ret;

        ret.u = p;

        ret.clWidth = p.clWords * p.wordWidth;
        ret.clOffsetWidth = $clog2(ret.clWidth / 8);
        ret.clWordIdxWidth = $clog2(p.clWords);
        ret.wordByteIdxWidth = $clog2(p.wordWidth / 8);
        ret.wayIndexWidth = (p.ways > 1) ? $clog2(p.ways) : 1;
        ret.setWidth = $clog2(p.sets);
        ret.nlineWidth = p.paWidth - ret.clOffsetWidth;
        ret.tagWidth = ret.nlineWidth - ret.setWidth;
        ret.reqWordIdxWidth = $clog2(p.reqWords);
        ret.reqOffsetWidth = p.paWidth - ret.tagWidth;
        ret.reqDataWidth = p.reqWords * p.wordWidth;
        ret.reqDataBytes = ret.reqDataWidth/8;

        ret.mshrSetWidth = (p.mshrSets > 1) ? $clog2(p.mshrSets) : 1;
        ret.mshrWayWidth = (p.mshrWays > 1) ? $clog2(p.mshrWays) : 1;

        ret.wbufDataWidth = ret.reqDataWidth*p.wbufWords;
        ret.wbufDirPtrWidth = $clog2(p.wbufDirEntries);
        ret.wbufDataPtrWidth = $clog2(p.wbufDataEntries);

        ret.accessWidth = p.accessWords * p.wordWidth;

        return ret;
    endfunction
    //  }}}
endpackage
