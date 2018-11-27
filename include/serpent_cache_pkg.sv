// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Michael Schaffner <schaffner@iis.ee.ethz.ch>, ETH Zurich
// Date: 15.08.2018
// Description: Package for OpenPiton compatible L1 cache subsystem

// this is needed to propagate the
// configuration in case Ariane is
// instantiated in OpenPiton
`ifdef PITON_ARIANE
`ifndef AXI64_CACHE_PORTS
  `include "l15.tmp.h"
  `include "define.tmp.h"
`endif
`endif

package serpent_cache_pkg;

  // these parames need to coincide with the
  // L1.5 parameterization, do not change
`ifdef PITON_ARIANE

`ifndef CONFIG_L15_ASSOCIATIVITY
    `define CONFIG_L15_ASSOCIATIVITY 4
`endif

`ifndef L15_THREADID_WIDTH
    `define L15_THREADID_WIDTH 1
`endif

`ifndef TLB_CSM_WIDTH
    `define TLB_CSM_WIDTH 33
`endif

  localparam L15_SET_ASSOC           = `CONFIG_L15_ASSOCIATIVITY;
  localparam L15_TID_WIDTH           = `L15_THREADID_WIDTH;
  localparam L15_TLB_CSM_WIDTH       = `TLB_CSM_WIDTH;
`else
  localparam L15_SET_ASSOC           = ariane_pkg::DCACHE_SET_ASSOC;// align with dcache for compatibility with the standard Ariane setup
  localparam L15_TID_WIDTH           = 2;
  localparam L15_TLB_CSM_WIDTH       = 33;
`endif
  localparam L15_WAY_WIDTH           = $clog2(L15_SET_ASSOC);
  localparam L1I_WAY_WIDTH           = $clog2(ariane_pkg::ICACHE_SET_ASSOC);
  localparam L1D_WAY_WIDTH           = $clog2(ariane_pkg::DCACHE_SET_ASSOC);

  // FIFO depths of L15 adapter
  localparam ADAPTER_REQ_FIFO_DEPTH  = 2;
  localparam ADAPTER_RTRN_FIFO_DEPTH = 2;


  // Calculated parameter
  localparam ICACHE_OFFSET_WIDTH     = $clog2(ariane_pkg::ICACHE_LINE_WIDTH/8);
  localparam ICACHE_NUM_WORDS        = 2**(ariane_pkg::ICACHE_INDEX_WIDTH-ICACHE_OFFSET_WIDTH);
  localparam ICACHE_CL_IDX_WIDTH     = $clog2(ICACHE_NUM_WORDS);// excluding byte offset

  localparam DCACHE_OFFSET_WIDTH     = $clog2(ariane_pkg::DCACHE_LINE_WIDTH/8);
  localparam DCACHE_NUM_WORDS        = 2**(ariane_pkg::DCACHE_INDEX_WIDTH-DCACHE_OFFSET_WIDTH);
  localparam DCACHE_CL_IDX_WIDTH     = $clog2(DCACHE_NUM_WORDS);// excluding byte offset

  localparam DCACHE_NUM_BANKS        = ariane_pkg::DCACHE_LINE_WIDTH/64;

  // write buffer parameterization
  localparam DCACHE_WBUF_DEPTH       = 8;
  localparam DCACHE_MAX_TX           = 2**L15_TID_WIDTH;
  localparam DCACHE_ID_WIDTH         = $clog2(DCACHE_MAX_TX);


  typedef struct packed {
    logic [ariane_pkg::DCACHE_INDEX_WIDTH+ariane_pkg::DCACHE_TAG_WIDTH-1:0] wtag;
    logic [63:0]                                                            data;
    logic [7:0]                                                             dirty;   // byte is dirty
    logic [7:0]                                                             valid;   // byte is valid
    logic [7:0]                                                             txblock; // byte is part of transaction in-flight
    logic                                                                   checked; // if cache state of this word has been checked
    logic [ariane_pkg::DCACHE_SET_ASSOC-1:0]                                hit_oh;  // valid way in the cache
  } wbuffer_t;

  // TX status registers are indexed with the transaction ID
  // they basically store which bytes from which buffer entry are part
  // of that transaction
  typedef struct packed {
    logic                                 vld;
    logic [7:0]                           be;
    logic [$clog2(DCACHE_WBUF_DEPTH)-1:0] ptr;
  } tx_stat_t;

  // local interfaces between caches and L15 adapter
  typedef enum logic [1:0] {
    DCACHE_STORE_REQ,
    DCACHE_LOAD_REQ,
    DCACHE_ATOMIC_REQ,
    DCACHE_INT_REQ
  }  dcache_out_t;

  typedef enum logic [2:0] {
    DCACHE_INV_REQ,  // no ack from the core required
    DCACHE_STORE_ACK,// note: this may contain an invalidation vector, too
    DCACHE_LOAD_ACK,
    DCACHE_ATOMIC_ACK,
    DCACHE_INT_ACK
  }  dcache_in_t;

  typedef enum logic [0:0] {
    ICACHE_INV_REQ, // no ack from the core required
    ICACHE_IFILL_ACK
  } icache_in_t;

  typedef struct packed {
    logic                                            vld;         // invalidate only affected way
    logic                                            all;         // invalidate all ways
    logic [ariane_pkg::ICACHE_INDEX_WIDTH-1:0]       idx;         // physical address to invalidate
    logic [L15_WAY_WIDTH-1:0]                        way;         // way to invalidate
  } cache_inval_t;

  // icache interface
  typedef struct packed {
    logic [$clog2(ariane_pkg::ICACHE_SET_ASSOC)-1:0] way;         // way to replace
    logic [63:0]                                     paddr;       // physical address
    logic                                            nc;          // noncacheable
    logic [L15_TID_WIDTH-1:0]                        tid;         // threadi id (used as transaction id in Ariane)
  } icache_req_t;

  typedef struct packed {
    icache_in_t                                      rtype;       // see definitions above
    logic [ariane_pkg::ICACHE_LINE_WIDTH-1:0]        data;        // full cache line width
    cache_inval_t                                    inv;         // invalidation vector
    logic                                            nc;          // noncacheable
    logic [L15_TID_WIDTH-1:0]                        tid;         // threadi id (used as transaction id in Ariane)
    logic                                            f4b;         // fetch 4 bytes only (from I/O space)
  } icache_rtrn_t;

  // dcache interface
  typedef struct packed {
    dcache_out_t                                     rtype;       // see definitions above
    logic [2:0]                                      size;        // transaction size: 000=Byte 001=2Byte; 010=4Byte; 011=8Byte; 111=Cache line (16/32Byte)
    logic [L1D_WAY_WIDTH-1:0]                        way;         // way to replace
    logic [63:0]                                     paddr;       // physical address
    logic [63:0]                                     data;        // word width of processor (no block stores at the moment)
    logic                                            nc;          // noncacheable
    logic [L15_TID_WIDTH-1:0]                        tid;         // threadi id (used as transaction id in Ariane)
    ariane_pkg::amo_t                                amo_op;      // amo opcode
  } dcache_req_t;

  typedef struct packed {
    dcache_in_t                                      rtype;       // see definitions above
    logic [ariane_pkg::DCACHE_LINE_WIDTH-1:0]        data;        // full cache line width
    cache_inval_t                                    inv;         // invalidation vector
    logic                                            nc;          // noncacheable
    logic [L15_TID_WIDTH-1:0]                        tid;         // threadi id (used as transaction id in Ariane)
  } dcache_rtrn_t;


  // taken from iop.h in openpiton
  // to l1.5 (only marked subset is used)
  typedef enum logic [4:0] {
    L15_LOAD_RQ     = 5'b00000, // load request
    L15_IMISS_RQ    = 5'b10000, // instruction fill request
    L15_STORE_RQ    = 5'b00001, // store request
    L15_ATOMIC_RQ   = 5'b00110, // atomic op
    //L15_CAS1_RQ     = 5'b00010, // compare and swap1 packet (OpenSparc atomics)
    //L15_CAS2_RQ     = 5'b00011, // compare and swap2 packet (OpenSparc atomics)
    //L15_SWAP_RQ     = 5'b00110, // swap packet (OpenSparc atomics)
    L15_STRLOAD_RQ  = 5'b00100, // unused
    L15_STRST_RQ    = 5'b00101, // unused
    L15_STQ_RQ      = 5'b00111, // unused
    L15_INT_RQ      = 5'b01001, // interrupt request
    L15_FWD_RQ      = 5'b01101, // unused
    L15_FWD_RPY     = 5'b01110, // unused
    L15_RSVD_RQ     = 5'b11111  // unused
  } l15_reqtypes_t;

  // from l1.5 (only marked subset is used)
  typedef enum logic [3:0] {
    L15_LOAD_RET               = 4'b0000, // load packet
    // L15_INV_RET                = 4'b0011, // invalidate packet, not unique...
    L15_ST_ACK                 = 4'b0100, // store ack packet
    //L15_AT_ACK                 = 4'b0011, // unused, not unique...
    L15_INT_RET                = 4'b0111, // interrupt packet
    L15_TEST_RET               = 4'b0101, // unused
    L15_FP_RET                 = 4'b1000, // unused
    L15_IFILL_RET              = 4'b0001, // instruction fill packet
    L15_EVICT_REQ              = 4'b0011, // eviction request
    L15_ERR_RET                = 4'b1100, // unused
    L15_STRLOAD_RET            = 4'b0010, // unused
    L15_STRST_ACK              = 4'b0110, // unused
    L15_FWD_RQ_RET             = 4'b1010, // unused
    L15_FWD_RPY_RET            = 4'b1011, // unused
    L15_RSVD_RET               = 4'b1111, // unused
    L15_CPX_RESTYPE_ATOMIC_RES = 4'b1110  // custom type for atomic responses
  } l15_rtrntypes_t;


  typedef struct packed {
    logic                              l15_val;                   // valid signal, asserted with request
    logic                              l15_req_ack;               // ack for response
    l15_reqtypes_t                     l15_rqtype;                // see below for encoding
    logic                              l15_nc;                    // non-cacheable bit
    logic [2:0]                        l15_size;                  // transaction size: 000=Byte 001=2Byte; 010=4Byte; 011=8Byte; 111=Cache line (16/32Byte)
    logic [L15_TID_WIDTH-1:0]          l15_threadid;              // currently 0 or 1
    logic                              l15_prefetch;              // unused in openpiton
    logic                              l15_invalidate_cacheline;  // unused by Ariane as L1 has no ECC at the moment
    logic                              l15_blockstore;            // unused in openpiton
    logic                              l15_blockinitstore;        // unused in openpiton
    logic [L15_WAY_WIDTH-1:0]          l15_l1rplway;              // way to replace
    logic [39:0]                       l15_address;               // physical address
    logic [63:0]                       l15_data;                  // word to write
    logic [63:0]                       l15_data_next_entry;       // unused in Ariane (only used for CAS atomic requests)
    logic [L15_TLB_CSM_WIDTH-1:0]      l15_csm_data;              // unused in Ariane
    logic [3:0]                        l15_amo_op;                // atomic operation type
  } l15_req_t;

  typedef struct packed {
    logic                              l15_ack;                   // ack for request struct
    logic                              l15_header_ack;            // ack for request struct
    logic                              l15_val;                   // valid signal for return struct
    l15_rtrntypes_t                    l15_returntype;            // see below for encoding
    logic                              l15_l2miss;                // unused in Ariane
    logic [1:0]                        l15_error;                 // unused in openpiton
    logic                              l15_noncacheable;          // non-cacheable bit
    logic                              l15_atomic;                // asserted in load return and store ack packets of atomic tx
    logic [L15_TID_WIDTH-1:0]          l15_threadid;              // used as transaction ID
    logic                              l15_prefetch;              // unused in openpiton
    logic                              l15_f4b;                   // 4byte instruction fill from I/O space (nc).
    logic [63:0]                       l15_data_0;                // used for both caches
    logic [63:0]                       l15_data_1;                // used for both caches
    logic [63:0]                       l15_data_2;                // currently only used for I$
    logic [63:0]                       l15_data_3;                // currently only used for I$
    logic                              l15_inval_icache_all_way;  // invalidate all ways
    logic                              l15_inval_dcache_all_way;  // unused in openpiton
    logic [15:4]                       l15_inval_address_15_4;    // invalidate selected cacheline
    logic                              l15_cross_invalidate;      // unused in openpiton
    logic [L15_WAY_WIDTH-1:0]          l15_cross_invalidate_way;  // unused in openpiton
    logic                              l15_inval_dcache_inval;    // invalidate selected cacheline and way
    logic                              l15_inval_icache_inval;    // unused in openpiton
    logic [L15_WAY_WIDTH-1:0]          l15_inval_way;             // way to invalidate
    logic                              l15_blockinitstore;        // unused in openpiton
  } l15_rtrn_t;

  // swap endianess in a 64bit word
  function automatic logic[63:0] swendian64(input logic[63:0] in);
    automatic logic[63:0] out;
    for(int k=0; k<64;k+=8)begin
        out[k +: 8] = in[63-k -: 8];
    end
    return out;
  endfunction

  function automatic logic [ariane_pkg::ICACHE_SET_ASSOC-1:0] icache_way_bin2oh (
    input logic [$clog2(ariane_pkg::ICACHE_SET_ASSOC)-1:0] in
  );
    logic [ariane_pkg::ICACHE_SET_ASSOC-1:0] out;
    out     = '0;
    out[in] = 1'b1;
    return out;
  endfunction

  function automatic logic [ariane_pkg::DCACHE_SET_ASSOC-1:0] dcache_way_bin2oh (
    input logic [$clog2(ariane_pkg::DCACHE_SET_ASSOC)-1:0] in
  );
    logic [ariane_pkg::DCACHE_SET_ASSOC-1:0] out;
    out     = '0;
    out[in] = 1'b1;
    return out;
  endfunction

  function automatic logic [DCACHE_NUM_BANKS-1:0] dcache_cl_bin2oh (
    input logic [$clog2(DCACHE_NUM_BANKS)-1:0] in
  );
    logic [DCACHE_NUM_BANKS-1:0] out;
    out     = '0;
    out[in] = 1'b1;
    return out;
  endfunction


  function automatic logic [5:0] popcnt64 (
    input logic [63:0] in
  );
    logic [5:0] cnt= 0;
    foreach (in[k]) begin
      cnt += in[k];
    end
    return cnt;
  endfunction : popcnt64

  function automatic logic [7:0] toByteEnable8(
    input logic [2:0] offset,
    input logic [1:0] size
  );
    logic [7:0] be;
    be = '0;
    unique case(size)
      2'b00:   be[offset]       = '1; // byte
      2'b01:   be[offset +:2 ]  = '1; // hword
      2'b10:   be[offset +:4 ]  = '1; // word
      default: be               = '1; // dword
    endcase // size
    return be;
  endfunction : toByteEnable8

  // openpiton requires the data to be replicated in case of smaller sizes than dwords
  function automatic logic [63:0] repData64(
    input logic [63:0] data,
    input logic [2:0]  offset,
    input logic [1:0]  size
  );
    logic [63:0] out;
    unique case(size)
      2'b00:   for(int k=0; k<8; k++) out[k*8  +: 8]    = data[offset*8 +: 8];  // byte
      2'b01:   for(int k=0; k<4; k++) out[k*16 +: 16]   = data[offset*8 +: 16]; // hword
      2'b10:   for(int k=0; k<2; k++) out[k*32 +: 32]   = data[offset*8 +: 32]; // word
      default: out   = data; // dword
    endcase // size
    return out;
  endfunction : repData64

  // note: this is openpiton specific. cannot transmit unaligned words.
  // hence we default to individual bytes in that case, and they have to be transmitted
  // one after the other
  function automatic logic [1:0] toSize64(
    input logic  [7:0] be
  );
    logic [1:0] size;
    unique case(be)
      8'b1111_1111:                                           size = 2'b11;  // dword
      8'b0000_1111, 8'b1111_0000:                             size = 2'b10; // word
      8'b1100_0000, 8'b0011_0000, 8'b0000_1100, 8'b0000_0011: size = 2'b01; // hword
      default:                                                size = 2'b00; // individual bytes
    endcase // be
    return size;
  endfunction : toSize64

  // align the physical address to the specified size:
  // 000: bytes
  // 001: hword
  // 010: word
  // 011: dword
  // 111: DCACHE line
  function automatic logic [63:0] paddrSizeAlign(
    input logic [63:0] paddr,
    input logic [2:0]  size
  );
    logic [63:0] out;
    out = paddr;
    unique case (size)
      3'b001: out[0:0]                     = '0;
      3'b010: out[1:0]                     = '0;
      3'b011: out[2:0]                     = '0;
      3'b111: out[DCACHE_OFFSET_WIDTH-1:0] = '0;
      default: ;
    endcase
    return out;
  endfunction : paddrSizeAlign

endpackage : serpent_cache_pkg
