// Attention: this is a dummy package for local compilation.
// The real package, with properly defined parameters, is in OpenPiton.

package l15_pkg;

  parameter int unsigned L15_PADDR_WIDTH = 40;  // Physical address bus in OpenPiton is 40
  parameter int unsigned L15_WORD_WIDTH = 64;
  parameter int unsigned L15_DATA_BUS_WIDTH = 256; // Hardcoded for the moment, changed on parametric cachelines
  parameter int unsigned L15_DATA_BUS_WORDS = L15_DATA_BUS_WIDTH / L15_WORD_WIDTH;
  parameter int unsigned L15_BE_WIDTH = L15_DATA_BUS_WIDTH / 8;
  parameter int unsigned L15_TID_WIDTH = 2;
  parameter int unsigned L15_SET_ASSOC = 4;
  parameter int unsigned L15_WAY_WIDTH = $clog2(L15_SET_ASSOC);
  parameter int unsigned L15_TLB_CSM_WIDTH = 33;

  typedef enum logic [4:0] {
    L15_LOAD_RQ    = 5'b00000,  // load request
    L15_IMISS_RQ   = 5'b10000,  // instruction fill request
    L15_STORE_RQ   = 5'b00001,  // store request
    L15_ATOMIC_RQ  = 5'b00110,  // atomic op
    //L15_CAS1_RQ    = 5'b00010,  // compare and swap1 packet (OpenSparc atomics)
    //L15_CAS2_RQ    = 5'b00011,  // compare and swap2 packet (OpenSparc atomics)
    //L15_SWAP_RQ    = 5'b00110,  // swap packet (OpenSparc atomics)
    L15_STRLOAD_RQ = 5'b00100,  // unused
    L15_STRST_RQ   = 5'b00101,  // unused
    L15_STQ_RQ     = 5'b00111,  // unused
    L15_INT_RQ     = 5'b01001,  // interrupt request
    L15_FWD_RQ     = 5'b01101,  // unused
    L15_FWD_RPY    = 5'b01110,  // unused
    L15_RSVD_RQ    = 5'b11111   // unused
  } l15_reqtypes_e;

  typedef enum logic [3:0] {
    L15_LOAD_RET               = 4'b0000,  // load packet
    //L15_INV_RET                = 4'b0011,  // invalidate packet, not unique...
    L15_ST_ACK                 = 4'b0100,  // store ack packet
    //L15_AT_ACK                 = 4'b0011,  // unused, not unique...
    L15_INT_RET                = 4'b0111,  // interrupt packet
    L15_TEST_RET               = 4'b0101,  // unused
    L15_FP_RET                 = 4'b1000,  // unused
    L15_IFILL_RET              = 4'b0001,  // instruction fill packet
    L15_EVICT_REQ              = 4'b0011,  // eviction request
    L15_ERR_RET                = 4'b1100,  // unused
    L15_STRLOAD_RET            = 4'b0010,  // unused
    L15_STRST_ACK              = 4'b0110,  // unused
    L15_FWD_RQ_RET             = 4'b1010,  // unused
    L15_FWD_RPY_RET            = 4'b1011,  // unused
    L15_RSVD_RET               = 4'b1111,  // unused
    L15_CPX_RESTYPE_ATOMIC_RES = 4'b1110   // custom type for atomic responses
  } l15_rtrntypes_e;

  typedef enum logic [3:0] {
    AMO_NONE = 4'b0000,
    AMO_LR   = 4'b0001,
    AMO_SC   = 4'b0010,
    AMO_SWAP = 4'b0011,
    AMO_ADD  = 4'b0100,
    AMO_AND  = 4'b0101,
    AMO_OR   = 4'b0110,
    AMO_XOR  = 4'b0111,
    AMO_MAX  = 4'b1000,
    AMO_MAXU = 4'b1001,
    AMO_MIN  = 4'b1010,
    AMO_MINU = 4'b1011,
    AMO_CAS1 = 4'b1100,  // unused, not part of riscv spec, but provided in OpenPiton
    AMO_CAS2 = 4'b1101   // unused, not part of riscv spec, but provided in OpenPiton
  } l15_amo_e;

  typedef struct packed {
    logic l15_val;  // valid signal, asserted with request
    logic l15_req_ack;  // ack for response
    l15_reqtypes_e l15_rqtype;  // see below for encoding
    logic l15_nc;  // non-cacheable bit
    logic [2:0]                        l15_size;                  // transaction size: 000=Byte 001=2Byte; 010=4Byte; 011=8Byte; 111=Cache line (16/32Byte)
    logic [L15_TID_WIDTH-1:0] l15_threadid;  // currently 0 or 1
    logic l15_prefetch;  // unused in openpiton
    logic l15_invalidate_cacheline;  // unused by Ariane as L1 has no ECC at the moment
    logic l15_blockstore;  // unused in openpiton
    logic l15_blockinitstore;  // unused in openpiton
    logic [L15_WAY_WIDTH-1:0] l15_l1rplway;  // way to replace
    logic [L15_PADDR_WIDTH-1:0] l15_address;  // physical address
    logic [L15_WORD_WIDTH-1:0] l15_data;  // word to write
    logic [L15_WORD_WIDTH-1:0] l15_data_next_entry;  // unused in Ariane (only used for CAS atomic requests)
    logic [L15_TLB_CSM_WIDTH-1:0] l15_csm_data;  // unused in Ariane
    l15_amo_e l15_amo_op;  // atomic operation type
    logic [L15_BE_WIDTH-1:0] l15_be;
  } l15_req_t;

  typedef struct packed {
    logic l15_ack;  // ack for request struct
    logic l15_header_ack;  // ack for request struct
    logic l15_val;  // valid signal for return struct
    l15_rtrntypes_e l15_returntype;  // see below for encoding
    logic l15_l2miss;  // unused in Ariane
    logic [1:0] l15_error;  // unused in openpiton
    logic l15_noncacheable;  // non-cacheable bit
    logic l15_atomic;  // asserted in load return and store ack packets of atomic tx
    logic [L15_TID_WIDTH-1:0] l15_threadid;  // used as transaction ID
    logic l15_prefetch;  // unused in openpiton
    logic l15_f4b;  // 4byte instruction fill from I/O space (nc).
    logic [L15_WORD_WIDTH-1:0] l15_data_0;  // used for both caches
    logic [L15_WORD_WIDTH-1:0] l15_data_1;  // used for both caches
    logic [L15_WORD_WIDTH-1:0] l15_data_2;  // currently only used for I$
    logic [L15_WORD_WIDTH-1:0] l15_data_3;  // currently only used for I$
    logic l15_inval_icache_all_way;  // invalidate all ways
    logic l15_inval_dcache_all_way;  // unused in openpiton
    logic [L15_PADDR_WIDTH-1:0] l15_inval_address;  // invalidate selected cacheline
    logic l15_cross_invalidate;  // unused in openpiton
    logic [L15_WAY_WIDTH-1:0] l15_cross_invalidate_way;  // unused in openpiton
    logic l15_inval_dcache_inval;  // invalidate selected cacheline and way
    logic l15_inval_icache_inval;  // unused in openpiton
    logic [L15_WAY_WIDTH-1:0] l15_inval_way;  // way to invalidate
    logic l15_blockinitstore;  // unused in openpiton
  } l15_rtrn_t;

endpackage
