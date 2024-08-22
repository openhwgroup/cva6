`ifndef WT_L15_TYPES_SVH
`define WT_L15_TYPES_SVH

`define L15_REQ_T(CVA6Cfg) struct packed { \
  logic l15_val;  // valid signal, asserted with request \
  logic l15_req_ack;  // ack for response \
  wt_cache_pkg::l15_reqtypes_t l15_rqtype;  // see below for encoding \
  logic l15_nc;  // non-cacheable bit \
  logic [2:0]                        l15_size;                  // transaction size: 000=Byte 001=2Byte; 010=4Byte; 011=8Byte; 111=Cache line (16/32Byte) \
  logic [CVA6Cfg.MEM_TID_WIDTH-1:0] l15_threadid;  // currently 0 or 1 \
  logic l15_prefetch;  // unused in openpiton \
  logic l15_invalidate_cacheline;  // unused by Ariane as L1 has no ECC at the moment \
  logic l15_blockstore;  // unused in openpiton \
  logic l15_blockinitstore;  // unused in openpiton \
  logic [CVA6Cfg.DCACHE_SET_ASSOC_WIDTH-1:0] l15_l1rplway;  // way to replace \
  logic [39:0] l15_address;  // physical address \
  logic [63:0] l15_data;  // word to write \
  logic [63:0] l15_data_next_entry;  // unused in Ariane (only used for CAS atomic requests) \
  logic [wt_cache_pkg::L15_TLB_CSM_WIDTH-1:0] l15_csm_data;  // unused in Ariane \
  logic [3:0] l15_amo_op;  // atomic operation type \
}

`define L15_RTRN_T(CVA6Cfg) struct packed { \
  logic l15_ack;  // ack for request struct \
  logic l15_header_ack;  // ack for request struct \
  logic l15_val;  // valid signal for return struct \
  wt_cache_pkg::l15_rtrntypes_t l15_returntype;  // see below for encoding \
  logic l15_l2miss;  // unused in Ariane \
  logic [1:0] l15_error;  // unused in openpiton \
  logic l15_noncacheable;  // non-cacheable bit \
  logic l15_atomic;  // asserted in load return and store ack packets of atomic tx \
  logic [CVA6Cfg.MEM_TID_WIDTH-1:0] l15_threadid;  // used as transaction ID \
  logic l15_prefetch;  // unused in openpiton \
  logic l15_f4b;  // 4byte instruction fill from I/O space (nc). \
  logic [63:0] l15_data_0;  // used for both caches \
  logic [63:0] l15_data_1;  // used for both caches \
  logic [63:0] l15_data_2;  // currently only used for I$ \
  logic [63:0] l15_data_3;  // currently only used for I$ \
  logic l15_inval_icache_all_way;  // invalidate all ways \
  logic l15_inval_dcache_all_way;  // unused in openpiton \
  logic [15:4] l15_inval_address_15_4;  // invalidate selected cacheline \
  logic l15_cross_invalidate;  // unused in openpiton \
  logic [CVA6Cfg.DCACHE_SET_ASSOC_WIDTH-1:0] l15_cross_invalidate_way;  // unused in openpiton \
  logic l15_inval_dcache_inval;  // invalidate selected cacheline and way \
  logic l15_inval_icache_inval;  // unused in openpiton \
  logic [CVA6Cfg.DCACHE_SET_ASSOC_WIDTH-1:0] l15_inval_way;  // way to invalidate \
  logic l15_blockinitstore;  // unused in openpiton \
}

`endif
