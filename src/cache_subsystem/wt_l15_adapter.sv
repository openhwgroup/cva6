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
// Date: 08.08.2018
// Description: adapter module to connect the L1D$ and L1I$ to the native
// interface of the OpenPiton L1.5 cache.
//
// A couple of notes:
//
// 1) the L15 has been designed for an OpenSparc T1 core with 2 threads and can serve only
//    1 ld and rd request per thread. Ariane has only one hart, but the LSU can issue several write
//    requests to optimize bandwidth. hence, we reuse the threadid field to issue and track multiple
//    requests (up to 2 in this case).
//
// 2) the CSM (clumped shared memory = coherence domain restriction in OpenPiton)
//    feature is currently not supported by Ariane.
//
// 3) some features like blockinitstore, prefetch, ECC errors are not used (see interface below)
//
// 4) the arbiter can store upt to two outgoing requests per cache. incoming responses are passed
//    through one streaming register, and need to be consumed unconditionally by the caches.
//
// 5) The L1.5 protocol is closely related to the CPX bus of openSPARC, see also [1,2]
//
// 6) Note on transaction data and size: if a store packet is less than 64 bits, then
//    the field is filled with copies of the data. in case of an interrupt vector,
//    an 18bit interrupt vector is expected.
//
// 7) L1I$ refill requests always have precedence over L1D$ requests.
//
// 8) L1I$ fill requests are always complete cache lines at the moment
//
// 9) the adapter converts from little endian (Ariane) to big endian (openpiton), and vice versa.
//
// 10) L1I$ requests to I.O space (bit39 of address = 1'b1) always return 32bit nc data
//
// Refs: [1] OpenSPARC T1 Microarchitecture Specification
//           https://www.oracle.com/technetwork/systems/opensparc/t1-01-opensparct1-micro-arch-1538959.html
//       [2] OpenPiton Microarchitecture Specification
//           https://parallel.princeton.edu/openpiton/docs/micro_arch.pdf
//


module wt_l15_adapter import ariane_pkg::*; import wt_cache_pkg::*; #(
  parameter bit          SwapEndianess = 1
) (
  input logic                  clk_i,
  input logic                  rst_ni,

  // icache
  input  logic                 icache_data_req_i,
  output logic                 icache_data_ack_o,
  input  icache_req_t          icache_data_i,
  // returning packets must be consumed immediately
  output logic                 icache_rtrn_vld_o,
  output icache_rtrn_t         icache_rtrn_o,

  // dcache
  input  logic                 dcache_data_req_i,
  output logic                 dcache_data_ack_o,
  input  dcache_req_t          dcache_data_i,
  // returning packets must be consumed immediately
  output logic                 dcache_rtrn_vld_o,
  output dcache_rtrn_t         dcache_rtrn_o,

  // L15
  output l15_req_t             l15_req_o,
  input  l15_rtrn_t            l15_rtrn_i
);

// request path
icache_req_t icache_data;
logic icache_data_full, icache_data_empty;

dcache_req_t dcache_data;
logic dcache_data_full, dcache_data_empty;

logic [1:0] arb_req, arb_ack;
logic       arb_idx;

// return path
logic rtrn_fifo_empty, rtrn_fifo_full, rtrn_fifo_pop;
l15_rtrn_t rtrn_fifo_data;


///////////////////////////////////////////////////////
// request path to L15
///////////////////////////////////////////////////////

  // relevant l15 signals
  // l15_req_t                          l15_req_o.l15_rqtype;                // see below for encoding
  // logic                              l15_req_o.l15_nc;                    // non-cacheable bit
  // logic [2:0]                        l15_req_o.l15_size;                  // transaction size: 000=Byte 001=2Byte; 010=4Byte; 011=8Byte; 111=Cache line (16/32Byte)
  // logic [L15_TID_WIDTH-1:0]          l15_req_o.l15_threadid;              // currently 0 or 1
  // logic                              l15_req_o.l15_invalidate_cacheline;  // unused by Ariane as L1 has no ECC at the moment
  // logic [L15_WAY_WIDTH-1:0]          l15_req_o.l15_l1rplway;              // way to replace
  // logic [39:0]                       l15_req_o.l15_address;               // physical address
  // logic [63:0]                       l15_req_o.l15_data;                  // word to write
  // logic [63:0]                       l15_req_o.l15_data_next_entry;       // unused in Ariane (only used for CAS atomic requests)
  // logic [L15_TLB_CSM_WIDTH-1:0]      l15_req_o.l15_csm_data;


  assign icache_data_ack_o  = icache_data_req_i & ~icache_data_full;
  assign dcache_data_ack_o  = dcache_data_req_i & ~dcache_data_full;

  // data mux
  assign l15_req_o.l15_nc                   = (arb_idx)        ? dcache_data.nc    : icache_data.nc;
  // icache fills are either cachelines or 4byte fills, depending on whether they go to the Piton I/O space or not.
  assign l15_req_o.l15_size                 = (arb_idx)        ? dcache_data.size  :
                                              (icache_data.nc) ? 3'b010            : 3'b111;
  assign l15_req_o.l15_threadid             = (arb_idx)        ? dcache_data.tid   : icache_data.tid;
  assign l15_req_o.l15_prefetch             = '0; // unused in openpiton
  assign l15_req_o.l15_invalidate_cacheline = '0; // unused by Ariane as L1 has no ECC at the moment
  assign l15_req_o.l15_blockstore           = '0; // unused in openpiton
  assign l15_req_o.l15_blockinitstore       = '0; // unused in openpiton
  assign l15_req_o.l15_l1rplway             = (arb_idx) ? dcache_data.way   : icache_data.way;

  assign l15_req_o.l15_address              = (arb_idx) ? dcache_data.paddr :
                                                          icache_data.paddr;

  assign l15_req_o.l15_data_next_entry      = '0; // unused in Ariane (only used for CAS atomic requests)
  assign l15_req_o.l15_csm_data             = '0; // unused in Ariane (only used for coherence domain restriction features)
  assign l15_req_o.l15_amo_op               = dcache_data.amo_op;


  // openpiton is big endian
  if (SwapEndianess) assign l15_req_o.l15_data = swendian64(dcache_data.data);
  else               assign l15_req_o.l15_data = dcache_data.data;

  // arbiter
  rrarbiter #(
    .NUM_REQ(2),
    .LOCK_IN(1)
  ) i_rrarbiter (
    .clk_i  ( clk_i                ),
    .rst_ni ( rst_ni               ),
    .flush_i( '0                   ),
    .en_i   ( l15_rtrn_i.l15_ack   ),
    .req_i  ( arb_req              ),
    .ack_o  ( arb_ack              ),
    .vld_o  (                      ),
    .idx_o  ( arb_idx              )
  );

  assign arb_req           = {~dcache_data_empty, ~icache_data_empty};
  assign l15_req_o.l15_val = (|arb_req);// & ~header_ack_q;

  // encode packet type
  always_comb begin : p_req
    l15_req_o.l15_rqtype = L15_LOAD_RQ;

    unique case (arb_idx)
      0: begin// icache
        l15_req_o.l15_rqtype = L15_IMISS_RQ;
      end
      1: begin
        unique case (dcache_data.rtype)
          DCACHE_STORE_REQ: begin
            l15_req_o.l15_rqtype = L15_STORE_RQ;
          end
          DCACHE_LOAD_REQ: begin
            l15_req_o.l15_rqtype = L15_LOAD_RQ;
          end
          DCACHE_ATOMIC_REQ: begin
            l15_req_o.l15_rqtype = L15_ATOMIC_RQ;
          end
          // DCACHE_INT_REQ: begin
          //     //TODO interrupt requests
          // end
          default: begin
            ;
          end
        endcase // dcache_data.rtype
      end
      default: begin
        ;
      end
    endcase
  end // p_req

  fifo_v2 #(
    .dtype       (  icache_req_t            ),
    .DEPTH       (  ADAPTER_REQ_FIFO_DEPTH  )
    ) i_icache_data_fifo (
    .clk_i       (  clk_i                   ),
    .rst_ni      (  rst_ni                  ),
    .flush_i     (  1'b0                    ),
    .testmode_i  (  1'b0                    ),
    .full_o      (  icache_data_full        ),
    .empty_o     (  icache_data_empty       ),
    .alm_full_o  (                          ),
    .alm_empty_o (                          ),
    .data_i      (  icache_data_i           ),
    .push_i      (  icache_data_ack_o       ),
    .data_o      (  icache_data             ),
    .pop_i       (  arb_ack[0]              )
  );

  fifo_v2 #(
    .dtype       (  dcache_req_t            ),
    .DEPTH       (  ADAPTER_REQ_FIFO_DEPTH  )
    ) i_dcache_data_fifo (
    .clk_i       (  clk_i                   ),
    .rst_ni      (  rst_ni                  ),
    .flush_i     (  1'b0                    ),
    .testmode_i  (  1'b0                    ),
    .full_o      (  dcache_data_full        ),
    .empty_o     (  dcache_data_empty       ),
    .alm_full_o  (                          ),
    .alm_empty_o (                          ),
    .data_i      (  dcache_data_i           ),
    .push_i      (  dcache_data_ack_o       ),
    .data_o      (  dcache_data             ),
    .pop_i       (  arb_ack[1]              )
  );

///////////////////////////////////////////////////////
// return path from L15
///////////////////////////////////////////////////////

  // relevant l15 signals
  // l15_rtrn_i.l15_returntype;            // see below for encoding
  // l15_rtrn_i.l15_noncacheable;          // non-cacheable bit
  // l15_rtrn_i.l15_atomic;                // asserted in load return and store ack pack
  // l15_rtrn_i.l15_threadid;              // used as transaction ID
  // l15_rtrn_i.l15_f4b;                   // 4byte instruction fill from I/O space (nc).
  // l15_rtrn_i.l15_data_0;                // used for both caches
  // l15_rtrn_i.l15_data_1;                // used for both caches
  // l15_rtrn_i.l15_data_2;                // currently only used for I$
  // l15_rtrn_i.l15_data_3;                // currently only used for I$
  // l15_rtrn_i.l15_inval_icache_all_way;  // invalidate all ways
  // l15_rtrn_i.l15_inval_address_15_4;    // invalidate selected cacheline
  // l15_rtrn_i.l15_inval_dcache_inval;    // invalidate selected cacheline and way
  // l15_rtrn_i.l15_inval_way;             // way to invalidate

  // acknowledge if we have space to hold this packet
  assign l15_req_o.l15_req_ack = l15_rtrn_i.l15_val & ~rtrn_fifo_full;
  // packets have to be consumed immediately
  assign rtrn_fifo_pop = ~rtrn_fifo_empty;

  // decode packet type
  always_comb begin : p_rtrn_logic
    icache_rtrn_o.rtype = ICACHE_IFILL_ACK;
    dcache_rtrn_o.rtype = DCACHE_LOAD_ACK;
    icache_rtrn_vld_o   = 1'b0;
    dcache_rtrn_vld_o   = 1'b0;
    if(!rtrn_fifo_empty) begin
      unique case (rtrn_fifo_data.l15_returntype)
        L15_LOAD_RET:  begin
          dcache_rtrn_o.rtype = DCACHE_LOAD_ACK;
          dcache_rtrn_vld_o   = 1'b1;
        end
        L15_ST_ACK:    begin
          dcache_rtrn_o.rtype = DCACHE_STORE_ACK;
          dcache_rtrn_vld_o   = 1'b1;
        end
        L15_IFILL_RET: begin
          icache_rtrn_o.rtype = ICACHE_IFILL_ACK;
          icache_rtrn_vld_o   = 1'b1;
        end
        L15_EVICT_REQ: begin
          icache_rtrn_o.rtype = ICACHE_INV_REQ;
          dcache_rtrn_o.rtype = DCACHE_INV_REQ;
          icache_rtrn_vld_o   = icache_rtrn_o.inv.vld | icache_rtrn_o.inv.all;
          dcache_rtrn_vld_o   = dcache_rtrn_o.inv.vld | dcache_rtrn_o.inv.all;
        end
        L15_CPX_RESTYPE_ATOMIC_RES: begin
          dcache_rtrn_o.rtype = DCACHE_ATOMIC_ACK;
          dcache_rtrn_vld_o   = 1'b1;
        end
        // L15_INT_RET:   begin
        // TODO: implement this
        // dcache_rtrn_o.reqType = DCACHE_INT_ACK;
        // end
        default: begin
        ;
        end
      endcase // rtrn_fifo_data.l15_returntype
    end
  end

  // openpiton is big endian
  if (SwapEndianess) begin : gen_swap
    assign dcache_rtrn_o.data = { swendian64(rtrn_fifo_data.l15_data_1),
                                  swendian64(rtrn_fifo_data.l15_data_0) };

    assign icache_rtrn_o.data = { swendian64(rtrn_fifo_data.l15_data_3),
                                  swendian64(rtrn_fifo_data.l15_data_2),
                                  swendian64(rtrn_fifo_data.l15_data_1),
                                  swendian64(rtrn_fifo_data.l15_data_0) };
  end else begin : gen_no_swap
    assign dcache_rtrn_o.data = { rtrn_fifo_data.l15_data_1,
                                  rtrn_fifo_data.l15_data_0 };

    assign icache_rtrn_o.data = { rtrn_fifo_data.l15_data_3,
                                  rtrn_fifo_data.l15_data_2,
                                  rtrn_fifo_data.l15_data_1,
                                  rtrn_fifo_data.l15_data_0 };
  end

  // fifo signals
  assign icache_rtrn_o.tid      = rtrn_fifo_data.l15_threadid;
  assign dcache_rtrn_o.tid      = rtrn_fifo_data.l15_threadid;

  // invalidation signal mapping
  assign icache_rtrn_o.inv.idx  = {rtrn_fifo_data.l15_inval_address_15_4, 4'b0000};
  assign icache_rtrn_o.inv.way  = rtrn_fifo_data.l15_inval_way;
  assign icache_rtrn_o.inv.vld  = rtrn_fifo_data.l15_inval_icache_inval;
  assign icache_rtrn_o.inv.all  = rtrn_fifo_data.l15_inval_icache_all_way;

  assign dcache_rtrn_o.inv.idx  = {rtrn_fifo_data.l15_inval_address_15_4, 4'b0000};
  assign dcache_rtrn_o.inv.way  = rtrn_fifo_data.l15_inval_way;
  assign dcache_rtrn_o.inv.vld  = rtrn_fifo_data.l15_inval_dcache_inval;
  assign dcache_rtrn_o.inv.all  = rtrn_fifo_data.l15_inval_dcache_all_way;

  fifo_v2 #(
    .dtype       (  l15_rtrn_t               ),
    .DEPTH       (  ADAPTER_RTRN_FIFO_DEPTH  )
  ) i_rtrn_fifo (
    .clk_i       (  clk_i                    ),
    .rst_ni      (  rst_ni                   ),
    .flush_i     (  1'b0                     ),
    .testmode_i  (  1'b0                     ),
    .full_o      (  rtrn_fifo_full           ),
    .empty_o     (  rtrn_fifo_empty          ),
    .alm_full_o  (                           ),
    .alm_empty_o (                           ),
    .data_i      (  l15_rtrn_i               ),
    .push_i      (  l15_req_o.l15_req_ack    ),
    .data_o      (  rtrn_fifo_data           ),
    .pop_i       (  rtrn_fifo_pop            )
  );


///////////////////////////////////////////////////////
// assertions
///////////////////////////////////////////////////////

//pragma translate_off
`ifndef VERILATOR

  invalidations: assert property (
    @(posedge clk_i) disable iff (!rst_ni) l15_rtrn_i.l15_val |-> l15_rtrn_i.l15_returntype == L15_EVICT_REQ |-> (l15_rtrn_i.l15_inval_icache_inval    |
                                                                                                                  l15_rtrn_i.l15_inval_dcache_inval    |
                                                                                                                  l15_rtrn_i.l15_inval_icache_all_way  |
                                                                                                                  l15_rtrn_i.l15_inval_dcache_all_way))
      else $fatal(1,"[l15_adapter] got invalidation package with zero invalidation flags");

  blockstore_o: assert property (
    @(posedge clk_i) disable iff (!rst_ni) l15_req_o.l15_val |-> l15_req_o.l15_rqtype == L15_STORE_RQ |-> !(l15_req_o.l15_blockstore || l15_req_o.l15_blockinitstore))
      else $fatal(1,"[l15_adapter] blockstores are not supported (out)");

  blockstore_i: assert property (
    @(posedge clk_i) disable iff (!rst_ni) l15_rtrn_i.l15_val |-> l15_rtrn_i.l15_returntype inside {L15_ST_ACK, L15_ST_ACK} |-> !l15_rtrn_i.l15_blockinitstore)
      else $fatal(1,"[l15_adapter] blockstores are not supported (in)");

  unsuported_rtrn_types: assert property (
    @(posedge clk_i) disable iff (!rst_ni) (l15_rtrn_i.l15_val |-> l15_rtrn_i.l15_returntype inside {L15_LOAD_RET, L15_ST_ACK, L15_IFILL_RET, L15_EVICT_REQ, L15_CPX_RESTYPE_ATOMIC_RES}))
      else $warning("[l15_adapter] return type %X04 is not (yet) supported by l15 adapter.", l15_rtrn_i.l15_returntype);

  amo_type: assert property (
    @(posedge clk_i) disable iff (!rst_ni) (l15_rtrn_i.l15_val |-> l15_rtrn_i.l15_returntype inside {L15_CPX_RESTYPE_ATOMIC_RES} |-> l15_rtrn_i.l15_atomic ))
      else $fatal(1,"[l15_adapter] l15_atomic must be asserted when the return type is an ATOMIC_RES");

  initial begin
    // assert wrong parameterizations
    assert (L15_SET_ASSOC >= ICACHE_SET_ASSOC)
      else $fatal(1,"[l15_adapter] number of icache ways must be smaller or equal the number of L15 ways");
    // assert wrong parameterizations
    assert (L15_SET_ASSOC >= DCACHE_SET_ASSOC)
      else $fatal(1,"[l15_adapter] number of dcache ways must be smaller or equal the number of L15 ways");
    // invalidation address returned by L1.5 is 16 bit
    assert (16 >= DCACHE_INDEX_WIDTH && 16 >= ICACHE_INDEX_WIDTH)
      else $fatal(1,"[l15_adapter] maximum number of index bits supported by L1.5 is 16");
  end
`endif
//pragma translate_on

endmodule // wt_l15_adapter