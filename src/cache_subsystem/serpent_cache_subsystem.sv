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
// Description: Ariane cache subsystem that is compatible with the OpenPiton
//              coherent memory system.
//
//              Define PITON_ARIANE if you want to use this cache.
//              Define AXI64_CACHE_PORTS if you want to use this cache
//              with a standard 64bit AXI interace instead of the openpiton
//              L1.5 interface.

import ariane_pkg::*;
import serpent_cache_pkg::*;

module serpent_cache_subsystem #(
`ifdef AXI64_CACHE_PORTS
  parameter int unsigned AxiIdWidth    = 10,
`endif
  parameter logic [63:0] CachedAddrBeg = 64'h00_8000_0000, // begin of cached region
  parameter logic [63:0] CachedAddrEnd = 64'h80_0000_0000, // end of cached region
  parameter bit          SwapEndianess = 0                 // swap endianess in l15 adapter
) (
  input logic                            clk_i,
  input logic                            rst_ni,
  // I$
  input  logic                           icache_en_i,            // enable icache (or bypass e.g: in debug mode)
  input  logic                           icache_flush_i,         // flush the icache, flush and kill have to be asserted together
  output logic                           icache_miss_o,          // to performance counter
  // address translation requests
  input  icache_areq_i_t                 icache_areq_i,          // to/from frontend
  output icache_areq_o_t                 icache_areq_o,
  // data requests
  input  icache_dreq_i_t                 icache_dreq_i,          // to/from frontend
  output icache_dreq_o_t                 icache_dreq_o,
  // D$
  // Cache management
  input  logic                           dcache_enable_i,        // from CSR
  input  logic                           dcache_flush_i,         // high until acknowledged
  output logic                           dcache_flush_ack_o,     // send a single cycle acknowledge signal when the cache is flushed
  output logic                           dcache_miss_o,          // we missed on a ld/st
  // AMO interface
  input amo_req_t                        dcache_amo_req_i,
  output amo_resp_t                      dcache_amo_resp_o,
  // Request ports
  input  dcache_req_i_t   [2:0]          dcache_req_ports_i,     // to/from LSU
  output dcache_req_o_t   [2:0]          dcache_req_ports_o,     // to/from LSU
  // writebuffer status
  output logic                           wbuffer_empty_o,
`ifdef AXI64_CACHE_PORTS
  // memory side
  output ariane_axi::req_t               axi_req_o,
  input  ariane_axi::resp_t              axi_resp_i
`else
  // L15 (memory side)
  output l15_req_t                       l15_req_o,
  input  l15_rtrn_t                      l15_rtrn_i
`endif
  // TODO: interrupt interface
);

logic icache_adapter_data_req, adapter_icache_data_ack, adapter_icache_rtrn_vld;
serpent_cache_pkg::icache_req_t  icache_adapter;
serpent_cache_pkg::icache_rtrn_t adapter_icache;


logic dcache_adapter_data_req, adapter_dcache_data_ack, adapter_dcache_rtrn_vld;
serpent_cache_pkg::dcache_req_t  dcache_adapter;
serpent_cache_pkg::dcache_rtrn_t adapter_dcache;

`ifdef AXI64_CACHE_PORTS
// used for local plumbing in this case
l15_req_t                       l15_req;
l15_rtrn_t                      l15_rtrn;
`endif

serpent_icache #(
`ifdef AXI64_CACHE_PORTS
    .Axi64BitCompliant  ( 1'b1          ),
`endif
    // use ID 0 for icache reads
    .RdTxId             ( 0             ),
    .CachedAddrBeg      ( CachedAddrBeg ),
    .CachedAddrEnd      ( CachedAddrEnd )
  ) i_serpent_icache (
    .clk_i              ( clk_i                   ),
    .rst_ni             ( rst_ni                  ),
    .flush_i            ( icache_flush_i          ),
    .en_i               ( icache_en_i             ),
    .miss_o             ( icache_miss_o           ),
    .areq_i             ( icache_areq_i           ),
    .areq_o             ( icache_areq_o           ),
    .dreq_i             ( icache_dreq_i           ),
    .dreq_o             ( icache_dreq_o           ),
    .mem_rtrn_vld_i     ( adapter_icache_rtrn_vld ),
    .mem_rtrn_i         ( adapter_icache          ),
    .mem_data_req_o     ( icache_adapter_data_req ),
    .mem_data_ack_i     ( adapter_icache_data_ack ),
    .mem_data_o         ( icache_adapter          )
  );


// Note:
// Ports 0/1 for PTW and LD unit are read only.
// they have equal prio and are RR arbited
// Port 2 is write only and goes into the merging write buffer
serpent_dcache #(
    // use ID 1 for dcache reads and amos. note that the writebuffer
    // uses all IDs up to DCACHE_MAX_TX-1 for write transactions.
    .RdAmoTxId       ( 1             ),
    .CachedAddrBeg   ( CachedAddrBeg ),
    .CachedAddrEnd   ( CachedAddrEnd )
  ) i_serpent_dcache (
    .clk_i           ( clk_i                   ),
    .rst_ni          ( rst_ni                  ),
    .enable_i        ( dcache_enable_i         ),
    .flush_i         ( dcache_flush_i          ),
    .flush_ack_o     ( dcache_flush_ack_o      ),
    .miss_o          ( dcache_miss_o           ),
    .wbuffer_empty_o ( wbuffer_empty_o         ),
    .amo_req_i       ( dcache_amo_req_i        ),
    .amo_resp_o      ( dcache_amo_resp_o       ),
    .req_ports_i     ( dcache_req_ports_i      ),
    .req_ports_o     ( dcache_req_ports_o      ),
    .mem_rtrn_vld_i  ( adapter_dcache_rtrn_vld ),
    .mem_rtrn_i      ( adapter_dcache          ),
    .mem_data_req_o  ( dcache_adapter_data_req ),
    .mem_data_ack_i  ( adapter_dcache_data_ack ),
    .mem_data_o      ( dcache_adapter          )
  );


// arbiter/adapter
serpent_l15_adapter #(
    .SwapEndianess   ( SwapEndianess ),
    .CachedAddrBeg   ( CachedAddrBeg ),
    .CachedAddrEnd   ( CachedAddrEnd )
  ) i_adapter (
    .clk_i              ( clk_i                   ),
    .rst_ni             ( rst_ni                  ),
    .icache_data_req_i  ( icache_adapter_data_req ),
    .icache_data_ack_o  ( adapter_icache_data_ack ),
    .icache_data_i      ( icache_adapter          ),
    .icache_rtrn_vld_o  ( adapter_icache_rtrn_vld ),
    .icache_rtrn_o      ( adapter_icache          ),
    .dcache_data_req_i  ( dcache_adapter_data_req ),
    .dcache_data_ack_o  ( adapter_dcache_data_ack ),
    .dcache_data_i      ( dcache_adapter          ),
    .dcache_rtrn_vld_o  ( adapter_dcache_rtrn_vld ),
    .dcache_rtrn_o      ( adapter_dcache          ),
`ifdef AXI64_CACHE_PORTS
    .l15_req_o          ( l15_req                 ),
    .l15_rtrn_i         ( l15_rtrn                )
`else
    .l15_req_o          ( l15_req_o               ),
    .l15_rtrn_i         ( l15_rtrn_i              )
`endif
  );

///////////////////////////////////////////////////////
// different memory plumbing to allow for using the
// serpent cache subsystem in a standard AXI setting.
///////////////////////////////////////////////////////

`ifdef AXI64_CACHE_PORTS

// support up to 512bit cache lines
localparam AxiNumWords = ariane_pkg::ICACHE_LINE_WIDTH/64;

typedef enum logic [1:0] {IFILL, LRSC, ATOP, STD} tx_t;
logic axi_rd_req, axi_rd_gnt;
logic [63:0]                    axi_rd_addr, axi_wr_addr;
logic [$clog2(AxiNumWords)-1:0] axi_rd_blen, axi_wr_blen;
logic [1:0] axi_rd_size, axi_wr_size;
logic [AxiIdWidth-1:0] axi_rd_id_in, axi_wr_id_in, axi_rd_id_out, axi_wr_id_out;
logic axi_rd_valid;
logic [AxiNumWords-1:0][63:0] axi_rd_data, axi_wr_data;
logic [AxiNumWords-1:0][7:0] axi_wr_be;
logic axi_wr_req, axi_wr_gnt;
logic axi_wr_valid, axi_rd_rdy, axi_wr_rdy;
logic axi_rd_lock, axi_wr_lock, axi_rd_exokay, axi_wr_exokay;
logic [5:0] axi_wr_atop;

logic [serpent_cache_pkg::L15_TID_WIDTH+2-1:0] id_tmp;
logic rd_pending_d, rd_pending_q;


// the axi interconnect does not correctly handle the ordering of read responses.
// workaround: only allow for one outstanding TX. need to improve this.
assign rd_pending_d = (axi_rd_valid) ? '0 : rd_pending_q | axi_rd_gnt;

// request side
always_comb begin : p_axi_req
  axi_wr_data  = l15_req.l15_data;
  axi_rd_addr  = l15_req.l15_address;
  axi_wr_addr  = l15_req.l15_address;
  axi_rd_req   = 1'b0;
  axi_wr_req   = 1'b0;
  axi_rd_id_in = {l15_req.l15_threadid, STD, l15_req.l15_nc};
  axi_wr_id_in = {l15_req.l15_threadid, STD, l15_req.l15_nc};
  axi_rd_size  = l15_req.l15_size[1:0];
  axi_wr_size  = l15_req.l15_size[1:0];
  axi_rd_blen  = '0;
  axi_wr_blen  = '0;// single word writes
  axi_wr_be    = '0;
  axi_rd_lock  = '0;
  axi_wr_lock  = '0;
  axi_wr_atop  = '0;

  if (l15_req.l15_val) begin
    unique case (l15_req.l15_rqtype)
      //////////////////////////////////////
      serpent_cache_pkg::L15_IMISS_RQ: begin
        axi_rd_req   = !rd_pending_q;
        axi_rd_id_in = {l15_req.l15_threadid, IFILL, l15_req.l15_nc};
        // always request 64bit words in case of ifill
        axi_rd_size  = 2'b11;
        if (l15_req.l15_size[2]) axi_rd_blen = ariane_pkg::ICACHE_LINE_WIDTH/64-1;
      end
      //////////////////////////////////////
      serpent_cache_pkg::L15_LOAD_RQ: begin
        axi_rd_req   = !rd_pending_q;
        if (l15_req.l15_size[2]) axi_rd_blen = ariane_pkg::DCACHE_LINE_WIDTH/64-1;
      end
      //////////////////////////////////////
      serpent_cache_pkg::L15_STORE_RQ: begin
        axi_wr_req   = 1'b1;
        axi_wr_be    = serpent_cache_pkg::toByteEnable8(l15_req.l15_address[2:0], l15_req.l15_size[1:0]);
      end
      //////////////////////////////////////
      serpent_cache_pkg::L15_ATOMIC_RQ: begin
        // default  
        axi_wr_req   = 1'b1;
        axi_wr_id_in = {l15_req.l15_threadid, ATOP, l15_req.l15_nc}; // encode as lr/sc
        axi_wr_be    = serpent_cache_pkg::toByteEnable8(l15_req.l15_address[2:0], l15_req.l15_size[1:0]);
        unique case (l15_req.l15_amo_op)
          AMO_LR: begin
            axi_rd_lock  = 1'b1;
            axi_rd_req   = !rd_pending_q;
            axi_rd_id_in = {l15_req.l15_threadid, LRSC, l15_req.l15_nc}; // encode as lr/sc
            // tie to zero in this special case
            axi_wr_req   = 1'b0;
          end
          AMO_SC: begin
            axi_wr_lock  = 1'b1;
            axi_wr_id_in = {l15_req.l15_threadid, LRSC, l15_req.l15_nc};
          end  
          // RISC-V atops have a load semantic
          AMO_SWAP: axi_wr_atop  = {axi_pkg::ATOP_ATOMICLOAD, axi_pkg::ATOP_ATOMICSWAP};
          AMO_ADD:  axi_wr_atop  = {axi_pkg::ATOP_ATOMICLOAD, axi_pkg::ATOP_ADD};
          AMO_AND:  begin 
            // in this case we need to invert the data to get a "CLR" semantic
            axi_wr_data  = ~l15_req.l15_data;
            axi_wr_atop  = {axi_pkg::ATOP_ATOMICLOAD, axi_pkg::ATOP_CLR};
          end  
          AMO_OR:   axi_wr_atop  = {axi_pkg::ATOP_ATOMICLOAD, axi_pkg::ATOP_SET};
          AMO_XOR:  axi_wr_atop  = {axi_pkg::ATOP_ATOMICLOAD, axi_pkg::ATOP_EOR};
          AMO_MAX:  axi_wr_atop  = {axi_pkg::ATOP_ATOMICLOAD, axi_pkg::ATOP_SMAX};
          AMO_MAXU: axi_wr_atop  = {axi_pkg::ATOP_ATOMICLOAD, axi_pkg::ATOP_UMAX};
          AMO_MIN:  axi_wr_atop  = {axi_pkg::ATOP_ATOMICLOAD, axi_pkg::ATOP_SMIN}; 
          AMO_MINU: axi_wr_atop  = {axi_pkg::ATOP_ATOMICLOAD, axi_pkg::ATOP_UMIN}; 
        endcase  
      end
      //////////////////////////////////////
    endcase
  end  
end  

// return path
always_comb begin : p_axi_rtrn
  // default
  l15_rtrn                   = '0;
  l15_rtrn.l15_ack           = axi_rd_gnt | axi_wr_gnt;
  l15_rtrn.l15_header_ack    = axi_rd_gnt | axi_wr_gnt;
  l15_rtrn.l15_data_0        = axi_rd_data[0];
  l15_rtrn.l15_data_1        = axi_rd_data[1];
  l15_rtrn.l15_data_2        = axi_rd_data[2];
  l15_rtrn.l15_data_3        = axi_rd_data[3];

  // we are always ready to consume packets unconditionally,
  // but we give prio to read responses below
  axi_rd_rdy                 = 1'b1;
  axi_wr_rdy                 = 1'b1;
  
  //////////////////////////////////////
  if (axi_rd_valid) begin
    // we give prio to read responses
    axi_wr_rdy                 = 1'b0;
    l15_rtrn.l15_val           = 1'b1;
    l15_rtrn.l15_threadid      = axi_rd_id_out>>3;
    l15_rtrn.l15_noncacheable  = axi_rd_id_out[0];
    unique case(tx_t'(axi_rd_id_out[2:1]))
      STD:   l15_rtrn.l15_returntype = serpent_cache_pkg::L15_LOAD_RET;
      LRSC:  l15_rtrn.l15_returntype = serpent_cache_pkg::L15_CPX_RESTYPE_ATOMIC_RES;
      ATOP:  l15_rtrn.l15_returntype = serpent_cache_pkg::L15_CPX_RESTYPE_ATOMIC_RES;
      IFILL: begin 
        l15_rtrn.l15_returntype = serpent_cache_pkg::L15_IFILL_RET;
        l15_rtrn.l15_f4b        = axi_rd_id_out[0];
      end  
    endcase
  //////////////////////////////////////  
  end else if (axi_wr_valid) begin
    l15_rtrn.l15_val           = 1'b1; 
    l15_rtrn.l15_threadid      = axi_wr_id_out>>3;
    l15_rtrn.l15_noncacheable  = axi_wr_id_out[0];
    unique case(tx_t'(axi_wr_id_out[2:1]))
      STD:   l15_rtrn.l15_returntype = serpent_cache_pkg::L15_ST_ACK;
      ATOP:  l15_rtrn.l15_val        = 1'b0; // silently drop atop write response, as we only rely on the read response here
      LRSC:  begin 
        l15_rtrn.l15_returntype = serpent_cache_pkg::L15_CPX_RESTYPE_ATOMIC_RES;
        // encode success 
        l15_rtrn.l15_data_0 = (axi_wr_exokay) ? '0 : '1;
      end
      default: ;
    endcase
  end
  //////////////////////////////////////
end

always_ff @(posedge clk_i or negedge rst_ni) begin : p_regs
  if(~rst_ni) begin
    rd_pending_q <= '0;
  end else begin
    rd_pending_q <= rd_pending_d;
  end
end


axi_adapter2 #(
  .DATA_WORDS      ( AxiNumWords     ),
  .AXI_ID_WIDTH    ( AxiIdWidth      )
) i_axi_adapter (
  .clk_i           ( clk_i             ),
  .rst_ni          ( rst_ni            ),
  .rd_req_i        ( axi_rd_req        ),
  .rd_gnt_o        ( axi_rd_gnt        ),
  .rd_addr_i       ( axi_rd_addr       ),
  .rd_blen_i       ( axi_rd_blen       ),
  .rd_size_i       ( axi_rd_size       ),
  .rd_id_i         ( axi_rd_id_in      ),
  .rd_rdy_i        ( axi_rd_rdy        ),
  .rd_lock_i       ( axi_rd_lock       ),
  .rd_valid_o      ( axi_rd_valid      ),
  .rd_data_o       ( axi_rd_data       ),
  .rd_id_o         ( axi_rd_id_out     ),
  .rd_exokay_o     ( axi_rd_exokay     ),    
  .wr_req_i        ( axi_wr_req        ),
  .wr_gnt_o        ( axi_wr_gnt        ),
  .wr_addr_i       ( axi_wr_addr       ),
  .wr_data_i       ( axi_wr_data       ),
  .wr_be_i         ( axi_wr_be         ),
  .wr_blen_i       ( axi_wr_blen       ),
  .wr_size_i       ( axi_wr_size       ),
  .wr_id_i         ( axi_wr_id_in      ),
  .wr_lock_i       ( axi_wr_lock       ),
  .wr_atop_i       ( axi_wr_atop       ),
  .wr_rdy_i        ( axi_wr_rdy        ),
  .wr_valid_o      ( axi_wr_valid      ),
  .wr_id_o         ( axi_wr_id_out     ),
  .wr_exokay_o     ( axi_wr_exokay     ),
  .axi_req_o       ( axi_req_o         ),
  .axi_resp_i      ( axi_resp_i        )
);

`endif


///////////////////////////////////////////////////////
// assertions
///////////////////////////////////////////////////////

//pragma translate_off
`ifndef VERILATOR

`ifdef AXI64_CACHE_PORTS
  initial begin
    assert (AxiIdWidth >= $clog2(serpent_cache_pkg::DCACHE_MAX_TX)+3) else
      $fatal(1,$psprintf("[l1 cache] AXI ID must be at least %01d bit wide", $clog2(serpent_cache_pkg::DCACHE_MAX_TX)+3));
    assert (ariane_pkg::ICACHE_LINE_WIDTH <= ariane_pkg::DCACHE_LINE_WIDTH) else 
      $fatal(1,"[l1 cache] AXI shim currently assumes that the icache line size >= dcache line size");
  end

  lr_exokay: assert property (
  @(posedge clk_i) disable iff (~rst_ni) axi_rd_valid |-> axi_rd_rdy |-> tx_t'(axi_rd_id_out[2:1]) == LRSC |-> axi_rd_exokay)
    else $warning("[l1 cache] LR did not receive an exokay, indicating that atomics are not supported");
  
`endif

a_invalid_instruction_fetch: assert property (
  @(posedge clk_i) disable iff (~rst_ni) icache_dreq_o.valid |-> (|icache_dreq_o.data) !== 1'hX)
else $warning(1,"[l1 dcache] reading invalid instructions: vaddr=%08X, data=%08X",
  icache_dreq_o.vaddr, icache_dreq_o.data);

a_invalid_write_data: assert property (
  @(posedge clk_i) disable iff (~rst_ni) dcache_req_ports_i[2].data_req |-> |dcache_req_ports_i[2].data_be |-> (|dcache_req_ports_i[2].data_wdata) !== 1'hX)
else $warning(1,"[l1 dcache] writing invalid data: paddr=%016X, be=%02X, data=%016X",
  {dcache_req_ports_i[2].address_tag, dcache_req_ports_i[2].address_index}, dcache_req_ports_i[2].data_be, dcache_req_ports_i[2].data_wdata);


for(genvar j=0; j<2; j++) begin : g_assertion
  a_invalid_read_data: assert property (
    @(posedge clk_i) disable iff (~rst_ni) dcache_req_ports_o[j].data_rvalid |-> (|dcache_req_ports_o[j].data_rdata) !== 1'hX)
  else $warning(1,"[l1 dcache] reading invalid data on port %01d: data=%016X",
    j, dcache_req_ports_o[j].data_rdata);
end
`endif
//pragma translate_on


endmodule // serpent_cache_subsystem
