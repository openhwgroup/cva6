// Copyright (c) 2018 ETH Zurich, University of Bologna
// All rights reserved.
//
// This code is under development and not yet released to the public.
// Until it is released, the code is under the copyright of ETH Zurich and
// the University of Bologna, and may contain confidential and/or unpublished
// work. Any reuse/redistribution is strictly forbidden without written
// permission from ETH Zurich.
//
// Bug fixes and contributions will eventually be released under the
// SolderPad open hardware license in the context of the PULP platform
// (http://www.pulp-platform.org), under the copyright of ETH Zurich and the
// University of Bologna.
//
// Author: Florian Zaruba    <zarubaf@iis.ee.ethz.ch>, ETH Zurich
//         Michael Schaffner <schaffner@iis.ee.ethz.ch>, ETH Zurich
// Date: 15.08.2018
// Description: Ariane cache subsystem that is compatible with the OpenPiton
//              coherent memory system.
//
//              Define SERPENT_PULP if you want to use this cache.
//              Define AXI64_CACHE_PORTS if you want to use this cache
//              with a standard 64bit AXI interace instead of the openpiton
//              L1.5 interface.

import ariane_pkg::*;
import serpent_cache_pkg::*;

module serpent_cache_subsystem #(
// `ifdef AXI64_CACHE_PORTS
   parameter int unsigned AXI_ID_WIDTH     = 10,
// `endif
   parameter logic [63:0] CACHE_START_ADDR = 64'h4000_0000
)(
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
    output ariane_axi::req_t              axi_req_o,
    input  ariane_axi::resp_t             axi_resp_i
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

   serpent_icache #(
`ifdef AXI64_CACHE_PORTS
      .AXI64BIT_COMPLIANT ( 1'b1                    ),
      .NC_ADDR_GE_LT      ( 0                       ),
`endif
      .NC_ADDR_BEGIN      ( CACHE_START_ADDR        )
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
`ifdef AXI64_CACHE_PORTS
      .NC_ADDR_GE_LT   ( 0                       ), // std config is for openpiton, where the upper memory region is NC
`endif
      .NC_ADDR_BEGIN   ( CACHE_START_ADDR        )
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
      .l15_req_o          ( l15_req_o               ),
      .l15_rtrn_i         ( l15_port_i              )
      );



// different memory plumbing
`ifdef AXI64_CACHE_PORTS

   // cannot handle invalidations ATM
   assign adapter_icache.rtype = ICACHE_IFILL_ACK;
   assign adapter_icache.inv   = '0;
   assign adapter_icache.nc    = icache_adapter.nc;
   assign adapter_icache.tid   = '0;
   assign adapter_icache.f4b   = icache_adapter.nc;

   std_cache_pkg::req_t icache_axi_req_type;
   assign icache_axi_req_type  = ( icache_adapter.nc ) ? std_cache_pkg::SINGLE_REQ : std_cache_pkg::CACHE_LINE_REQ;

   axi_adapter #(
      .DATA_WIDTH           ( ICACHE_LINE_WIDTH       ),
      .AXI_ID_WIDTH         ( AXI_ID_WIDTH            )
   ) i_icache_axi_adapter (
      .clk_i                ( clk_i                   ),
      .rst_ni               ( rst_ni                  ),
      .req_i                ( icache_adapter_data_req ),
      .type_i               ( icache_axi_req_type     ),
      .gnt_o                ( adapter_icache_data_ack ),
      .gnt_id_o             (                         ),
      .addr_i               ( icache_adapter.paddr    ),
      .we_i                 ( '0                      ),
      .wdata_i              ( '0                      ),
      .be_i                 ( '0                      ),
      .size_i               ( 2'b11                   ),// always request in multiples of 64bit
      .id_i                 ( '0                      ),
      .valid_o              ( adapter_icache_rtrn_vld ),
      .rdata_o              ( adapter_icache.data     ),
      .id_o                 (                         ),
      .critical_word_o      (                         ),
      .critical_word_valid_o(                         ),
      .axi_req_o            ( axi_data_o              ),
      .axi_resp_i           ( axi_data_i              )
   );

   std_cache_pkg::req_t dcache_axi_req_type;
   logic [DCACHE_LINE_WIDTH-1:0] dcache_axi_wdata;
   logic dcache_axi_we;
   logic [DCACHE_LINE_WIDTH/8-1:0] dcache_axi_be;
   logic [1:0] dcache_axi_size;
   logic [63:0] dcache_axi_paddr;
   // AXI IDs are 10 wide here
   logic [AXI_ID_WIDTH-1:0] dcache_axi_id, axi_dcache_id;

   // encode NC, RD, and TX ID into AXI ID field
   // dcache is aware of the fact that transactions with different IDs can overtake each other in the
   // interconnect, and issues the transactions accordingly. so this is safe.
   assign dcache_axi_req_type  = ( dcache_adapter.size[2] ) ? std_cache_pkg::CACHE_LINE_REQ : std_cache_pkg::SINGLE_REQ;
   assign dcache_axi_size      = ( dcache_adapter.size[2] ) ? 2'b11 : dcache_adapter.size;
   assign dcache_axi_we        = ( dcache_adapter.rtype == serpent_cache_pkg::DCACHE_STORE_REQ );
   assign dcache_axi_id        = {dcache_adapter.tid, dcache_adapter.nc, dcache_axi_we};
   assign dcache_axi_wdata     = dcache_adapter.data;
   assign dcache_axi_be        = ( dcache_axi_we ) ? serpent_cache_pkg::toByteEnable8(dcache_adapter.paddr[2:0], dcache_adapter.size) : '0;
   assign dcache_axi_paddr     = dcache_adapter.paddr;

   // cannot handle invalidations and atomics ATM
   assign adapter_dcache.inv   = '0;
   assign adapter_dcache.rtype = (axi_dcache_id[0]) ? serpent_cache_pkg::DCACHE_STORE_ACK : serpent_cache_pkg::DCACHE_LOAD_ACK;
   assign adapter_dcache.nc    = axi_dcache_id[1];
   assign adapter_dcache.tid   = axi_dcache_id>>2;

   axi_adapter #(
      .DATA_WIDTH           ( DCACHE_LINE_WIDTH       ),
      .AXI_ID_WIDTH         ( AXI_ID_WIDTH            )
   ) i_dcache_axi_adapter (
      .clk_i                ( clk_i                   ),
      .rst_ni               ( rst_ni                  ),
      .req_i                ( dcache_adapter_data_req ),
      .type_i               ( dcache_axi_req_type     ),
      .gnt_o                ( adapter_dcache_data_ack ),
      .gnt_id_o             (                         ),
      .addr_i               ( dcache_axi_paddr        ),
      .we_i                 ( dcache_axi_we           ),
      .wdata_i              ( dcache_axi_wdata        ),
      .be_i                 ( dcache_axi_be           ),
      .size_i               ( dcache_axi_size         ),// always request in multiples of 64bit
      .id_i                 ( dcache_axi_id           ),
      .valid_o              ( adapter_dcache_rtrn_vld ),
      .rdata_o              ( adapter_dcache.data     ),
      .id_o                 ( axi_dcache_id           ),
      .critical_word_o      (                         ),
      .critical_word_valid_o(                         ),
      .axi_req_o            (                         ),
      .axi_resp_i           (  '0                     )
   );


`endif

///////////////////////////////////////////////////////
// assertions
///////////////////////////////////////////////////////


//pragma translate_off
`ifndef VERILATOR

`ifdef AXI64_CACHE_PORTS
   a_write_size: assert property (
      @(posedge clk_i) disable iff (~rst_ni) dcache_adapter_data_req |-> adapter_dcache_data_ack |-> dcache_axi_we |-> dcache_axi_req_type==std_cache_pkg::SINGLE_REQ)
         else $fatal(1,"[l1 cache] full cacheline stores not supported at the moment");

   a_paddr_align: assert property (
      @(posedge clk_i) disable iff (~rst_ni) dcache_adapter_data_req |-> adapter_dcache_data_ack |-> dcache_axi_req_type==std_cache_pkg::CACHE_LINE_REQ |-> dcache_axi_paddr[2:0] == 3'b000)
         else $fatal(1,"[l1 cache] CL address must be aligned");
`endif

   a_invalid_instruction_fetch: assert property (
       @(posedge clk_i) disable iff (~rst_ni) icache_dreq_o.valid |-> (|icache_dreq_o.data) !== 1'hX)
           else $warning(1,"[l1 dcache] reading invalid instructions: vaddr=%08X, data=%08X",
               icache_dreq_o.vaddr, icache_dreq_o.data);

   a_invalid_write_data: assert property (
       @(posedge clk_i) disable iff (~rst_ni) dcache_req_ports_i[2].data_req |-> |dcache_req_ports_i[2].data_be |-> (|dcache_req_ports_i[2].data_wdata) !== 1'hX)
           else $warning(1,"[l1 dcache] writing invalid data: paddr=%016X, be=%02X, data=%016X",
               {dcache_req_ports_i[2].address_tag, dcache_req_ports_i[2].address_index}, dcache_req_ports_i[2].data_be, dcache_req_ports_i[2].data_wdata);

   generate
      for(genvar j=0; j<2; j++) begin
         a_invalid_read_data: assert property (
            @(posedge clk_i) disable iff (~rst_ni) dcache_req_ports_o[j].data_rvalid |-> (|dcache_req_ports_o[j].data_rdata) !== 1'hX)
               else $warning(1,"[l1 dcache] reading invalid data on port %01d: data=%016X",
                  j, dcache_req_ports_o[j].data_rdata);
      end
   endgenerate

   initial begin
      assert (AXI_ID_WIDTH >= $clog2(serpent_cache_pkg::DCACHE_MAX_TX)+2) else
         $fatal(1,$psprintf("[l1 cache] AXI ID must be at least %01d bit wide", $clog2(serpent_cache_pkg::DCACHE_MAX_TX)+2));
   end
`endif
//pragma translate_on


endmodule // serpent_cache_subsystem
