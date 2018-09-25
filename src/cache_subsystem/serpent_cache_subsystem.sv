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

`ifdef AXI64_CACHE_PORTS
   // memory side
   AXI_BUS.Master                         icache_data_if,          // I$ refill port
   AXI_BUS.Master                         dcache_data_if,          // D$ refill port
   AXI_BUS.Master                         dcache_bypass_if         // bypass axi port (disabled D$ or uncacheable access)
`else
   // L15 (memory side)   
   output logic                           l15_val_o,
   input  logic                           l15_ack_i,
   input  logic                           l15_header_ack_i,
   output l15_req_t                       l15_data_o,
          
   input  logic                           l15_val_i,
   output logic                           l15_req_ack_o,
   input  l15_rtrn_t                      l15_rtrn_i
`endif   
   // TODO: interrupt interface
);

   logic icache_adapter_data_req, adapter_icache_data_ack, adapter_icache_rtrn_vld;
   serpent_cache_pkg::icache_req_t  icache_adapter;
   serpent_cache_pkg::icache_rtrn_t adapter_icache;

   serpent_icache #(
`ifdef AXI64_CACHE_PORTS
      .AXI64BIT_COMPLIANT ( 1'b1                    ),
`endif
      .NC_ADDR_BEGIN      ( CACHE_START_ADDR        ),
      .NC_ADDR_GE_LT      ( 0                       ) // todo: make compliant with openpiton
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

   // decreasing priority
   // Port 0: PTW
   // Port 1: Load Unit
   // Port 2: Store Unit
   std_nbdcache #(
      .CACHE_START_ADDR ( CACHE_START_ADDR )
   ) i_nbdcache (
      .clk_i              ( clk_i                  ),
      .rst_ni             ( rst_ni                 ),
      .enable_i           ( dcache_enable_i        ),
      .flush_i            ( dcache_flush_i         ),
      .flush_ack_o        ( dcache_flush_ack_o     ),
      .miss_o             ( dcache_miss_o          ),
      .data_if            ( dcache_data_if         ),
      .bypass_if          ( dcache_bypass_if       ),
      .amo_req_i          ( dcache_amo_req_i       ),
      .amo_resp_o         ( dcache_amo_resp_o      ),
      .req_ports_i        ( dcache_req_ports_i     ),
      .req_ports_o        ( dcache_req_ports_o     )
   );


   // logic dcache_adapter_data_req, adapter_dcache_data_ack, adapter_dcache_rtrn_vld;
   // dcache_req_t  dcache_adapter;
   // dcache_rtrn_t adapter_dcache;

   // // decreasing priority
   // // Port 0: PTW
   // // Port 1: Load Unit
   // // Port 2: Store Unit
   // serpent_dcache #(
   //    .CACHE_START_ADDR ( CACHE_START_ADDR )
   // ) i_serpent_dcache (
   //    .clk_i              ( clk_i                   ),
   //    .rst_ni             ( rst_ni                  ),
   //    .enable_i           ( dcache_enable_i         ),
   //    .flush_i            ( dcache_flush_i          ),
   //    .flush_ack_o        ( dcache_flush_ack_o      ),
   //    .miss_o             ( dcache_miss_o           ),
   //    .amo_commit_i       ( dcache_amo_commit_i     ),
   //    .amo_valid_o        ( dcache_amo_valid_o      ),
   //    .amo_result_o       ( dcache_amo_result_o     ),
   //    .amo_flush_i        ( dcache_amo_flush_i      ),
   //    .req_ports_i        ( dcache_req_ports_i      ),
   //    .req_ports_o        ( dcache_req_ports_o      ),
   //    .mem_rtrn_vld_i     ( adapter_dcache_rtrn_vld ),
   //    .mem_rtrn_i         ( adapter_dcache          ),
   //    .mem_data_req_o     ( dcache_adapter_data_req ),
   //    .mem_data_ack_i     ( adapter_dcache_data_ack ),
   //    .mem_data_o         ( dcache_adapter          )
   // );


// different memory plumbing
`ifdef AXI64_CACHE_PORTS

   // cannot handle invalidations atm
   assign adapter_icache.rtype = ICACHE_IFILL_ACK;
   assign adapter_icache.inv   = '0;
   assign adapter_icache.nc    = icache_adapter.nc;
   assign adapter_icache.tid   = '0;
   assign adapter_icache.f4b   = icache_adapter.nc;

   std_cache_pkg::req_t icache_axi_req_type;
   assign icache_axi_req_type  = ( icache_adapter.nc ) ? std_cache_pkg::SINGLE_REQ : std_cache_pkg::CACHE_LINE_REQ;
   
   axi_adapter #(
      .DATA_WIDTH ( ICACHE_LINE_WIDTH )
   ) i_axi_adapter (
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
      .axi                  ( icache_data_if          )
   );

`else 

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
      .l15_val_o          ( l15_val_o               ),
      .l15_ack_i          ( l15_ack_i               ),
      .l15_header_ack_i   ( l15_header_ack_i        ),
      .l15_data_o         ( l15_port_o              ),
      .l15_val_i          ( l15_val_i               ),
      .l15_req_ack_o      ( l15_req_ack_o           ),
      .l15_rtrn_i         ( l15_port_i              )
      );

`endif

endmodule // serpent_cache_subsystem
