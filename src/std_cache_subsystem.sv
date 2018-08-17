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
// Description: Standard Ariane cache subsystem with instruction cache and 
//              write-back data cache.

import ariane_pkg::*;
import std_cache_pkg::*;

module std_cache_subsystem #(
   parameter logic [63:0] CACHE_START_ADDR = 64'h4000_0000
)(   
   input logic                            clk_i,
   input logic                            rst_ni,
          
   // I$
   input  logic                           icache_flush_i,         // flush the icache, flush and kill have to be asserted together
   input  logic                           icache_fetch_enable_i,  // the core should fetch instructions
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
   input  logic                           dcache_amo_commit_i,    // commit atomic memory operation
   output logic                           dcache_amo_valid_o,     // we have a valid AMO result
   output logic [63:0]                    dcache_amo_result_o,    // result of atomic memory operation
   input  logic                           dcache_amo_flush_i,     // forget about AMO
   // Request ports
   input  dcache_req_i_t   [2:0]          dcache_req_ports_i,     // to/from LSU
   output dcache_req_o_t   [2:0]          dcache_req_ports_o,     // to/from LSU

   // memory side
   AXI_BUS.Master                         icache_data_if,          // I$ refill port
   AXI_BUS.Master                         dcache_data_if,          // D$ refill port
   AXI_BUS.Master                         dcache_bypass_if         // bypass axi port (disabled D$ or uncacheable access)
);


   icache #(
   ) i_icache (
      .clk_i             ( clk_i                 ),
      .rst_ni            ( rst_ni                ),
      .flush_i           ( icache_flush_i        ),
      .fetch_enable_i    ( icache_fetch_enable_i ),
      .miss_o            ( icache_miss_o         ),
      .areq_i            ( icache_areq_i         ),
      .areq_o            ( icache_areq_o         ),
      .dreq_i            ( icache_dreq_i         ),
      .dreq_o            ( icache_dreq_o         ),
      .axi               ( icache_data_if        )
   );


   // decreasing priority
   // Port 0: PTW
   // Port 1: Load Unit
   // Port 2: Store Unit
   nbdcache #(
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
      .amo_commit_i       ( dcache_amo_commit_i    ),
      .amo_valid_o        ( dcache_amo_valid_o     ),
      .amo_result_o       ( dcache_amo_result_o    ),
      .amo_flush_i        ( dcache_amo_flush_i     ),
      .req_ports_i        ( dcache_req_ports_i     ),
      .req_ports_o        ( dcache_req_ports_o     )
   );


endmodule // std_cache_subsystem