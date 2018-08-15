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
   parameter logic [63:0] CACHE_START_ADDR = 64'h4000_0000,
   parameter int unsigned AXI_ID_WIDTH     = 10,
   parameter int unsigned AXI_USER_WIDTH   = 1
)  (   
   input logic                            clk_i,
   input logic                            rst_ni,
          
   // Icache
   //input  logic               flush_icache_i,     // instruction fence in
    


   // Dcache
   // Cache management
   input  logic                           dcache_enable_i,    // from CSR
   input  logic                           dcache_flush_i,     // high until acknowledged
   output logic                           dcache_flush_ack_o, // send a single cycle acknowledge signal when the cache is flushed
   output logic                           dcache_miss_o,      // we missed on a ld/st
   // Data cache refill port
   AXI_BUS.Master                         dcache_data_if,
   AXI_BUS.Master                         dcache_bypass_if,
   // AMO interface
   input  logic                           dcache_amo_commit_i, // commit atomic memory operation
   output logic                           dcache_amo_valid_o,  // we have a valid AMO result
   output logic [63:0]                    dcache_amo_result_o, // result of atomic memory operation
   input  logic                           dcache_amo_flush_i,  // forget about AMO
   // Request ports
   input  dcache_req_i_t   [2:0]          dcache_req_ports_i,  
   output dcache_req_o_t   [2:0]          dcache_req_ports_o
);


/*   icache #(
      .SET_ASSOCIATIVITY ( 4                    ),
      .CACHE_LINE_WIDTH  ( 128                  ),
      .FETCH_WIDTH       ( FETCH_WIDTH          )
   ) i_icache (
      .flush_i          ( flush_icache_i        ),
      .vaddr_i          ( fetch_vaddr           ), // 1st cycle
      .is_speculative_i ( fetch_is_speculative  ), // 1st cycle
      .data_o           ( icache_data_d         ),
      .req_i            ( icache_req            ),
      .kill_s1_i        ( kill_s1               ),
      .kill_s2_i        ( kill_s2               ),
      .ready_o          ( icache_ready          ),
      .valid_o          ( icache_valid_d        ),
      .ex_o             ( icache_ex_d           ),
      .is_speculative_o ( icache_speculative_d  ),
      .vaddr_o          ( icache_vaddr_d        ),
      .axi              ( axi                   ),
      .miss_o           ( l1_icache_miss_o      ),
      .*
   );
*/


   // decreasing priority
   // Port 0: PTW
   // Port 1: Load Unit
   // Port 2: Store Unit
   nbdcache #(
      .CACHE_START_ADDR ( CACHE_START_ADDR ),
      .AXI_ID_WIDTH     ( AXI_ID_WIDTH     ),
      .AXI_USER_WIDTH   ( AXI_USER_WIDTH   )
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