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
  parameter int unsigned AXI_ID_WIDTH     = 10,
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
    // AMOs
    input  amo_req_t                       amo_req_i,
    output amo_resp_t                      amo_resp_o,
    // D$
    // Cache management
    input  logic                           dcache_enable_i,        // from CSR
    input  logic                           dcache_flush_i,         // high until acknowledged
    output logic                           dcache_flush_ack_o,     // send a single cycle acknowledge signal when the cache is flushed
    output logic                           dcache_miss_o,          // we missed on a ld/st
    output logic                           wbuffer_empty_o,        // statically set to 1, as there is no wbuffer in this cache system
    // Request ports
    input  dcache_req_i_t   [2:0]          dcache_req_ports_i,     // to/from LSU
    output dcache_req_o_t   [2:0]          dcache_req_ports_o,     // to/from LSU
    // memory side
    AXI_BUS.Master                         icache_data_if,          // I$ refill port
    AXI_BUS.Master                         dcache_data_if,          // D$ refill port
    AXI_BUS.Master                         dcache_bypass_if         // bypass axi port (disabled D$ or uncacheable access)
);
  
  assign wbuffer_empty_o = 1'b1;

   std_icache #(
   ) i_icache (
       .clk_i    ( clk_i                 ),
       .rst_ni   ( rst_ni                ),
       .flush_i  ( icache_flush_i        ),
       .en_i     ( icache_en_i           ),
       .miss_o   ( icache_miss_o         ),
       .areq_i   ( icache_areq_i         ),
       .areq_o   ( icache_areq_o         ),
       .dreq_i   ( icache_dreq_i         ),
       .dreq_o   ( icache_dreq_o         ),
       .axi      ( icache_data_if        )
   );

   // decreasing priority
   // Port 0: PTW
   // Port 1: Load Unit
   // Port 2: Store Unit
   std_nbdcache #(
      .AXI_ID_WIDTH     ( AXI_ID_WIDTH     ),
      .CACHE_START_ADDR ( CACHE_START_ADDR )
   ) i_nbdcache (
      .clk_i        ( clk_i                  ),
      .rst_ni       ( rst_ni                 ),
      .enable_i     ( dcache_enable_i        ),
      .flush_i      ( dcache_flush_i         ),
      .flush_ack_o  ( dcache_flush_ack_o     ),
      .miss_o       ( dcache_miss_o          ),
      .data_if      ( dcache_data_if         ),
      .bypass_if    ( dcache_bypass_if       ),
      .req_ports_i  ( dcache_req_ports_i     ),
      .req_ports_o  ( dcache_req_ports_o     ),
      .amo_req_i    ( amo_req_i              ),
      .amo_resp_o   ( amo_resp_o             )
   );


///////////////////////////////////////////////////////
// assertions
///////////////////////////////////////////////////////


//pragma translate_off
`ifndef VERILATOR

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
    
`endif
//pragma translate_on


endmodule // std_cache_subsystem
