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
// Author: Michael Schaffner, ETH Zurich
// Date: 19.03.2017
// Description: Ariane Top-level wrapper to break out SV structs to logic vectors.

// default to AXI64 cache ports if not using the
// serpent PULP extension
`ifndef SERPENT_PULP
`ifndef AXI64_CACHE_PORTS
  `define AXI64_CACHE_PORTS
`endif
`endif

module ariane_verilog_wrap #(
  parameter bit          SWAP_ENDIANESS   = 0,             // swap endianess in l15 adapter
  parameter bit          CACHE_LOW_REGION = 0,             // cached region is below CACHE_START_ADDR
  parameter logic [63:0] CACHE_START_ADDR = 64'h8000_0000  // address on which to decide whether the request is cache-able or not
) (
  input                       clk_i,
  input                       reset_l,      // this is an openpiton-specific name, do not change (hier. paths in TB use this)
  // Core ID, Cluster ID and boot address are considered more or less static
  input  [63:0]               boot_addr_i,  // reset boot address
  input  [63:0]               hart_id_i,    // hart id in a multicore environment (reflected in a CSR)
  // Interrupt inputs
  input  [1:0]                irq_i,        // level sensitive IR lines, mip & sip (async)
  input                       ipi_i,        // inter-processor interrupts (async)
  // Timer facilities
  input                       time_irq_i,   // timer interrupt in (async)
  input                       debug_req_i,  // debug request (async)

`ifdef AXI64_CACHE_PORTS
  // AXI (memory side)
  output [$size(ariane_axi::req_t)-1:0]             axi_req_o,
  input  [$size(ariane_axi::resp_t)-1:0]            axi_resp_i
`else
  // L15 (memory side)
  output [$size(serpent_cache_pkg::l15_req_t)-1:0]  l15_req_o,
  input  [$size(serpent_cache_pkg::l15_rtrn_t)-1:0] l15_rtrn_i
`endif
 );

// assign bitvector to packed struct and vice versa
`ifdef AXI64_CACHE_PORTS
  ariane_axi::req_t             axi_req;
  ariane_axi::resp_t            axi_resp;

  assign axi_req_o = axi_req;
  assign axi_resp  = axi_resp_i;
`else
  // L15 (memory side)
  serpent_cache_pkg::l15_req_t  l15_req;
  serpent_cache_pkg::l15_rtrn_t l15_rtrn;

  assign l15_req_o = l15_req;
  assign l15_rtrn  = l15_rtrn_i;
`endif

  logic rst_n, irq_received;

`ifdef VERILATOR

  assign irq_received = 1'b1;

`else

  // simulation hack, need to wait until interrupt arrives.
  // TODO: find a clean solution for this
  initial begin
    irq_received <= '0;

    repeat(100) @(posedge clk_i);

    while(!reset_l) @(posedge clk_i);

    while(l15_rtrn.l15_returntype != serpent_cache_pkg::L15_INT_RET) @(posedge clk_i);

    irq_received <= 1;
  end

`endif


  assign rst_n = reset_l & irq_received;



  ariane #(
    .SWAP_ENDIANESS   ( SWAP_ENDIANESS   ),
    .CACHE_LOW_REGION ( CACHE_LOW_REGION ),
    .CACHE_START_ADDR ( CACHE_START_ADDR )
  ) ariane (
    .clk_i                   ,
    .rst_ni      ( rst_n  ),
    .boot_addr_i             ,
    .hart_id_i               ,
    .irq_i                   ,
    .ipi_i                   ,
    .time_irq_i              ,
    .debug_req_i             ,
`ifdef AXI64_CACHE_PORTS
    .axi_req_o   ( axi_req  ),
    .axi_resp_i  ( axi_resp )
`else
    .l15_req_o   ( l15_req  ),
    .l15_rtrn_i  ( l15_rtrn )
`endif
  );

endmodule // ariane_verilog_wrap
