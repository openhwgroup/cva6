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
// Date: 19.03.2017
// Description: Ariane Top-level wrapper to break out SV structs to logic vectors.

// default to AXI64 cache ports if not using the
// serpent PULP extension
`ifndef PITON_ARIANE
`ifndef AXI64_CACHE_PORTS
  `define AXI64_CACHE_PORTS
`endif
`endif

module ariane_verilog_wrap #(
  parameter bit          SwapEndianess = 1,                // swap endianess in l15 adapter
  parameter logic [63:0] CachedAddrEnd = 64'h80_0000_0000, // end of cached region
  parameter logic [63:0] CachedAddrBeg = 64'h00_8000_0000  // begin of cached region
) (
  input                       clk_i,
  input                       reset_l,      // this is an openpiton-specific name, do not change (hier. paths in TB use this)
  output                      spc_grst_l,   // this is an openpiton-specific name, do not change (hier. paths in TB use this)
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
  serpent_cache_pkg::l15_req_t  l15_req, l15_req_remapped;
  serpent_cache_pkg::l15_rtrn_t l15_rtrn;

  always_comb begin : p_remap
    l15_req_remapped = l15_req;
    if (l15_req.l15_address < 64'h1000) begin
      l15_req_remapped.l15_address = l15_req.l15_address + 64'hfff1000000;
    end
  end

  assign l15_req_o = l15_req_remapped;
  assign l15_rtrn  = l15_rtrn_i;
`endif

  // // this is a workaround since interrupts are not fully supported yet.
  // // the logic below catches the initial wake up interrupt that enables the cores.
  // logic wake_up_d, wake_up_q;
  // logic rst_n;

  // assign wake_up_d = wake_up_q || ((l15_rtrn.l15_returntype == serpent_cache_pkg::L15_INT_RET) && l15_rtrn.l15_val);

  // always_ff @(posedge clk_i or negedge reset_l) begin : p_regs
  //   if(~reset_l) begin
  //     wake_up_q <= 0;
  //   end else begin
  //     wake_up_q <= wake_up_d;
  //   end
  // end

  // // reset gate this
  // assign rst_n = wake_up_q & reset_l;

  // this is a workaround,
  // we basically wait for 32k cycles such that the SRAMs in openpiton can initialize
  // 128KB..8K cycles
  // 256KB..16K cycles
  // etc, so this should be enough for 512k per tile

  logic [15:0] wake_up_cnt_d, wake_up_cnt_q;
  logic rst_n;

  assign wake_up_cnt_d = (wake_up_cnt_q[$high(wake_up_cnt_q)]) ? wake_up_cnt_q : wake_up_cnt_q + 1;

  always_ff @(posedge clk_i or negedge reset_l) begin : p_regs
    if(~reset_l) begin
      wake_up_cnt_q <= 0;
    end else begin
      wake_up_cnt_q <= wake_up_cnt_d;
    end
  end

  // reset gate this
  assign rst_n = wake_up_cnt_q[$high(wake_up_cnt_q)] & reset_l;

  // reset_synchronizer #(
  //    .NUM_REGS(2)
  // ) i_sync (
  //    .clk_i   ( clk_i      ),
  //    .rst_ni  ( rst_n      ),
  //    .tmode_i ( 1'b0       ),
  //    .rst_no  ( spc_grst_l )
  // );

  synchronizer i_sync (
    .clk         ( clk_i      ),
    .presyncdata ( rst_n      ),
    .syncdata    ( spc_grst_l )
  );

  ariane #(
    .SwapEndianess ( SwapEndianess ),
    .CachedAddrEnd ( CachedAddrEnd ),
    .CachedAddrBeg ( CachedAddrBeg )
  ) ariane (
    .clk_i       ( clk_i      ),
    .rst_ni      ( spc_grst_l ),
    .boot_addr_i              ,
    .hart_id_i                ,
    .irq_i                    ,
    .ipi_i                    ,
    .time_irq_i               ,
    .debug_req_i              ,
`ifdef AXI64_CACHE_PORTS
    .axi_req_o   ( axi_req   ),
    .axi_resp_i  ( axi_resp  )
`else
    .l15_req_o   ( l15_req   ),
    .l15_rtrn_i  ( l15_rtrn  )
`endif
  );

endmodule // ariane_verilog_wrap
