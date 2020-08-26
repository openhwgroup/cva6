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
// Description: simple emulation layer for the tlb.
//


module tlb_emul import ariane_pkg::*; import wt_cache_pkg::*; #(
  parameter TlbRandHitRate = 10 //in percent
) (
  input logic            clk_i,
  input logic            rst_ni,

  input logic            tlb_rand_en_i,
  input logic            exception_en_i,
  input logic [63:0]     tlb_offset_i,

  // icache interface
  input  icache_areq_o_t req_i,
  output icache_areq_i_t req_o
);

logic tlb_ready_d, tlb_ready_q;

always_ff @(posedge clk_i or negedge rst_ni) begin : p_tlb_rand
  automatic bit ok  = 0;
  automatic int rnd = 0;

  assert(TlbRandHitRate<=100 && TlbRandHitRate>=0) else
    $fatal("TlbRandHitRate must be a percentage");

  if(~rst_ni) begin
    tlb_ready_q <= '0;
  end else begin
    if (tlb_rand_en_i) begin
      ok = randomize(rnd) with {rnd > 0; rnd <= 100;};
      if(rnd < TlbRandHitRate) begin
        tlb_ready_q = '1;
      end else
        tlb_ready_q = '0;
    end else begin
      tlb_ready_q = '1;
    end
  end
end

// TODO: add random exceptions
always_comb begin : proc_tlb
  req_o.fetch_valid     = '0;
  req_o.fetch_paddr     = '0;
  req_o.fetch_exception = '0;

  if (req_i.fetch_req && tlb_ready_q) begin
    req_o.fetch_valid = 1'b1;
    req_o.fetch_paddr = req_i.fetch_vaddr + tlb_offset_i;
  end
end

endmodule // tlb_emul
