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
// Author: Michael Schaffner <schaffner@iis.ee.ethz.ch>, ETH Zurich
// Date: 15.08.2018
// Description: simple emulation layer for the tlb.
//

import ariane_pkg::*;
import piton_cache_pkg::*;

module tlb_emul #(
    parameter TLB_RAND_HIT_RATE = 10 //in percent
)(

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

    assert(TLB_RAND_HIT_RATE<=100 && TLB_RAND_HIT_RATE>=0) else
        $fatal("TLB_RAND_HIT_RATE must be a percentage");

    if(~rst_ni) begin
        tlb_ready_q <= '0;
    end else begin
        if (tlb_rand_en_i) begin
            ok = randomize(rnd) with {rnd > 0; rnd <= 100;};
            if(rnd < TLB_RAND_HIT_RATE) begin
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
