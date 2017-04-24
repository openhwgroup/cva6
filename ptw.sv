
// Author: David Schaffenrath, TU Graz - Florian Zaruba, ETH Zurich
// Date: 24.4.2017
// Description: Hardware-PTW
//
//
// Copyright (C) 2017 ETH Zurich, University of Bologna
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
import ariane_pkg::*;

module ptw (
    input logic        clk_i,    // Clock
    input logic        rst_ni,   // Asynchronous reset active low

    input logic [63:0] rdata_i
);

    pte_t ptw_pte_i;
    assign ptw_pte_i = pte_t'(rdata_i);

    enum logic[3:0] {
      PTW_READY,
      PTW_WAIT_GRANT,
      PTW_PTE_LOOKUP,
      PTW_PROPAGATE_ERROR
    } ptw_state_q, ptw_state_n;

    logic ptw_active = (ptw_state_q != PTW_READY);

    struct packed {
        // logic r; don't care
        // logic w; don't care
        // logic x; If page isn't executable it isn't put in the instruction TLB
        logic u;
        logic g;
        logic[PPN4K_WIDTH-1:0] ppn;
    } itlb_content, itlb_update_content;

    struct packed {
         // logic r; If page isn't readable it isn't put in the data TLB (unless it
         //          is executable and the MXR flag is set)
        logic x_only; // Because of the MXR flag we need an indication if the page
                      // is actually not readable, but executable
        logic w;
        logic u;
        logic g;
        logic[PPN4K_WIDTH-1:0] ppn;
    } dtlb_content, dtlb_update_content;

    always_comb begin
        itlb_update_content = '{
            u: ptw_pte_i.u,
            g: ptw_pte_i.g,
            ppn: ptw_pte_i.ppn[37:0]
        };
        dtlb_update_content = '{
            x_only: ptw_pte_i.x & ~ptw_pte_i.r,
            w: ptw_pte_i.w,
            u: ptw_pte_i.u,
            g: ptw_pte_i.g,
            ppn: ptw_pte_i.ppn[37:0]
        };
    end
    //-------------------
    // Page table walker
    //-------------------

    // A virtual address va is translated into a physical address pa as follows:
    // 1. Let a be sptbr.ppn × PAGESIZE, and let i = LEVELS-1. (For Sv32,
    //    PAGESIZE=2^12 and LEVELS=2.)
    // 2. Let pte be the value of the PTE at address a+va.vpn[i]×PTESIZE. (For
    //    Sv32, PTESIZE=4.)
    // 3. If pte.v = 0, or if pte.r = 0 and pte.w = 1, stop and raise an access
    //    exception.
    // 4. Otherwise, the PTE is valid. If pte.r = 1 or pte.x = 1, go to step 5.
    //    Otherwise, this PTE is a pointer to the next level of the page table.
    //    Let i=i-1. If i < 0, stop and raise an access exception. Otherwise, let
    //    a = pte.ppn × PAGESIZE and go to step 2.
    // 5. A leaf PTE has been found. Determine if the requested memory access
    //    is allowed by the pte.r, pte.w, and pte.x bits. If not, stop and
    //    raise an access exception. Otherwise, the translation is successful.
    //    Set pte.a to 1, and, if the memory access is a store, set pte.d to 1.
    //    The translated physical address is given as follows:
    //      - pa.pgoff = va.pgoff.
    //      - If i > 0, then this is a superpage translation and
    //        pa.ppn[i-1:0] = va.vpn[i-1:0].
    //      - pa.ppn[LEVELS-1:i] = pte.ppn[LEVELS-1:i].
    always_comb begin : ptw
        unique case (ptw_state_q)

            PTW_READY: begin

            end

            PTW_WAIT_GRANT: begin

            end

            PTW_PTE_LOOKUP: begin

            end

            PTW_PROPAGATE_ERROR: begin

            end

            default:
                ptw_state_n = PTW_READY;

        endcase // ptw_state_q
    end


endmodule