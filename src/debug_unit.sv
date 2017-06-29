// Author: Florian Zaruba, ETH Zurich
// Date: 29.06.2017
// Description: Memory Mapped Debug Unit
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

module debug_unit (
    input  logic                clk_i,    // Clock
    input  logic                rst_ni,  // Asynchronous reset active low

    input  logic [63:0]         commit_pc_i,
    input  logic                commit_ack_i,

    // External Debug Interface
    input  logic                debug_req_i,
    output logic                debug_gnt_o,
    output logic                debug_rvalid_o,
    input  logic [14:0]         debug_addr_i,
    input  logic                debug_we_i,
    input  logic [63:0]         debug_wdata_i,
    output logic [63:0]         debug_rdata_o,
    output logic                debug_halted_o,
    input  logic                debug_halt_i,
    input  logic                debug_resume_i

);

    // |    Address    |       Name      |                             Description                             |
    // |---------------|-----------------|---------------------------------------------------------------------|
    // | 0x0000-0x007F | Debug Registers | Always accessible, even when the core is running                    |
    // | 0x0400-0x047F | GPR (x0-x31)    | General Purpose Registers. Only accessible if the core is halted.   |
    // | 0x0500-0x05FF | FPR (f0-f31)    | Reserved. Not used in the Ariane.                                   |
    // | 0x2000-0x20FF | Debug Registers | Only accessible if the core is halted                               |
    // | 0x4000-0x7FFF | CSR             | Control and Status Registers. Only accessible if the core is halted |

    always_comb begin : debug_ctrl

        // ----------
        // Read
        // ----------
        // we've got a new read request
        if (debug_req_i && !debug_we_i) begin


        // ----------
        // Write
        // ----------
        end else if (debug_req_i) begin


        end
    end

    // --------------------
    // HW Breakpoints
    // --------------------

endmodule