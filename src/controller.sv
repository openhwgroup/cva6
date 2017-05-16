// Author: Florian Zaruba, ETH Zurich
// Date: 08.05.2017
// Description: Flush controller
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

module controller (
    input  logic            clk_i,    // Clock
    input  logic            rst_ni,   // Asynchronous reset active low

    output logic            flush_bp_o, // flush branch prediction data structures
    output logic            flush_unissued_instr_o,
    output logic            flush_scoreboard_o,
    output logic            flush_if_o,
    output logic            flush_id_o,
    output logic            flush_ex_o,

    input  logic            flush_ready_lsu_i, // we need to wait for this signal from LSU
    input  logic            flush_commit_i,    // flush request from commit stage in
    input  logic            flush_csr_i,
    input  branchpredict    resolved_branch_i
);
    assign flush_bp_o = 1'b0;

    always_comb begin : flush_ctrl
        flush_unissued_instr_o = 1'b0;
        flush_scoreboard_o     = 1'b0;
        flush_if_o             = 1'b0;
        // flush on mispredict
        if (resolved_branch_i.is_mispredict) begin
            flush_unissued_instr_o = 1'b1;
            flush_if_o             = 1'b1;
        end

    end
    // flush on exception
endmodule
