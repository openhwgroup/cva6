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

    output logic            flush_bp_o,             // flush branch prediction data structures
    output logic            flush_pcgen_o,          // flush PC Generation Stage
    output logic            flush_if_o,             // flush the IF stage
    output logic            flush_unissued_instr_o, // flush un-issued instructions of the scoreboard
    output logic            flush_id_o,             // flush ID stage
    output logic            flush_ex_o,             // flush EX stage

    input  exception        ex_i,               // we got an exception, flush the pipeline
    input  branchpredict    resolved_branch_i,  // we got a resolved branch, check if we need to flush the front-end
    input  logic            flush_csr_i         // we got an instruction which altered the CSR, flush the pipeline
);
    // flush branch prediction
    assign flush_bp_o = 1'b0;

    // ------------
    // Flush CTRL
    // ------------
    always_comb begin : flush_ctrl
        flush_pcgen_o          = 1'b0;
        flush_if_o             = 1'b0;
        flush_unissued_instr_o = 1'b0;
        flush_id_o             = 1'b0;
        flush_ex_o             = 1'b0;

        // ------------
        // Mis-predict
        // ------------
        // flush on mispredict
        if (resolved_branch_i.is_mispredict) begin
            // flush only un-issued instructions
            flush_unissued_instr_o = 1'b1;
            // and if stage
            flush_if_o             = 1'b1;
        end

        // ------------
        // Exception
        // ------------
        if (ex_i.valid) begin
            // don't flush pcgen as we want to take the exception
            flush_pcgen_o          = 1'b0;
            flush_if_o             = 1'b1;
            flush_id_o             = 1'b1;
            flush_ex_o             = 1'b1;
        end

        // ---------------------------------
        // CSR instruction with side-effect
        // ---------------------------------
        if (flush_csr_i) begin
            flush_pcgen_o          = 1'b1;
            flush_if_o             = 1'b1;
            flush_id_o             = 1'b1;
            flush_ex_o             = 1'b1;
        end

    end
    // flush on exception
endmodule
