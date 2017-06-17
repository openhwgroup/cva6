// Author: Florian Zaruba, ETH Zurich
// Date: 15.04.2017
// Description: Commits to the architectural state resulting from the scoreboard.
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

module commit_stage (
    input logic                 clk_i,         // Clock
    input logic                 rst_ni,        // Asynchronous reset active low

    output exception            exception_o,   // take exception to controller

    // from scoreboard
    input  scoreboard_entry     commit_instr_i,
    output logic                commit_ack_o,

    // to register file
    output  logic[4:0]          waddr_a_o,
    output  logic[63:0]         wdata_a_o,
    output  logic               we_a_o,

    // to CSR file and PC Gen (because on certain CSR instructions we'll need to flush the whole pipeline)
    output logic [63:0]         pc_o,
    // to/from CSR file
    output fu_op                csr_op_o,
    output logic [63:0]         csr_wdata_o,
    input  logic [63:0]         csr_rdata_i,
    input  exception            csr_exception_i,
    // commit signals to ex
    output logic                commit_lsu_o,   // commit the pending store
    output logic                commit_csr_o    // commit the pending CSR instruction
);

    assign waddr_a_o = commit_instr_i.rd;
    assign pc_o      = commit_instr_i.pc;

    // -------------------
    // Commit Instruction
    // -------------------
    // write register file or commit instruction in LSU or CSR Buffer
    always_comb begin : commit
        // default assignments
        commit_ack_o = 1'b0;
        we_a_o       = 1'b0;
        commit_lsu_o = 1'b0;
        commit_csr_o = 1'b0;
        wdata_a_o    = commit_instr_i.result;
        csr_op_o     = ADD; // this corresponds to a CSR NOP
        csr_wdata_o  = 64'b0;

        // we will not commit the instruction if we took an exception
        if (commit_instr_i.valid) begin
            // register will be the all zero register.
            // and also acknowledge the instruction, this is mainly done for the instruction tracer
            // as it will listen on the instruction ack signal. For the overall result it does not make any
            // difference as the whole pipeline is going to be flushed anyway.
            if (~exception_o.valid) begin
                // we can definitely write the register file
                // if the instruction is not committing anything the destination
                we_a_o       = 1'b1;

                // do not commit the instruction if we got an exception since the store buffer will be cleared
                // by the subsequent flush triggered by an exception
                if (commit_instr_i.fu == STORE) begin
                    commit_lsu_o = 1'b1;
                end
            end

            commit_ack_o = 1'b1;
            // check whether the instruction we retire was a store
            // ---------
            // CSR Logic
            // ---------
            // check whether the instruction we retire was a CSR instruction
            if (commit_instr_i.fu == CSR) begin
                // write the CSR file
                commit_csr_o = 1'b1;
                wdata_a_o    = csr_rdata_i;
                csr_op_o     = commit_instr_i.op;
                csr_wdata_o  = commit_instr_i.result;
            end
        end
    end

    // -----------------------------
    // Exception & Interrupt Logic
    // -----------------------------
    // here we know for sure that we are taking the exception
    always_comb begin : exception_handling
        // Multiple simultaneous interrupts and traps at the same privilege level are handled in the following decreasing
        // priority order: external interrupts, software interrupts, timer interrupts, then finally any synchronous traps. (1.10 p.30)
        // interrupts are correctly prioritized in the CSR reg file, exceptions are prioritized here
        exception_o.valid = 1'b0;
        exception_o.cause = 64'b0;
        exception_o.tval  = 64'b0;
        // check for CSR exception
        if (csr_exception_i.valid && ~csr_exception_i.cause[63]) begin
            exception_o      = csr_exception_i;
            // if no earlier exception happened the commit instruction will still contain
            // the instruction data from the ID stage. If a earlier exception happened we don't care
            // as we will overwrite it anyway in the next IF bl
            exception_o.tval = commit_instr_i.ex.tval;
        end
        // but we give precedence to exceptions which happened earlier
        if (commit_instr_i.ex.valid) begin
            exception_o = commit_instr_i.ex;
        end
        // check for CSR interrupts (e.g.: normal interrupts they get triggered here)
        if (csr_exception_i.valid && csr_exception_i.cause[63]) begin
            exception_o = csr_exception_i;
            exception_o.tval = commit_instr_i.ex.tval;
        end
    end

    `ifndef SYNTHESIS
        always_ff @(posedge clk_i) begin : exception_displayer
            string cause;
            // we encountered an exception
            // format cause
            if (exception_o.valid) begin
                case (exception_o.cause)
                    INSTR_ADDR_MISALIGNED: cause = "Instruction Address Misaligned";
                    INSTR_ACCESS_FAULT:    cause = "Instruction Access Fault";
                    ILLEGAL_INSTR:         cause = "Illegal Instruction";
                    BREAKPOINT:            cause = "Breakpoint";
                    LD_ADDR_MISALIGNED:    cause = "Load Address Misaligned";
                    LD_ACCESS_FAULT:       cause = "Load Access Fault";
                    ST_ADDR_MISALIGNED:    cause = "Store Address Misaligned";
                    ST_ACCESS_FAULT:       cause = "Store Access Fault";
                    ENV_CALL_UMODE:        cause = "Environment Call User Mode";
                    ENV_CALL_SMODE:        cause = "Environment Call Supervisor Mode";
                    ENV_CALL_MMODE:        cause = "Environment Call Machine Mode";
                    INSTR_PAGE_FAULT:      cause = "Instruction Page Fault";
                    LOAD_PAGE_FAULT:       cause = "Load Page Fault";
                    STORE_PAGE_FAULT:      cause = "Store Page Fault";
                    default: cause = "Interrupt";
                endcase
            $display("Exception @%t, PC: %h, TVal: %h, Cause: %s", $time, commit_instr_i.pc, exception_o.tval, cause);
            end
        end
    `endif
endmodule
