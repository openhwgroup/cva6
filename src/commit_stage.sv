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
    input  logic                halt_i,        // request to halt the core

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
    output logic                commit_lsu_o,    // commit the pending store
    input  logic                commit_lsu_ready_i,
    input  logic                no_st_pending_i, // there is no store pending
    output logic                commit_csr_o,    // commit the pending CSR instruction
    output logic                fence_i_o,        // flush icache and pipeline
    output logic                sfence_vma_o     // flush TLBs and pipeline
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
        fence_i_o    = 1'b0;
        sfence_vma_o = 1'b0;

        // we will not commit the instruction if we took an exception
        // but we do not commit the instruction if we requested a halt
        if (commit_instr_i.valid && !halt_i) begin

            commit_ack_o = 1'b1;
            // register will be the all zero register.
            // and also acknowledge the instruction, this is mainly done for the instruction tracer
            // as it will listen on the instruction ack signal. For the overall result it does not make any
            // difference as the whole pipeline is going to be flushed anyway.
            if (!exception_o.valid) begin
                // we can definitely write the register file
                // if the instruction is not committing anything the destination
                we_a_o       = 1'b1;

                // check whether the instruction we retire was a store
                // do not commit the instruction if we got an exception since the store buffer will be cleared
                // by the subsequent flush triggered by an exception
                if (commit_instr_i.fu == STORE) begin
                    if (commit_lsu_ready_i)
                        commit_lsu_o = 1'b1;
                    else // if the LSU buffer is not ready - do not commit, wait
                        commit_ack_o = 1'b0;
                end
            end

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
            // ------------------
            // SFENCE.VMA Logic
            // ------------------
            // check if this instruction was a SFENCE_VMA
            if (commit_instr_i.op == SFENCE_VMA) begin
                // no store pending so we can flush the TLBs and pipeline
                if (no_st_pending_i) begin
                    sfence_vma_o = 1'b1;
                // wait for the store buffer to drain until flushing the pipeline
                end else begin
                    commit_ack_o = 1'b0;
                end
            end
            // ------------------
            // FENCE.I Logic
            // ------------------
            if (commit_instr_i.op == FENCE_I) begin
                commit_ack_o = 1'b1;
                // tell the controller to flush the I$
                fence_i_o = 1'b1;
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
        if (csr_exception_i.valid && !csr_exception_i.cause[63]) begin
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
        // check for CSR interrupts (e.g.: normal interrupts which get triggered here)
        // by putting interrupts here we give them precedence over any other exception
        if (csr_exception_i.valid && csr_exception_i.cause[63]) begin
            exception_o = csr_exception_i;
            exception_o.tval = commit_instr_i.ex.tval;
        end
        // If we halted the processor don't take any exceptions
        if (halt_i) begin
            exception_o.valid = 1'b0;
        end
    end
endmodule
