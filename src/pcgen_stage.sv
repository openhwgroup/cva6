// Author: Florian Zaruba, ETH Zurich
// Date: 20.04.2017
// Description: PC generation stage
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

module pcgen_stage (
    input  logic             clk_i,              // Clock
    input  logic             rst_ni,             // Asynchronous reset active low
    // control signals
    input  logic             flush_i,            // flush request for PCGEN
    input  logic             flush_bp_i,         // flush branch prediction
    input  logic             fetch_enable_i,
    input  logic             if_ready_i,
    input  branchpredict     resolved_branch_i,  // from controller signaling a branch_predict -> update BTB
    // to IF
    output logic [63:0]      fetch_address_o,    // new PC (address because we do not distinguish instructions)
    output logic             fetch_valid_o,      // the PC (address) is valid
    output branchpredict_sbe branch_predict_o,   // pass on the information if this is speculative
    // global input
    input  logic [63:0]      boot_addr_i,
    // from commit
    input  logic [63:0]      pc_commit_i,        // PC of instruction in commit stage
    // CSR input
    input  logic [63:0]      epc_i,              // exception PC which we need to return to
    input  logic             eret_i,             // return from exception
    input  logic [63:0]      trap_vector_base_i, // base of trap vector
    input  logic             ex_valid_i,         // exception is valid - from commit
    // Debug
    input  logic [63:0]      debug_pc_i,         // PC from debug stage
    input  logic             debug_set_pc_i      // Set PC request from debug
);

    logic [63:0]      npc_n, npc_q;
    // the PC was set to a new region by a higher priority input (e.g.: exception, debug, ctrl return from exception)
    logic             set_pc_n, set_pc_q;
    branchpredict_sbe branch_predict_btb;
    // branch-predict input register -> this path is critical
    branchpredict     resolved_branch_q;

    btb #(
        .NR_ENTRIES              ( BTB_ENTRIES             ),
        .BITS_SATURATION_COUNTER ( BITS_SATURATION_COUNTER )
    )
    btb_i
    (
        // Use the PC from last cycle to perform branch lookup for the current cycle
        .flush_i                 ( flush_bp_i              ),
        .vpc_i                   ( npc_q                   ),
        .branch_predict_i        ( resolved_branch_q       ), // update port
        .branch_predict_o        ( branch_predict_btb      ), // read port
        .*
    );
    // -------------------
    // Next PC
    // -------------------
    // next PC (NPC) can come from (in order of precedence:
    // 0. Default assignment
    // 1. Branch Predict taken
    // 2. Control flow change request
    // 3. Return from environment call
    // 4. Exception/Interrupt
    // 5. Pipeline Flush because of CSR side effects
    // 6. Debug
    // Mis-predict handling is a little bit different
    always_comb begin : npc_select
        automatic logic [63:0] fetch_address = npc_q;

        branch_predict_o = branch_predict_btb;
        fetch_valid_o    = 1'b1;
        // this tells us whether it is a consecutive PC or a completely new PC
        set_pc_n         = 1'b0;

        // -------------------------------
        // 2. Control flow change request
        // -------------------------------
        // keep the PC stable if IF by default
        npc_n            = npc_q;
        // check if had a mis-predict the cycle earlier and if we can reset the PC (e.g.: it was a predicted or consecutive PC
        // which was set a cycle earlier)
        if (resolved_branch_q.is_mispredict && !set_pc_q) begin
            // we already got the correct target address
            fetch_address = resolved_branch_q.target_address;
        end

        // -------------------------------
        // 0. Default assignment
        // -------------------------------
        // default is a consecutive PC
        if (if_ready_i && fetch_enable_i)
            // but operate on the current fetch address
            npc_n = {fetch_address[63:2], 2'b0}  + 64'h4;


        // we only need to stall the consecutive and predicted case since in any other case we will flush at least
        // the front-end which means that the IF stage will always be ready to accept a new request

        // -------------------------------
        // 1. Predict taken
        // -------------------------------
        // only predict if the IF stage is ready, otherwise we might take the predicted PC away which will end in a endless loop
        // also check if we fetched on a half word (npc_q[1] == 1), it might be the case that we need the next 16 byte of the following instruction
        // prediction could potentially prevent us from getting them
        if (if_ready_i && branch_predict_btb.valid && branch_predict_btb.predict_taken) begin
            if (!fetch_address[1])
                npc_n = branch_predict_btb.predict_address;
            // invalidate branch-prediction as we need to correct a possible predicted (not-taken path)
            // an example can be a prediction from the previous cycle to a mis-aligned instruction (0x..1e), we will need to
            // potentially fetch another 16 byte at least and loose prediction on it example:
            // 0x20002dda bltu             a5, a7, pc + -76 <- predicted
            // 0x20002d8e bnez             a4, pc + 148     <- predicted as well (but kill prediction as the previous instruction could be 32 bit)
            else
                branch_predict_o.valid = 1'b0;
        end

        // -------------------------------
        // 3. Return from environment call
        // -------------------------------
        if (eret_i) begin
            npc_n                  = epc_i;
            branch_predict_o.valid = 1'b0;
            set_pc_n               = 1'b1;
        end

        // -------------------------------
        // 4. Exception/Interrupt
        // -------------------------------
        if (ex_valid_i) begin
            npc_n                  = trap_vector_base_i;
            branch_predict_o.valid = 1'b0;
            set_pc_n               = 1'b1;
        end

        // -----------------------------------------------
        // 5. Pipeline Flush because of CSR side effects
        // -----------------------------------------------
        // On a pipeline flush start fetching from the next address
        // of the instruction in the commit stage
        if (flush_i) begin
            // we came here from a flush request of a CSR instruction,
            // as CSR instructions do not exist in a compressed form
            // we can unconditionally do PC + 4 here
            npc_n    = pc_commit_i + 64'h4;
            set_pc_n = 1'b1;
            branch_predict_o.valid = 1'b0;
        end

        // -------------------------------
        // 6. Debug
        // -------------------------------
        if (debug_set_pc_i) begin
            npc_n = debug_pc_i;
            branch_predict_o.valid = 1'b0;
            set_pc_n = 1'b1;
        end

        // fetch enable
        if (!fetch_enable_i) begin
            fetch_valid_o = 1'b0;
        end

        // set fetch address
        fetch_address_o  = fetch_address;

    end

    // -------------------
    // Sequential Process
    // -------------------
    // PCGEN -> IF Pipeline Stage
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if(~rst_ni) begin
           npc_q             <= boot_addr_i;
           set_pc_q          <= 1'b0;
           resolved_branch_q <= '0;
        end else begin
           npc_q             <= npc_n;
           set_pc_q          <= set_pc_n;
           resolved_branch_q <= resolved_branch_i;
        end
    end
endmodule
