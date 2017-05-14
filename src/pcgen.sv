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

module pcgen (
    input  logic             clk_i,              // Clock
    input  logic             rst_ni,             // Asynchronous reset active low
    // control signals
    input  logic             fetch_enable_i,
    input  logic             flush_i,
    input  logic             if_ready_i,
    input  branchpredict     resolved_branch_i,  // from controller signaling a branch_predict -> update BTB
    // to IF
    output logic [63:0]      fetch_address_o,    // new PC (address because we do not distinguish instructions)
    output logic             fetch_valid_o,      // the PC (address) is valid
    output branchpredict_sbe branch_predict_o,   // pass on the information if this is speculative
    // global input
    input  logic [63:0]      boot_addr_i,
    // CSR input
    input  logic [63:0]      epc_i,              // return from exception
    input  logic [63:0]      trap_vector_base_i, // base of trap vector
    input  exception         ex_i                // exception in - from commit
);

    logic [63:0]      npc_n, npc_q;
    branchpredict_sbe branch_predict_btb;

    assign pc_if_o = npc_q;

    btb #(
        .NR_ENTRIES(64),
        .BITS_SATURATION_COUNTER(2)
    )
    btb_i
    (
        // Use the PC from last cycle to perform branch lookup for the current cycle
        .vpc_i                   ( npc_q                   ),
        .branch_predict_i        ( resolved_branch_i       ), // update port
        .branch_predict_o        ( branch_predict_btb      ), // read port
        .*
    );
    // -------------------
    // Next PC
    // -------------------
    // next PC (NPC) can come from:
    // 1. Exception
    // 2. Return from exception
    // 3. Predicted branch
    // 4. Debug
    // 5. Boot address
    always_comb begin : npc_select
        branch_predict_o = branch_predict_btb;
        fetch_valid_o = 1'b1;

        // 0. Default assignment
        // default is a consecutive PC
        if (if_ready_i && fetch_enable_i)
            npc_n       = {npc_q[62:2], 2'b0}  + 64'h4;
        else // or keep the PC stable if IF is not ready
            npc_n       =  npc_q;
        // 4. Predict taken
        if (branch_predict_btb.valid && branch_predict_btb.predict_taken) begin
            npc_n = branch_predict_btb.predict_address;
        end
        // 1.Debug
        // 3. Control flow change request
        if (resolved_branch_i.is_mispredict) begin
            // we already got the correct target address
            npc_n    = resolved_branch_i.target_address;
        end
        // 2. Exception
        if (ex_i.valid) begin
            npc_n                 = trap_vector_base_i;
            branch_predict_o.valid = 1'b0;
        end

        // 3. Return from exception

        // fetch enable
        if (!fetch_enable_i) begin
            fetch_valid_o = 1'b0;
        end
    end
    // -------------------
    // Sequential Process
    // -------------------
    // PCGEN -> IF Pipeline Stage
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if(~rst_ni) begin
           npc_q       <= boot_addr_i;
        end else begin
           npc_q       <= npc_n;
        end
    end

endmodule