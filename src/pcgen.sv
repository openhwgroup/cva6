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
    input  logic          clk_i,              // Clock
    input  logic          rst_ni,             // Asynchronous reset active low

    input  logic          fetch_enable_i,
    input  logic          flush_i,
    input  logic          if_ready_i,
    input  branchpredict  resolved_branch_i,  // from controller signaling a branchpredict -> update BTB
    // to IF
    output logic [63:0]   pc_if_o,            // new PC
    output logic          pc_if_valid_o,      // the PC is valid
    output logic          is_branch_o,
    // global input
    input  logic [63:0]   boot_addr_i,
    // CSR input
    input  logic [63:0]   epc_i,              // return from exception
    input  logic [63:0]   trap_vector_base_i, // base of trap vector
    input  exception      ex_i                // exception in - from commit
);

    logic [63:0] branch_target_address;
    logic        predict_taken;
    logic [63:0] npc_n, npc_q;
    logic        is_branch;
    logic        is_branch_n, is_branch_q;


    assign pc_if_o     = npc_q;
    assign is_branch_o = is_branch_q;

    btb #(
        .NR_ENTRIES(64),
        .BITS_SATURATION_COUNTER(2)
    )
    btb_i
    (
        // Use the PC from last cycle to perform branch lookup
        .vpc_i                   ( npc_q                   ),
        .branchpredict_i         ( resolved_branch_i       ),
        .is_branch_o             ( is_branch               ),
        .predict_taken_o         ( predict_taken           ),
        .branch_target_address_o ( branch_target_address   ),
        .*
    );
    // -------------------
    // Next PC
    // -------------------
    // next PC (npc) can come from:
    // 1. Exception
    // 2. Return from exception
    // 3. Predicted branch
    // 4. Debug
    // 5. Boot address
    always_comb begin : npc_select
        // default assignment
        // default is a consecutive PC
        if (if_ready_i && fetch_enable_i)
            npc_n       = {npc_q[62:2], 2'b0}  + 64'h4;
        else // or keep the PC stable if IF is not ready
            npc_n       =  npc_q;

        pc_if_valid_o = 1'b0;
        is_branch_n   = is_branch;

        // 4. Predict taken
        if (is_branch && predict_taken) begin
            npc_n = branch_target_address;
        end
        // 1.Debug

        // 3. Control flow change request
        if (resolved_branch_i.is_mispredict) begin
            // we already got the correct target address
            npc_n    = resolved_branch_i.target_address;
        end
        // 2. Exception
        if (ex_i.valid) begin
            npc_n       = trap_vector_base_i;
            is_branch_n = 1'b0;
        end

        // 3. Return from exception

        // fetch enable
        if (fetch_enable_i) begin
            pc_if_valid_o = 1'b1;
        end
    end
    // -------------------
    // Sequential Process
    // -------------------
    // PCGEN -> IF Register
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if(~rst_ni) begin
           npc_q       <= boot_addr_i;
           is_branch_q <= 1'b0;
        end else begin
           npc_q       <= npc_n;
           is_branch_q <= is_branch_n;
        end
    end

endmodule