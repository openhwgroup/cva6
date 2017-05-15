// Author: Florian Zaruba, ETH Zurich
// Date: 14.05.2017
// Description: Instruction fetch stage
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

module if_stage (
    input  logic                   clk_i,       // Clock
    input  logic                   rst_ni,      // Asynchronous reset active low
    // control signals
    input  logic                   flush_i,
    output logic                   if_busy_o,   // is the IF stage busy fetching instructions?
    input  logic                   id_ready_i,
    // fetch direction from PC Gen
    input  logic [63:0]            fetch_address_i,
    input  logic                   fetch_valid_i,
    input  branchpredict_sbe       branch_predict_i,
    // instruction cache interface
    output logic                   instr_req_o,
    output logic [63:0]            instr_addr_o,
    input  logic                   instr_gnt_i,
    input  logic                   instr_rvalid_i,
    input  logic [31:0]            instr_rdata_i,
    // Output of IF Pipeline stage
    output fetch_entry             fetch_entry_o,
    output logic                   fetch_entry_valid_i,      // instruction in IF/ID pipeline is valid
    input  logic                   instr_ack_i,
    output exception               ex_o
);
    logic              prefetch_busy;

    // Pre-fetch buffer, caches a fixed number of instructions
    prefetch_buffer prefetch_buffer_i (

        .ready_i           ( instr_ack_i                 ),
        .valid_o           ( fetch_entry_valid_i         ),
        // Prefetch Buffer Status
        .busy_o            ( prefetch_busy               ),
        .*
    );

    assign if_busy_o             = prefetch_busy;

    // --------------------------------------------------------------
    // IF-ID pipeline registers, frozen when the ID stage is stalled
    // --------------------------------------------------------------
    always_ff @(posedge clk_i, negedge rst_ni) begin : IF_ID_PIPE_REGISTERS
      if (~rst_ni) begin
            ex_o                    <= '{default: 0};
        end else begin
            ex_o.cause              <= 64'b0; // TODO: Output exception
            ex_o.tval               <= 64'b0; // TODO: Output exception
            ex_o.valid              <= 1'b0; //illegal_compressed_instr;  // TODO: Output exception
        end
    end
    //-------------
    // Assertions
    //-------------
    `ifndef SYNTHESIS
    `ifndef VERILATOR
        // there should never be a grant when there was no request
        assert property (
          @(posedge clk_i) (instr_gnt_i) |-> (instr_req_o) )
        else $warning("There was a grant without a request");
    `endif
    `endif
endmodule