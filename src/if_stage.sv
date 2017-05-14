////////////////////////////////////////////////////////////////////////////////
// Copyright (C) 2017 ETH Zurich, University of Bologna                       //
// All rights reserved.                                                       //
//                                                                            //
// This code is under development and not yet released to the public.         //
// Until it is released, the code is under the copyright of ETH Zurich        //
// and the University of Bologna, and may contain unpublished work.           //
// Any reuse/redistribution should only be under explicit permission.         //
//                                                                            //
// Bug fixes and contributions will eventually be released under the          //
// SolderPad open hardware license and under the copyright of ETH Zurich      //
// and the University of Bologna.                                             //
//                                                                            ///
// Engineer:       Renzo Andri - andrire@student.ethz.ch                      //
//                                                                            //
// Additional contributions by:                                               //
//                 Igor Loi - igor.loi@unibo.it                               //
//                 Andreas Traber - atraber@student.ethz.ch                   //
//                 Sven Stucki - svstucki@student.ethz.ch                     //
//                                                                            //
// Design Name:    Instruction Fetch Stage                                    //
// Project Name:   zero-riscy                                                 //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Instruction fetch unit: Selection of the next PC, and      //
//                 buffering (sampling) of the read instruction               //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////
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
    output logic [63:0]            pc_o,
    output logic                   instr_valid_o,      // instruction in IF/ID pipeline is valid
    input  logic                   instr_ack_i,
    output logic [31:0]            instr_rdata_o,      // read instruction is sampled and sent to ID stage for decoding
    output logic                   instr_is_compressed_o,
    output exception               ex_o,
    output branchpredict_sbe       branch_predict_o    // branch prediction  out
);
    // output logic illegal_compressed_instr_o -> in exception
    logic              fetch_valid;
    logic [31:0]       instr_rdata;
    logic              instr_is_compressed;
    logic [31:0]       decompressed_instruction;
    logic [63:0]       addr_o;
    logic              illegal_compressed_instr;
    logic              prefetch_busy;
    branchpredict_sbe  branch_predict;
    // ---------------------
    // IF <-> ID Registers
    // ---------------------
    logic [63:0] pc_n,                  pc_q;
    logic        instr_valid_n,         instr_valid_q;
    logic [31:0] instr_rdata_n,         instr_rdata_q;
    logic        instr_is_compressed_n, instr_is_compressed_q;
    // branch predict registers
    logic              branch_predict_n,    branch_predict_q;

    // compressed instruction decoding, or more precisely compressed instruction expander
    // since it does not matter where we decompress instructions, we do it here to ease timing closure
    compressed_decoder compressed_decoder_i (
        .instr_i          ( instr_rdata                ),
        .instr_o          ( decompressed_instruction   ),
        .is_compressed_o  ( instr_is_compressed        ),
        .illegal_instr_o  ( illegal_compressed_instr   )
    );

    // Pre-fetch buffer, caches a fixed number of instructions
    prefetch_buffer prefetch_buffer_i (

        .ready_i           ( instr_ack_i                 ),
        .valid_o           ( fetch_valid                 ),
        .rdata_o           ( instr_rdata                 ),
        .addr_o            ( addr_o                      ),
        .branch_predict_o  ( branch_predict              ),
        // goes to instruction memory / instruction cache

        // Prefetch Buffer Status
        .busy_o            ( prefetch_busy               ),
        .*
    );

    assign if_busy_o             = prefetch_busy;

    assign pc_o                  = pc_q;
    assign instr_valid_o         = instr_valid_q;
    assign instr_rdata_o         = instr_rdata_q;
    assign instr_is_compressed_o = instr_is_compressed_q;
    assign branch_predict_o      = branch_predict_q;
    // Pipeline registers
    always_comb begin
        // Instruction is valid, latch new data
        pc_n                    = addr_o;
        instr_valid_n           = fetch_valid;
        instr_rdata_n           = decompressed_instruction;
        instr_is_compressed_n   = instr_is_compressed;
        branch_predict_n        = branch_predict;

        if (flush_i) begin
            instr_valid_n = 1'b0;
        end
        // exception forwarding in here
    end

    // --------------------------------------------------------------
    // IF-ID pipeline registers, frozen when the ID stage is stalled
    // --------------------------------------------------------------
    always_ff @(posedge clk_i, negedge rst_ni) begin : IF_ID_PIPE_REGISTERS
      if (~rst_ni) begin
            ex_o                    <= '{default: 0};
            branch_predict_q        <= '{default: 0};
            pc_q                    <= 64'b0;
            instr_valid_q           <= 1'b0;
            instr_rdata_q           <= 32'b0;
            instr_is_compressed_q   <= 1'b0;
        end else begin
            pc_q                    <= pc_n;
            instr_valid_q           <= instr_valid_n;
            instr_rdata_q           <= instr_rdata_n;
            instr_is_compressed_q   <= instr_is_compressed_n;
            branch_predict_q        <= branch_predict_n;
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