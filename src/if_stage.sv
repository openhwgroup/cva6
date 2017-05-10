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
    input  logic                   flush_i,
    input  logic                   req_i,       // request new instructions
    output logic                   if_busy_o,   // is the IF stage busy fetching instructions?
    input  logic                   id_ready_i,
    input  logic                   halt_if_i,   // pipeline stall
    // ctrl flow instruction in
    input  logic [63:0]            fetch_addr_i,
    input  logic                   set_pc_i,    // set new PC
    input  logic                   is_branch_i,  // the new PC was a branch e.g.: branch or jump
    // branchpredict out
    output logic                   branch_valid_o,
    output logic [63:0]            predict_address_o,
    output logic                   predict_taken_o,
    // instruction cache interface
    output logic                   instr_req_o,
    output logic [63:0]            instr_addr_o,
    input  logic                   instr_gnt_i,
    input  logic                   instr_rvalid_i,
    input  logic [31:0]            instr_rdata_i,
    // Output of IF Pipeline stage
    output logic                   instr_valid_id_o,      // instruction in IF/ID pipeline is valid
    output logic [31:0]            instr_rdata_id_o,      // read instruction is sampled and sent to ID stage for decoding
    output logic                   is_compressed_id_o,    // compressed decoder thinks this is a compressed instruction
    output logic                   illegal_c_insn_id_o,   // compressed decoder thinks this is an invalid instruction
    output logic [63:0]            pc_if_o,
    output logic [63:0]            pc_id_o,
    output exception               ex_o
);

    logic              if_ready, if_valid;
    logic              branch_req;
    logic              valid;
    logic              prefetch_busy;

    logic              fetch_valid;
    logic              fetch_ready;
    logic       [31:0] fetch_rdata;
    logic       [63:0] fetch_addr;

    // branch predict registers
    logic         branch_valid_n,    branch_valid_q;
    logic [63:0]  predict_address_n, predict_address_q;
    logic         predict_taken_n,   predict_taken_q;

    // offset FSM
    enum logic[0:0] {WAIT, IDLE} offset_fsm_cs, offset_fsm_ns;
    logic [31:0] instr_decompressed;
    logic        illegal_c_insn;
    logic        instr_compressed_int;
    logic        clear_instr_valid_i;

    // compressed instruction decoding, or more precisely compressed instruction
    // expander
    //
    // since it does not matter where we decompress instructions, we do it here
    // to ease timing closure
    compressed_decoder compressed_decoder_i (
        .instr_i         ( fetch_rdata          ),
        .instr_o         ( instr_decompressed   ),
        .is_compressed_o ( instr_compressed_int ),
        .illegal_instr_o ( illegal_c_insn       )
    );

    // Pre-fetch buffer, caches a fixed number of instructions
    prefetch_buffer prefetch_buffer_i (
        .clk               ( clk_i                       ),
        .rst_n             ( rst_ni                       ),

        .req_i             ( req_i                       ),

        .branch_i          ( branch_req                  ), // kill everything
        .addr_i            ( {fetch_addr_i[63:1], 1'b0}  ),

        .ready_i           ( fetch_ready                 ),
        .valid_o           ( fetch_valid                 ),
        .rdata_o           ( fetch_rdata                 ),
        .addr_o            ( fetch_addr                  ),

        // goes to instruction memory / instruction cache
        .instr_req_o       ( instr_req_o                 ),
        .instr_addr_o      ( instr_addr_o                ),
        .instr_gnt_i       ( instr_gnt_i                 ),
        .instr_rvalid_i    ( instr_rvalid_i              ),
        .instr_rdata_i     ( instr_rdata_i               ),

        // Prefetch Buffer Status
        .busy_o            ( prefetch_busy               )
    );

    // offset FSM state transition logic
    always_comb begin
      offset_fsm_ns = offset_fsm_cs;

      fetch_ready   = 1'b0;
      branch_req    = 1'b0;
      valid         = 1'b0;

      unique case (offset_fsm_cs)
        // no valid instruction data for ID stage
        // assume aligned
        IDLE: begin
          if (req_i) begin
            branch_req    = 1'b1;
            offset_fsm_ns = WAIT;
          end
        end

        // serving aligned 32 bit or 16 bit instruction, we don't know yet
        WAIT: begin
          if (fetch_valid) begin
            valid   = 1'b1; // an instruction is ready for ID stage

            if (req_i && if_valid) begin
              fetch_ready   = 1'b1;
              offset_fsm_ns = WAIT;
            end
          end
        end

        default: begin
          offset_fsm_ns = IDLE;
        end
      endcase

      // take care of control flow changes
      if (set_pc_i) begin
        valid = 1'b0;
        // switch to new PC from ID stage
        branch_req = 1'b1;
        offset_fsm_ns = WAIT;
      end
    end

    // -------------
    // Branch Logic
    // -------------
    // We need to pass those registers on to ID in the case we've set
    // a new branch target (or jump) and we got a valid instruction
    always_comb begin
        branch_valid_n    = branch_valid_q;
        predict_address_n = predict_address_q;
        predict_taken_n   = predict_taken_q;
        // we got a branch redirect from PCGEN
        if (is_branch_i) begin
            // set the registers to the correct address
            branch_valid_n    = 1'b1;
            predict_address_n = fetch_addr_i;
            // whether we took the branch or not can be seen from the set PC
            // nevertheless we also need to keep branches not taken
            predict_taken_n   = set_pc_i;
        end
        // we have a valid instruction and id excepted it so we consider all the
        // branch information to be sampled correctly
        if (if_valid && clear_instr_valid_i) begin
            branch_valid_n = 1'b0;
        end

    end

    // --------------------------------------------------------------
    // IF-ID pipeline registers, frozen when the ID stage is stalled
    // --------------------------------------------------------------
    always_ff @(posedge clk_i, negedge rst_ni) begin : IF_ID_PIPE_REGISTERS
      if (~rst_ni) begin
            // offset FSM state
            offset_fsm_cs         <= IDLE;
            instr_valid_id_o      <= 1'b0;
            instr_rdata_id_o      <= '0;
            illegal_c_insn_id_o   <= 1'b0;
            is_compressed_id_o    <= 1'b0;
            pc_id_o               <= '0;
            ex_o                  <= '{default: 0};
            branch_valid_q        <= 1'b0;
            predict_address_q     <= 64'b0;
            predict_taken_q       <= 1'b0;
        end
      else
        begin
            offset_fsm_cs         <= offset_fsm_ns;
            branch_valid_q        <= branch_valid_n;
            predict_address_q     <= predict_address_n;
            predict_taken_q       <= predict_taken_n;

            if (if_valid) begin
              instr_valid_id_o    <= 1'b1;
              instr_rdata_id_o    <= instr_decompressed;
              illegal_c_insn_id_o <= illegal_c_insn;
              is_compressed_id_o  <= instr_compressed_int;
              pc_id_o             <= pc_if_o;
              ex_o.cause          <= 64'b0; // TODO: Output exception
              ex_o.tval           <= 64'b0; // TODO: Output exception
              ex_o.valid          <= 1'b0;  // TODO: Output exception
            end else if (clear_instr_valid_i) begin
              instr_valid_id_o    <= 1'b0;
            end

        end
    end

    // Assignments
    assign pc_if_o             = fetch_addr;
    // id stage acknowledged
    assign clear_instr_valid_i = id_ready_i;
    assign if_ready            = valid & id_ready_i;
    assign if_valid            = (~halt_if_i) & if_ready;
    assign if_busy_o           = prefetch_busy;
    assign branch_valid_o      = branch_valid_q;
    assign predict_address_o   = predict_address_q;
    assign predict_taken_o     = predict_taken_q;

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