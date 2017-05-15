// Author: Florian Zaruba, ETH Zurich
// Date: 14.05.2017
// Description: Dual Port fetch FIFO with instruction aligner and support for compressed instructions
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

module fetch_fifo
(
    input  logic                   clk_i,
    input  logic                   rst_ni,
    // control signals
    input  logic                   flush_i,    // clears the contents of the FIFO -> quasi reset
    // branch prediction at in_addr_i address, as this is an address and not PC it can be the case
    // that we have two compressed instruction (or one compressed instruction and one unaligned instruction) so we need
    // keep two prediction inputs: [c1|c0] <- prediction for c1 and c0
    input  branchpredict_sbe       branch_predict_i,
    input  logic [63:0]            in_addr_i,
    input  logic [31:0]            in_rdata_i,
    input  logic                   in_valid_i,
    output logic                   in_ready_o,
    // output port
    output fetch_entry             fetch_entry_o,
    output logic                   out_valid_o,
    input  logic                   out_ready_i
);

    localparam DEPTH = 8; // must be a power of two

    // input registers - bounding the path from memory
    branchpredict_sbe       branch_predict_n, branch_predict_q;
    logic [63:0]            in_addr_n,        in_addr_q;
    logic [31:0]            in_rdata_n,       in_rdata_q;
    logic                   in_valid_n,       in_valid_q;
    // compressed to decompressed instruction
    logic [31:0] decompressed_instruction [2];
    logic        is_illegal [2];

    fetch_entry mem_n[DEPTH-1:0], mem_q[DEPTH-1:0];
    logic [$clog2(DEPTH)-1:0]     read_pointer_n, read_pointer_q;
    logic [$clog2(DEPTH)-1:0]     write_pointer_n, write_pointer_q;
    logic [$clog2(DEPTH)-1:0]     status_cnt_n,    status_cnt_q; // this integer will be truncated by the synthesis tool

    // status signals
    logic full, empty;
    // the last instruction was unaligned
    logic unaligned_n, unaligned_q;
    // save the unaligned part of the instruction to this ff
    logic [15:0] unaligned_instr_n, unaligned_instr_q;
    // save the address of the unaligned instruction
    logic [63:0] unaligned_address_n, unaligned_address_q;
    // we always need two empty places
    // as it could happen that we get two compressed instructions/cycle
    /* verilator lint_off WIDTH */
    assign full        = (status_cnt_q >= DEPTH - 3);
    assign empty       = (status_cnt_q == 0);
    /* verilator lint_on WIDTH */
    // the output is valid if we are either empty or just got a valid
    assign out_valid_o = !empty || in_valid_q;
    // we need space for at least two instructions: the full flag is conditioned on that
    // but if we pop in the current cycle and we have one place left we can still fit two instructions alt
    assign in_ready_o  = !full;

    // ----------------
    // Input Registers
    // ----------------
    always_comb begin
        // if we are not ready latch the values
        in_addr_n           = in_addr_q;
        in_rdata_n          = in_rdata_q;
        in_valid_n          = 1'b0;
        branch_predict_n    = branch_predict_q;
        // if we are ready to accept new data - do so!
        if (in_ready_o) begin
            in_addr_n        = in_addr_i;
            in_rdata_n       = in_rdata_i;
            in_valid_n       = in_valid_i;
            branch_predict_n = branch_predict_i;
        end
        // flush the input registers
        if (flush_i) begin
            in_valid_n = 1'b0;
        end
    end
    // --------------------
    // Compressed Decoders
    // --------------------
    // compressed instruction decoding, or more precisely compressed instruction expander
    // since it does not matter where we decompress instructions, we do it here to ease timing closure
    genvar i;
    generate
        for (i = 0; i < 2; i++) begin
            compressed_decoder compressed_decoder_i (
                .instr_i          ( in_rdata_q[(16*(i+1)-1):(i*16)]  ),
                .instr_o          ( decompressed_instruction[i]      ),
                .illegal_instr_o  ( is_illegal[i]                    )
            );
        end
    endgenerate

    // --------------------------------------------
    // FIFO Management + Instruction (re)-aligner
    // --------------------------------------------
    always_comb begin : output_port
        // counter
        automatic logic [$clog2(DEPTH)-1:0] status_cnt    = status_cnt_q;
        automatic logic [$clog2(DEPTH)-1:0] write_pointer = write_pointer_q;

        write_pointer_n           = write_pointer_q;
        read_pointer_n            = read_pointer_q;
        mem_n                     = mem_q;
        unaligned_n               = unaligned_q;
        unaligned_instr_n         = unaligned_instr_q;
        unaligned_address_n       = unaligned_address_q;
        // ---------------------------------
        // Input port & Instruction Aligner
        // ---------------------------------
        if (in_valid_q && !unaligned_q) begin
            // we got a valid instruction so we can satisfy the unaligned instruction
            unaligned_n = 1'b0;
            // check if the instruction is compressed
            if (in_rdata_q[1:0] != 2'b11) begin
                // it is compressed
                mem_n[write_pointer_q]    = {
                    branch_predict_q, in_addr_q, decompressed_instruction[0], 1'b1, is_illegal[0]
                };

                status_cnt++;
                write_pointer++;
                // is the second instruction also compressed, like:
                // _____________________________________________
                // | compressed 2 [31:16] | compressed 1[15:0] |
                // |____________________________________________
                // check if the lower compressed instruction was no branch otherwise we will need to squash this instruction
                // but only if we predicted it to be taken, the predict was on the lower 16 bit compressed instruction
                if (in_rdata_q[17:16] != 2'b11 && !(branch_predict_q.valid && branch_predict_q.predict_taken && branch_predict_q.is_lower_16)) begin

                    mem_n[write_pointer_q + 1'b1]    = {
                        branch_predict_q, {in_addr_q[63:2], 2'b10}, decompressed_instruction[1], 1'b1, is_illegal[1]
                    };

                    status_cnt++;
                    write_pointer++;
                    $display("Instruction: [ c  | c  ] @ %t", $time);
                // or is it an unaligned 32 bit instruction like
                // ____________________________________________________
                // |instr [15:0] | instr [31:16] | compressed 1[15:0] |
                // |____________________________________________________
                end else if (!(branch_predict_q.valid && branch_predict_q.predict_taken && branch_predict_q.is_lower_16)) begin
                    // save the lower 16 bit
                    unaligned_instr_n = in_rdata_q[31:16];
                    // and that it was unaligned
                    unaligned_n = 1'b1;
                    // save the address as well
                    unaligned_address_n = {in_addr_q[63:2], 2'b10};
                    $display("Instruction: [ i0 | c  ] @ %t", $time);
                    // this does not consume space in the FIFO
                end
            end else begin
                // this is a full 32 bit instruction like
                // _______________________
                // | instruction [31:0]  |
                // |______________________
                mem_n[write_pointer_q]    = {
                    branch_predict_q, in_addr_q, in_rdata_q, 1'b0, 1'b0
                };
                status_cnt++;
                write_pointer++;
                $display("Instruction: [    i    ] @ %t", $time);
            end
        end
        // we have an outstanding unaligned instruction
        if (in_valid_q && unaligned_q) begin

            mem_n[write_pointer_q]    = {
                branch_predict_q, unaligned_address_q, {in_rdata_q[15:0], unaligned_instr_q}, 1'b0, 1'b0
            };

            status_cnt++;
            write_pointer++;
            // whats up with the other upper 16 bit of this instruction
            // is the second instruction also compressed, like:
            // _____________________________________________
            // | compressed 2 [31:16] | unaligned[31:16]    |
            // |____________________________________________
            // check if the lower compressed instruction was no branch otherwise we will need to squash this instruction
            // but only if we predicted it to be taken, the predict was on the lower 16 bit compressed instruction
            if (in_rdata_q[17:16] != 2'b11  && !(branch_predict_q.valid && branch_predict_q.predict_taken && branch_predict_q.is_lower_16)) begin
                mem_n[write_pointer_q + 1'b1] = {
                    branch_predict_q, {in_addr_q[63:2], 2'b10}, decompressed_instruction[1], 1'b1, is_illegal[1]
                };

                status_cnt++;
                write_pointer++;
                // unaligned access served
                unaligned_n = 1'b0;
                $display("Instruction: [ c  | i1 ] @ %t", $time);
            // or is it an unaligned 32 bit instruction like
            // ____________________________________________________
            // |instr [15:0] | instr [31:16] | compressed 1[15:0] |
            // |____________________________________________________
            end else if (!(branch_predict_q.valid && branch_predict_q.predict_taken && branch_predict_q.is_lower_16)) begin
                // save the lower 16 bit
                unaligned_instr_n = in_rdata_q[31:16];
                // and that it was unaligned
                unaligned_n = 1'b1;
                // save the address as well
                unaligned_address_n = {in_addr_q[63:2], 2'b10};
                $display("Instruction: [ i0 | i1 ] @ %t", $time);
                // this does not consume space in the FIFO
            end
        end

        // -------------
        // Output port
        // -------------
        // we are ready to accept a new request if we still have two places in the queue

        // Output assignments
        fetch_entry_o = mem_q[read_pointer_q].branch_predict;

        if (out_ready_i) begin
            read_pointer_n = read_pointer_q + 1;
            status_cnt--;
        end

        write_pointer_n = write_pointer;
        status_cnt_n    = status_cnt;

        if (flush_i) begin
            status_cnt_n    = '0;
            write_pointer_n = 'b0;
            read_pointer_n  = 'b0;
        end
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (~rst_ni) begin
            status_cnt_q              <= '{default: 0};
            mem_q                     <= '{default: 0};
            read_pointer_q            <= '{default: 0};
            write_pointer_q           <= '{default: 0};
            unaligned_q               <= 1'b0;
            unaligned_instr_q         <= 16'b0;
            unaligned_address_q       <= 64'b0;
            // input registers
            in_addr_q                 <= 64'b0;
            in_rdata_q                <= 32'b0;
            in_valid_q                <= 1'b0;
            branch_predict_q          <= '{default: 0};
        end else begin
            status_cnt_q              <= status_cnt_n;
            mem_q                     <= mem_n;
            read_pointer_q            <= read_pointer_n;
            write_pointer_q           <= write_pointer_n;
            unaligned_q               <= unaligned_n;
            unaligned_instr_q         <= unaligned_instr_n;
            unaligned_address_q       <= unaligned_address_n;
            // input registers
            in_addr_q                 <= in_addr_n;
            in_rdata_q                <= in_rdata_n;
            in_valid_q                <= in_valid_n;
            branch_predict_q          <= branch_predict_n;
        end
    end

    //-------------
    // Assertions
    //-------------
    `ifndef SYNTHESIS
    `ifndef VERILATOR
    // since this is a dual port queue the status count of the queue should never change more than two
    assert property (@(posedge clk_i) ((status_cnt_n - status_cnt_q) < 3 || (status_cnt_n - status_cnt_q) > 3)) else $error("FIFO underflowed or overflowed");
    // assert property (
    //   @(posedge clk_i) (instr_gnt_i) |-> (instr_req_o) )
    // else $warning("There was a grant without a request");
    `endif
    `endif
endmodule