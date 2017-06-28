// Author: Florian Zaruba, ETH Zurich
// Date: 14.05.2017
// Description: Re-aligns compressed instruction
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

module instr_realigner (
    input  logic                   clk_i,               // Clock
    input  logic                   rst_ni,              // Asynchronous reset active low
    // control signals
    input  logic                   flush_i,

    input  fetch_entry             fetch_entry_0_i,
    input  logic                   fetch_entry_valid_0_i,
    output logic                   fetch_ack_0_o,

    output fetch_entry             fetch_entry_o,
    output logic                   fetch_entry_valid_o,
    input  logic                   fetch_ack_i
);
    // ----------
    // Registers
    // ----------
    // the last instruction was unaligned
    logic         unaligned_n,        unaligned_q;
    // save the unaligned part of the instruction to this ff
    logic [15:0] unaligned_instr_n,   unaligned_instr_q;
    // the previous instruction was compressed
    logic        compressed_n,        compressed_q;
    // register to save the unaligned address
    logic [63:0] unaligned_address_n, unaligned_address_q;
    // get the next instruction, needed on a unaligned access
    logic jump_unaligned_half_word;

    // check if the lower compressed instruction was no branch otherwise we will need to squash this instruction
    // but only if we predicted it to be taken, the predict was on the lower 16 bit compressed instruction
    logic kill_upper_16_bit;
    assign kill_upper_16_bit = fetch_entry_0_i.branch_predict.valid &&
                               fetch_entry_0_i.branch_predict.predict_taken &&
                               fetch_entry_0_i.branch_predict.is_lower_16;
    // ----------
    // Registers
    // ----------
    always_comb begin : realign_instr

        unaligned_n          = unaligned_q;
        unaligned_instr_n    = unaligned_instr_q;
        compressed_n         = compressed_q;
        unaligned_address_n  = unaligned_address_q;

        // directly output this instruction. adoptions are made throughout the process
        fetch_entry_o        = fetch_entry_0_i;
        fetch_entry_valid_o  = fetch_entry_valid_0_i;
        fetch_ack_0_o        = fetch_ack_i;
        // we just jumped to a half word and encountered an unaligned 32-bit instruction
        jump_unaligned_half_word = 1'b0;
        // ---------------------------------
        // Input port & Instruction Aligner
        // ---------------------------------
        // check if the entry if the fetch FIFO is valid and if we are currently not serving the second part
        // of a compressed instruction
        if (fetch_entry_valid_0_i && !compressed_q) begin
            // ------------------------
            // Access on Word Boundary
            // ------------------------
            if (fetch_entry_0_i.address[1] == 1'b0) begin
                // do we actually want the first instruction or was the address a half word access?
                if (!unaligned_q) begin
                    // we got a valid instruction so we can satisfy the unaligned instruction
                    unaligned_n = 1'b0;
                    // check if the instruction is compressed
                    if (fetch_entry_0_i.instruction[1:0] != 2'b11) begin
                        // it is compressed
                        fetch_entry_o.instruction = {15'b0, fetch_entry_0_i.instruction[15:0]};

                        // should we even look at the upper instruction bits?
                        if (!kill_upper_16_bit) begin
                            // Yes, so...
                            // 1. Is the second instruction also compressed, like:
                            // _____________________________________________
                            // | compressed 2 [31:16] | compressed 1[15:0] |
                            // |____________________________________________
                            if (fetch_entry_0_i.instruction[17:16] != 2'b11) begin
                                // yes, this was a compressed instruction
                                compressed_n = 1'b1;
                                // do not advance the queue pointer
                                fetch_ack_0_o = 1'b0;
                            // 2. or is it an unaligned 32 bit instruction like
                            // ____________________________________________________
                            // |instr [15:0] | instr [31:16] | compressed 1[15:0] |
                            // |____________________________________________________
                            end else begin
                                // save the lower 16 bit
                                unaligned_instr_n = fetch_entry_0_i.instruction[31:16];
                                // save the address
                                unaligned_address_n = {fetch_entry_0_i.address[63:2], 2'b10};
                                // and that it was unaligned
                                unaligned_n = 1'b1;
                                // this does not consume space in the FIFO
                            end
                        end
                    end
                end
                // this is a full 32 bit instruction like
                // _______________________
                // | instruction [31:0]  |
                // |______________________

                // we have an outstanding unaligned instruction
                else if (unaligned_q) begin


                    fetch_entry_o.address = unaligned_address_q;
                    fetch_entry_o.instruction = {fetch_entry_0_i.instruction[15:0], unaligned_instr_q};

                    // again should we look at the upper bits?
                    if (!kill_upper_16_bit) begin
                        // whats up with the other upper 16 bit of this instruction
                        // is the second instruction also compressed, like:
                        // _____________________________________________
                        // | compressed 2 [31:16] | unaligned[31:16]    |
                        // |____________________________________________
                        // check if the lower compressed instruction was no branch otherwise we will need to squash this instruction
                        // but only if we predicted it to be taken, the predict was on the lower 16 bit compressed instruction
                        if (fetch_entry_0_i.instruction[17:16] != 2'b11) begin
                            // this was a compressed instruction
                            compressed_n  = 1'b1;
                            // do not advance the queue pointer
                            fetch_ack_0_o = 1'b0;
                            // unaligned access served
                            unaligned_n = 1'b0;
                            // or is it an unaligned 32 bit instruction like
                        // ____________________________________________________
                        // |instr [15:0] | instr [31:16] | compressed 1[15:0] |
                        // |____________________________________________________
                        end else if (!kill_upper_16_bit) begin
                            // save the lower 16 bit
                            unaligned_instr_n = fetch_entry_0_i.instruction[31:16];
                            // save the address
                            unaligned_address_n = {fetch_entry_0_i.address[63:2], 2'b10};
                            // and that it was unaligned
                            unaligned_n = 1'b1;
                        end
                    end
                    // we've got a predicted taken branch we need to clear the unaligned flag if it was decoded as a lower 16 instruction
                    else if (fetch_entry_0_i.branch_predict.valid) begin
                        // the next fetch will start from a 4 byte boundary again
                        unaligned_n = 1'b0;
                    end
                end
            end
            // ----------------------------
            // Access on half-Word Boundary
            // ----------------------------
            else if (fetch_entry_0_i.address[1] == 1'b1) begin // address was a half word access
                // reset the unaligned flag as this is a completely new fetch (because consecutive fetches only happen on a word basis)
                unaligned_n = 1'b0;
                // this is a compressed instruction
                if (fetch_entry_0_i.instruction[17:16] != 2'b11) begin
                    // it is compressed
                    fetch_entry_o.instruction = {15'b0, fetch_entry_0_i.instruction[15:0]};

                // this is the first part of a 32 bit unaligned instruction
                end else begin
                     // save the lower 16 bit
                    unaligned_instr_n = fetch_entry_0_i.instruction[31:16];
                    // and that it was unaligned
                    unaligned_n = 1'b1;
                    // save the address
                    unaligned_address_n = {fetch_entry_0_i.address[63:2], 2'b10};
                    // we need to wait for the second instruction
                    fetch_entry_valid_o = 1'b0;
                    // so get it by acknowledging this instruction
                    fetch_ack_0_o = 1'b1;
                    // we got to an unaligned instruction -> get the next entry to full-fill the need
                    jump_unaligned_half_word = 1'b1;
                end
                // there can never be a whole 32 bit instruction on a half word access
            end
        end
        // ----------------------------
        // Next compressed instruction
        // ----------------------------
        // we are serving the second part of an instruction which was also compressed
        if (compressed_q) begin
            fetch_ack_0_o = fetch_ack_i;
            compressed_n  = 1'b0;
            fetch_entry_o.instruction = {16'b0, fetch_entry_0_i.instruction[31:16]};
            fetch_entry_o.address = {fetch_entry_0_i.address[63:2], 2'b10};
            fetch_entry_valid_o = 1'b1;
        end

        // if we didn't get an acknowledge keep the registers stable
        if (!fetch_ack_i && !jump_unaligned_half_word) begin
            unaligned_n         = unaligned_q;
            unaligned_instr_n   = unaligned_instr_q;
            compressed_n        = compressed_q;
            unaligned_address_n = unaligned_address_q;
        end

        if (flush_i) begin
            // clear the unaligned and compressed instruction
            unaligned_n  = 1'b0;
            compressed_n = 1'b0;
        end
    end

    // ---------
    // Registers
    // ---------
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (~rst_ni) begin
            unaligned_q         <= 1'b0;
            unaligned_instr_q   <= 16'b0;
            unaligned_address_q <= 64'b0;
            compressed_q        <= 1'b0;
        end else begin
            unaligned_q         <= unaligned_n;
            unaligned_instr_q   <= unaligned_instr_n;
            unaligned_address_q <= unaligned_address_n;
            compressed_q        <= compressed_n;
        end
    end

endmodule