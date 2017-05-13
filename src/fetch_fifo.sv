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
//                                                                            //
// Engineer:       Andreas Traber - atraber@iis.ee.ethz.ch                    //
//                                                                            //
// Design Name:    Fetch Fifo for 32 bit memory interface                     //
// Project Name:   zero-riscy                                                 //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Fetch fifo                                                 //
////////////////////////////////////////////////////////////////////////////////

import ariane_pkg::*;

// input port: send address one cycle before the data
// clear_i clears the FIFO for the following cycle.
module fetch_fifo
(
    input  logic                   clk_i,
    input  logic                   rst_ni,
    // control signals
    input  logic                   clear_i,          // clears the contents of the fifo
    // input port
    // branch prediction at in_addr_i address, as this is an address and not PC it can be the case
    // that we have two compressed instruction (or one compressed instruction and one unaligned instruction) so we need
    // keep two prediction inputs: [c1|c0] <- prediction for c1 and c0
    input  branchpredict_sbe       branch_predict_i,
    input  logic [63:0]            in_addr_i,
    input  logic [31:0]            in_rdata_i,
    input  logic                   in_valid_i,
    output logic                   in_ready_o,
    // output port
    output branchpredict_sbe [1:0] branch_predict_o,
    output logic [63:0]            out_addr_o,
    output logic [31:0]            out_rdata_o,
    output logic                   out_valid_o,
    input  logic                   out_ready_i

);

    localparam DEPTH = 4; // must be 3 or greater
    typedef struct packed {
        branchpredict_sbe branch_predict;
        logic [63:0]      address;
        logic [31:0]      instruction;
    } fetch_entry;
    // input registers - bounding the path from memory
    branchpredict_sbe       branch_predict_n, branch_predict_q;
    logic [63:0]            in_addr_n,        in_addr_q;
    logic [31:0]            in_rdata_n,       in_rdata_q;
    logic                   in_valid_n,       in_valid_q;

    fetch_entry mem_n[DEPTH-1:0], mem_q[DEPTH-1:0];
    logic [$clog2(DEPTH)-1:0]     read_pointer_n, read_pointer_q;
    logic [$clog2(DEPTH)-1:0]     write_pointer_n, write_pointer_q;
    int unsigned status_cnt_n, status_cnt_q; // this integer will be truncated by the synthesis tool

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
    assign full        = (status_cnt_q == DEPTH - 2);
    assign empty       = (status_cnt_q == 0);
    assign out_valid_o = ~empty;
    assign in_ready_o  = ~full;

    // Output assignments
    assign branch_predict_o = mem_q[read_pointer_q].branch_predict;
    assign out_addr_o       = mem_q[read_pointer_q].address;
    assign out_rdata_o      = mem_q[read_pointer_q].instruction;

    // ----------------
    // Input Registers
    // ----------------
    always_comb begin
        // if we are not ready latch the values
        in_addr_n           = in_addr_q;
        in_rdata_n          = in_rdata_q;
        in_valid_n          = in_rdata_q;
        branch_predict_n    = branch_predict_q;
        // if we are ready to accept new data - do so!
        if (out_valid_o) begin
            in_addr_n        = in_addr_i;
            in_rdata_n       = in_rdata_i;
            in_valid_n       = in_valid_i;
            branch_predict_n = branch_predict_i;
        end
        // flush the input registers
        if (clear_i) begin
            in_valid_n = 1'b0;
        end
    end

    // --------------
    // FIFO Management
    // --------------
    always_comb begin : output_port
        // counter
        automatic int status_cnt    = status_cnt_q;
        automatic int write_pointer = write_pointer_q;

        write_pointer_n     = write_pointer_q;
        read_pointer_n      = read_pointer_q;
        mem_n               = mem_q;
        unaligned_n         = unaligned_q;
        unaligned_instr_n   = unaligned_instr_q;
        unaligned_address_n = unaligned_address_q;
        // ---------------------------------
        // Input port & Instruction Aligner
        // ---------------------------------
        if (in_valid_i && !unaligned_q) begin
            // we got a valid instruction so we can satisfy the unaligned instruction
            unaligned_n = 1'b0;
            // check if the instruction is compressed
            if(in_rdata_i[1:0] != 2'b11) begin
                // it is compressed
                mem_n[write_pointer_q].branch_predict = branch_predict_q;
                mem_n[write_pointer_q].address        = in_addr_q;
                mem_n[write_pointer_q].instruction    = in_rdata_q[15:0];

                status_cnt++;
                write_pointer++;
                // is the second instruction also compressed, like:
                // _____________________________________________
                // | compressed 2 [31:16] | compressed 1[15:0] |
                // |____________________________________________
                if (in_rdata_i[17:16] != 2'b11) begin
                    mem_n[write_pointer_q + 1].branch_predict = branch_predict_q;
                    mem_n[write_pointer_q + 1].address        = {in_addr_q[63:2], 2'b10};
                    mem_n[write_pointer_q + 1].instruction    = in_rdata_q[31:16];

                    status_cnt++;
                    write_pointer++;
                // or is it an unaligned 32 bit instruction like
                // ____________________________________________________
                // |instr [15:0] | instr [31:16] | compressed 1[15:0] |
                // |____________________________________________________
                end else begin
                    // we've got an unaligned 32 bit instruction
                    // save the lower 16 bit
                    unaligned_instr_n = in_rdata_q[31:16];
                    // and that it was unaligned
                    unaligned_n = 1'b1;
                    // save the address as well
                    unaligned_address_n = {in_addr_q[63:2], 2'b10};
                    // this does not consume space in the FIFO
                end
            end else begin
                // this is a full 32 bit instruction like
                // _______________________
                // | instruction [31:0]  |
                // |______________________
                mem_n[write_pointer_q].branch_predict = branch_predict_q;
                mem_n[write_pointer_q].address        = in_addr_q;
                mem_n[write_pointer_q].instruction    = in_rdata_q;
                status_cnt++;
                write_pointer++;
            end
        end
        // we have an outstanding unaligned instruction
        if (in_valid_i && unaligned_q) begin
            mem_n[write_pointer_q].branch_predict = branch_predict_q;
            mem_n[write_pointer_q].address        = unaligned_address_q;
            mem_n[write_pointer_q].instruction    = {in_rdata_q[15:0], unaligned_instr_q};
            status_cnt++;
            write_pointer++;
            // whats up with the other upper 16 bit of this instruction
            // is the second instruction also compressed, like:
            // _____________________________________________
            // | compressed 2 [31:16] | compressed 1[15:0] |
            // |____________________________________________
            if (in_rdata_i[17:16] != 2'b11) begin
                mem_n[write_pointer_q + 1].branch_predict = branch_predict_q;
                mem_n[write_pointer_q + 1].address        = {in_addr_q[63:2], 2'b10};
                mem_n[write_pointer_q + 1].instruction    = in_rdata_q[31:16];
                status_cnt++;
                write_pointer++;
                // unaligned access served
                unaligned_n = 1'b0;
            // or is it an unaligned 32 bit instruction like
            // ____________________________________________________
            // |instr [15:0] | instr [31:16] | compressed 1[15:0] |
            // |____________________________________________________
            end else begin
                // we've got an unaligned 32 bit instruction
                // save the lower 16 bit
                unaligned_instr_n = in_rdata_q[31:16];
                // and that it was unaligned
                unaligned_n = 1'b1;
                // save the address as well
                unaligned_address_n = {in_addr_q[63:2], 2'b10};
                // this does not consume space in the FIFO
            end
        end

        // -------------
        // Output port
        // -------------
        // we are ready to accept a new request if we still have two places in the queue
        if (out_ready_i) begin
            read_pointer_n = read_pointer_q + 1;
            status_cnt--;
        end
        write_pointer_n = write_pointer;
        status_cnt_n    = status_cnt;

        if (clear_i)
            status_cnt_n = '0;

    end

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (~rst_ni) begin
            status_cnt_q        <= '{default: 0};
            mem_q               <= '{default: 0};
            read_pointer_q      <= '{default: 0};
            write_pointer_q     <= '{default: 0};
            unaligned_q         <= 1'b0;
            unaligned_instr_q   <= 16'b0;
            unaligned_address_q <= 64'b0;
            // input registers
            in_addr_q           <= 64'b0;
            in_rdata_q          <= 32'b0;
            in_valid_q          <= 1'b0;
            branch_predict_q    <= '{default: 0};
        end else begin
            status_cnt_q        <= status_cnt_n;
            mem_q               <= mem_n;
            read_pointer_q      <= read_pointer_n;
            write_pointer_q     <= write_pointer_n;
            unaligned_q         <= unaligned_n;
            unaligned_instr_q   <= unaligned_instr_n;
            unaligned_address_q <= unaligned_address_n;
            // input registers
            in_addr_q           <= in_addr_n;
            in_rdata_q          <= in_rdata_n;
            in_valid_q          <= in_rdata_n;
            branch_predict_q    <= branch_predict_n;
        end
    end
endmodule