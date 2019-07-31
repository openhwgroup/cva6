// Copyright 2018 - 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Florian Zaruba <zarubaf@iis.ee.ethz.ch>
// Description: Instruction Re-aligner
//
// This module takes 32-bit aligned cache blocks and extracts the instructions.
// As we are supporting the compressed instruction set extension in a 32 bit instruction word
// are up to 2 compressed instructions.
// Furthermore those instructions can be arbitrarily interleaved which makes it possible to fetch
// only the lower part of a 32 bit instruction.
// Furthermore we need to handle the case if we want to start fetching from an unaligned
// instruction e.g. a branch.

import ariane_pkg::*;

module instr_realign (
    input  logic                              clk_i,
    input  logic                              rst_ni,
    input  logic                              flush_i,
    input  logic                              valid_i,
    output logic                              serving_unaligned_o, // we have an unaligned instruction in [0]
    output logic [63:0]                       serving_unaligned_address_o,
    input  logic [63:0]                       address_i,
    input  logic [FETCH_WIDTH-1:0]            data_i,
    output logic [INSTR_PER_FETCH-1:0]        valid_o,
    output logic [INSTR_PER_FETCH-1:0][63:0]  addr_o,
    output logic [INSTR_PER_FETCH-1:0][31:0]  instr_o
);
    // point to the start position of each valid instruction and address
    // for example, if it is a 64 bit fetch block, the address is 0xabcd000 the data is
    //     64     32       0
    //     | 3 | 2 | 1 | 0 | <- instruction slot
    //     | C |   I   | C |
    // then the valid_instr_pos will be 0, 16, 48
    // valid instr_block_idx will be 0, 1, 3
    // valid_instr_address will be 0xabcd000, 0xabcd002, 0xabcd006
    logic [INSTR_PER_FETCH:0][$clog2(FETCH_WIDTH):0]         valid_instr_pos;
    logic [INSTR_PER_FETCH:0][$clog2(INSTR_PER_FETCH):0]     valid_instr_block_idx;
    logic [INSTR_PER_FETCH:0][63:0]                          valid_instr_address;

    // determine whether each 16 bit sub-block is a compressed instruction by the LSB
    logic [INSTR_PER_FETCH-1:0] instr_is_compressed;
    for (genvar i = 0; i < INSTR_PER_FETCH; i ++) begin
        // LSB != 2'b11
        assign instr_is_compressed[i] = RVC && (~&data_i[i * 16 +: 2]);
    end

    // save the unaligned part of the instruction to this ff
    logic [15:0] unaligned_instr_d,   unaligned_instr_q;
    // the last instruction was unaligned
    logic        unaligned_d,         unaligned_q;
    // register to save the unaligned address
    logic [63:0] unaligned_address_d, unaligned_address_q;
    // we have an unaligned instruction
    assign serving_unaligned_o = unaligned_q;
    assign serving_unaligned_address_o = unaligned_address_q;

    // instruction re-alignment
    always_comb begin : re_align
        // default to be not unaligned
        unaligned_d = 1'b0;
        // unaligned address can only be the last sub-block if it exists
        unaligned_address_d = {address_i[63:NR_ALIGN_BITS], NR_ALIGN_BITS'(-2)};
        // unaligned instr can only be the last 16 bit of data if it exists
        unaligned_instr_d = data_i[(FETCH_WIDTH-1) -: 16];

        // default to be invalid for all instrucitions
        valid_o = '0;
        instr_o = '0;

        // reset the pointers to the begining of the data
        valid_instr_pos = '0;
        valid_instr_block_idx = '0;
        valid_instr_address = '{default:address_i};

        if (address_i[NR_ALIGN_BITS-1:1] != NR_ALIGN_BITS'(0)) begin
            valid_instr_address[0] = address_i;
        end

        // iteratively realign the rest instructions
        for (int unsigned i = 0; i < INSTR_PER_FETCH; i++) begin : gen_instr_realign

            // there could be valid instruction if two conditions are met
            // 1) the current valid_instr_pos is less than the FETCH_WDITH
            // For example, 0, 16 32, is less than 64 but when the valid_instr_pos is 64
            // we went through all the input data
            // 2) the address is less than between this aligned address and next aligned address.
            // For example, if the address is unaligned and the address is 0xabcd0004
            //     64     32       0
            //     | 3 | 2 | 1 | 0 | <- instruction slot
            //     | C | C |   *   |
            // the output instructions will only be valid at 0xabcd0004 and 0xabcd0006, and they are
            // the first 32 bits of the data
            if ((valid_instr_pos[i] < FETCH_WIDTH) &
                (valid_instr_address[i] < {(address_i[63:NR_ALIGN_BITS]+1'b1), NR_ALIGN_BITS'(0)})) begin
                valid_o[i] = valid_i;
                addr_o[i] = valid_instr_address[i];

                // if last instruction is unaligned
                if (unaligned_q && i == 0) begin
                    instr_o[0] = {data_i[15:0], unaligned_instr_q};
                    addr_o[0] = unaligned_address_q;
                    valid_instr_pos[i+1] = valid_instr_pos[i] + 16;
                    valid_instr_block_idx[i+1] = valid_instr_block_idx[i] + 1;
                    valid_instr_address[i+1] = valid_instr_address[i] + 2;
                end
                // if it is a compressed instruction, append the data with zeros,
                // increment the pointer by 1 sub-block (16 bits)
                else if (instr_is_compressed[valid_instr_block_idx[i]]) begin
                    instr_o[i] = {16'b0, data_i[valid_instr_pos[i] +: 16]};
                    valid_instr_pos[i+1] = valid_instr_pos[i] + 16;
                    valid_instr_block_idx[i+1] = valid_instr_block_idx[i] + 1;
                    valid_instr_address[i+1] = valid_instr_address[i] + 2;
                end
                // if it is a 32 bit instruction, we could have two situations:
                // 1) if it is the last unaligned instruction, set the flag
                // 2) if it is a normal 32 bit instruction, output the instruction
                else begin
                    valid_instr_pos[i+1] = valid_instr_pos[i] + 32;
                    valid_instr_block_idx[i+1] = valid_instr_block_idx[i] + 2;
                    valid_instr_address[i+1] = valid_instr_address[i] + 4;

                    // if the last insruction is unaligned and the address is aligned, for example,
                    //     64     32       0
                    //     | 3 | 2 | 1 | 0 | <- instruction slot
                    // |   I   | C |   I   |
                    // we store the lower part of the instruction that is used in next cycle and
                    // set the unaligned flag
                    if (valid_instr_pos[i] == (FETCH_WIDTH - 16)) begin
                        unaligned_d = 1'b1;
                        valid_o[i] = 1'b0;
                    end
                    // if the last insruction is unaligned and the address is unaligned, for example,
                    //     64     32       0
                    //     | 3 | 2 | 1 | 0 | <- instruction slot
                    // |   I   | C |   *   |
                    // we store the lower part of the instruction that is used in next cycle and
                    // set the unaligned flag
                    else if (valid_instr_address[i] == unaligned_address_d) begin
                        unaligned_d = 1'b1;
                        valid_o[i] = 1'b0;
                        unaligned_instr_d = data_i[valid_instr_pos[i] +: 16];
                    end
                    else begin
                        instr_o[i] = data_i[valid_instr_pos[i] +: 32];
                    end
                end
            end
            // no more valid instruction exists
            else begin
              valid_instr_pos[i+1] = FETCH_WIDTH;
              valid_o[i] = 1'b0;
            end
        end
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (~rst_ni) begin
            unaligned_q         <= 1'b0;
            unaligned_address_q <= '0;
            unaligned_instr_q   <= '0;
        end else begin
            if (valid_i) begin
                unaligned_address_q <= unaligned_address_d;
                unaligned_instr_q   <= unaligned_instr_d;
            end

            if (flush_i) begin
                unaligned_q <= 1'b0;
            end else if (valid_i) begin
                unaligned_q <= unaligned_d;
            end
        end
    end
endmodule
