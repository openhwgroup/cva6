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
    input  logic [riscv::VLEN-1:0]            address_i,
    input  logic [FETCH_WIDTH-1:0]            data_i,
    output logic [INSTR_PER_FETCH-1:0]        valid_o,
    output logic [INSTR_PER_FETCH-1:0][riscv::VLEN-1:0]  addr_o,
    output logic [INSTR_PER_FETCH-1:0][31:0]  instr_o
);
    // as a maximum we support a fetch width of 64-bit, hence there can be 4 compressed instructions
    logic [3:0] instr_is_compressed;

    for (genvar i = 0; i < INSTR_PER_FETCH; i ++) begin
        // LSB != 2'b11
        assign instr_is_compressed[i] = ~&data_i[i * 16 +: 2];
    end

    // save the unaligned part of the instruction to this ff
    logic [15:0] unaligned_instr_d,   unaligned_instr_q;
    // the last instruction was unaligned
    logic        unaligned_d,         unaligned_q;
    // register to save the unaligned address
    logic [riscv::VLEN-1:0] unaligned_address_d, unaligned_address_q;
    // we have an unaligned instruction
    assign serving_unaligned_o = unaligned_q;

    // Instruction re-alignment
    if (FETCH_WIDTH == 32) begin : realign_bp_32
        always_comb begin : re_align
            unaligned_d = unaligned_q;
            unaligned_address_d = {address_i[riscv::VLEN-1:2], 2'b10};
            unaligned_instr_d = data_i[31:16];

            valid_o[0] = valid_i;
            instr_o[0] = (unaligned_q) ? {data_i[15:0], unaligned_instr_q} : data_i[31:0];
            addr_o[0]  = (unaligned_q) ? unaligned_address_q : address_i;

            valid_o[1] = 1'b0;
            instr_o[1] = '0;
            addr_o[1]  = {address_i[riscv::VLEN-1:2], 2'b10};

            // this instruction is compressed or the last instruction was unaligned
            if (instr_is_compressed[0] || unaligned_q) begin
                // check if this is instruction is still unaligned e.g.: it is not compressed
                // if its compressed re-set unaligned flag
                // for 32 bit we can simply check the next instruction and whether it is compressed or not
                // if it is compressed the next fetch will contain an aligned instruction
                // is instruction 1 also compressed
                // yes? -> no problem, no -> we've got an unaligned instruction
                if (instr_is_compressed[1]) begin
                    unaligned_d = 1'b0;
                    valid_o[1] = valid_i;
                    instr_o[1] = {16'b0, data_i[31:16]};
                end else begin
                    // save the upper bits for next cycle
                    unaligned_d = 1'b1;
                    unaligned_instr_d = data_i[31:16];
                    unaligned_address_d = {address_i[riscv::VLEN-1:2], 2'b10};
                end
            end // else -> normal fetch

            // we started to fetch on a unaligned boundary with a whole instruction -> wait until we've
            // received the next instruction
            if (valid_i && address_i[1]) begin
                // the instruction is not compressed so we can't do anything in this cycle
                if (!instr_is_compressed[0]) begin
                    valid_o = '0;
                    unaligned_d = 1'b1;
                    unaligned_address_d = {address_i[riscv::VLEN-1:2], 2'b10};
                    unaligned_instr_d = data_i[15:0];
                // the instruction isn't compressed but only the lower is ready
                end else begin
                    valid_o = 1'b1;
                end
            end
        end
    // TODO(zarubaf): Fix 64 bit FETCH_WIDTH, maybe generalize to arbitrary fetch width
    end else if (FETCH_WIDTH == 64) begin : realign_bp_64
        initial begin
          $error("Not propperly implemented");
        end
        always_comb begin : re_align
            unaligned_d = unaligned_q;
            unaligned_address_d = unaligned_address_q;
            unaligned_instr_d = unaligned_instr_q;

            valid_o    = '0;
            valid_o[0] = valid_i;

            instr_o[0] = data_i[31:0];
            addr_o[0]  = address_i;

            instr_o[1] = '0;
            addr_o[1]  = {address_i[riscv::VLEN-1:3], 3'b010};

            instr_o[2] = {16'b0, data_i[47:32]};
            addr_o[2]  = {address_i[riscv::VLEN-1:3], 3'b100};

            instr_o[3] = {16'b0, data_i[63:48]};
            addr_o[3]  = {address_i[riscv::VLEN-1:3], 3'b110};

            // last instruction was unaligned
            if (unaligned_q) begin
                instr_o[0] = {data_i[15:0], unaligned_instr_q};
                addr_o[0] = unaligned_address_q;
                // for 64 bit there exist the following options:
                //     64      32      0
                //     | 3 | 2 | 1 | 0 | <- instruction slot
                // |   I   |   I   |   U   | -> again unaligned
                // | * | C |   I   |   U   | -> aligned
                // | * |   I   | C |   U   | -> aligned
                // |   I   | C | C |   U   | -> again unaligned
                // | * | C | C | C |   U   | -> aligned
                // Legend: C = compressed, I = 32 bit instruction, U = unaligned upper half
                //         * = don't care
                if (instr_is_compressed[1]) begin
                    instr_o[1] = {16'b0, data_i[31:16]};
                    valid_o[1] = valid_i;

                    if (instr_is_compressed[2]) begin
                        if (instr_is_compressed[3]) begin
                            unaligned_d = 1'b0;
                            valid_o[3] = valid_i;
                        end else begin
                            // continues to be unaligned
                        end
                    end else begin
                        unaligned_d = 1'b0;
                        instr_o[2] = data_i[63:32];
                        valid_o[2] = valid_i;
                    end
                // instruction 1 is not compressed
                end else begin
                    instr_o[1] = data_i[47:16];
                    valid_o[1] = valid_i;
                    addr_o[2] = {address_i[riscv::VLEN-1:3], 3'b110};
                    if (instr_is_compressed[2]) begin
                        unaligned_d = 1'b0;
                        instr_o[2] = {16'b0, data_i[63:48]};
                        valid_o[2] = valid_i;
                    end else begin
                        // continues to be unaligned
                    end
                end
            end else if (instr_is_compressed[0]) begin // instruction zero is RVC
                //     64     32       0
                //     | 3 | 2 | 1 | 0 | <- instruction slot
                // |   I   |   I   | C | -> again unaligned
                // | * | C |   I   | C | -> aligned
                // | * |   I   | C | C | -> aligned
                // |   I   | C | C | C | -> again unaligned
                // | * | C | C | C | C | -> aligned
                if (instr_is_compressed[1]) begin
                    instr_o[1] = {16'b0, data_i[31:16]};
                    valid_o[1] = valid_i;

                    if (instr_is_compressed[2]) begin
                        valid_o[2] = valid_i;
                        if (instr_is_compressed[3]) begin
                            valid_o[3] = valid_i;
                        end else begin
                            // this instruction is unaligned
                            unaligned_d = 1'b1;
                            unaligned_instr_d = data_i[63:48];
                            unaligned_address_d = addr_o[3];
                        end
                    end else begin
                        instr_o[2] = data_i[63:32];
                        valid_o[2] = valid_i;
                    end
                // instruction 1 is not compressed -> check slot 3
                end else begin
                    instr_o[1] = data_i[47:16];
                    valid_o[1] = valid_i;
                    addr_o[2] = {address_i[riscv::VLEN-1:3], 3'b110};
                    if (instr_is_compressed[3]) begin
                        instr_o[2] = data_i[63:48];
                        valid_o[2] = valid_i;
                    end else begin
                        unaligned_d = 1'b1;
                        unaligned_instr_d = data_i[63:48];
                        unaligned_address_d = addr_o[2];
                    end
                end

            // Full instruction in slot zero
            //     64     32       0
            //     | 3 | 2 | 1 | 0 | <- instruction slot
            // |   I   | C |   I   |
            // | * | C | C |   I   |
            // | * |   I   |   I   |
            end else begin
                addr_o[1] = {address_i[riscv::VLEN-1:3], 3'b100};

                if (instr_is_compressed[2]) begin
                    instr_o[1] = {16'b0, data_i[47:32]};
                    valid_o[1] = valid_i;
                    addr_o[2] = {address_i[riscv::VLEN-1:3], 3'b110};
                    if (instr_is_compressed[3]) begin
                        // | * | C | C |   I   |
                        valid_o[2] = valid_i;
                        addr_o[2] = {16'b0, data_i[63:48]};
                    end else begin
                        // this instruction is unaligned
                        unaligned_d = 1'b1;
                        unaligned_instr_d = data_i[63:48];
                        unaligned_address_d = addr_o[2];
                    end
                end else begin
                    // two regular instructions back-to-back
                    instr_o[1] = data_i[63:32];
                    valid_o[1] = valid_i;
                end
            end

            // --------------------------
            // Unaligned fetch
            // --------------------------
            // Address was not 64 bit aligned
            case (address_i[2:1])
                // this means the previouse instruction was either compressed or unaligned
                // in any case we don't ccare
                2'b01: begin
                    //     64     32       0
                    //     | 3 | 2 | 1 | 0 | <- instruction slot
                    // |   I   |   I   | x  -> again unaligned
                    // | * | C |   I   | x  -> aligned
                    // | * |   I   | C | x  -> aligned
                    // |   I   | C | C | x  -> again unaligned
                    // | * | C | C | C | x  -> aligned
                    addr_o[0] = {address_i[riscv::VLEN-1:3], 3'b010};

                    if (instr_is_compressed[1]) begin
                        instr_o[0] = {16'b0, data_i[31:16]};
                        valid_o[0] = valid_i;

                        if (instr_is_compressed[2]) begin
                            valid_o[1] = valid_i;
                            instr_o[1] = {16'b0, data_i[47:32]};
                            addr_o[1] = {address_i[riscv::VLEN-1:3], 3'b100};
                            if (instr_is_compressed[3]) begin
                                instr_o[2] = {16'b0, data_i[63:48]};
                                addr_o[2] = {address_i[riscv::VLEN-1:3], 3'b110};
                                valid_o[2] = valid_i;
                            end else begin
                                // this instruction is unaligned
                                unaligned_d = 1'b1;
                                unaligned_instr_d = data_i[63:48];
                                unaligned_address_d = addr_o[3];
                            end
                        end else begin
                            instr_o[1] = data_i[63:32];
                            addr_o[1] = {address_i[riscv::VLEN-1:3], 3'b100};
                            valid_o[1] = valid_i;
                        end
                    // instruction 1 is not compressed -> check slot 3
                    end else begin
                        instr_o[0] = data_i[47:16];
                        valid_o[0] = valid_i;
                        addr_o[1] = {address_i[riscv::VLEN-1:3], 3'b110};
                        if (instr_is_compressed[3]) begin
                            instr_o[1] = data_i[63:48];
                            valid_o[1] = valid_i;
                        end else begin
                            unaligned_d = 1'b1;
                            unaligned_instr_d = data_i[63:48];
                            unaligned_address_d = addr_o[1];
                        end
                    end
                end
                2'b10: begin
                    valid_o = '0;
                    //     64     32       0
                    //     | 3 | 2 | 1 | 0 | <- instruction slot
                    // |   I   | C |   *   | <- unaligned
                    //    | C  | C |   *   | <- aligned
                    //    |    I   |   *   | <- aligned
                    if (instr_is_compressed[2]) begin
                        valid_o[0] = valid_i;
                        instr_o[0] = data_i[47:32];
                        // second instruction is also compressed
                        if (instr_is_compressed[3]) begin
                            valid_o[1] = valid_i;
                            instr_o[1] = data_i[63:48];
                        // regular instruction -> unaligned
                        end else begin
                            unaligned_d = 1'b1;
                            unaligned_address_d = {address_i[riscv::VLEN-1:3], 3'b110};
                            unaligned_instr_d = data_i[63:48];
                        end
                    // instruction is a regular instruction
                    end else begin
                        valid_o[0] = valid_i;
                        instr_o[0] = data_i[63:32];
                        addr_o[0] = address_i;
                    end
                end
                // we started to fetch on a unaligned boundary with a whole instruction -> wait until we've
                // received the next instruction
                2'b11: begin
                    valid_o = '0;
                    if (!instr_is_compressed[3]) begin
                        unaligned_d = 1'b1;
                        unaligned_address_d = {address_i[riscv::VLEN-1:3], 3'b110};
                        unaligned_instr_d = data_i[63:48];
                    end else begin
                        valid_o[3] = valid_i;
                    end
                end
            endcase
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
