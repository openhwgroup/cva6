// Copyright 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Moritz Schneider, ETH Zurich
// Date: 2.10.2019
// Description: single PMP entry

module pmp_entry #(
    parameter int unsigned XLEN = 64,
    parameter int unsigned PMP_LEN = 54
) (
    // Input
    input logic [XLEN-1:0] addr_i,

    // Configuration
    input logic [PMP_LEN-1:0] conf_addr_i,
    input logic [PMP_LEN-1:0] conf_addr_prev_i,
    input riscv::pmp_addr_mode_t conf_addr_mode_i,

    // Output
    output logic match_o
);
    logic [3:0] match;

    pmp_tor_entry #(
        .XLEN(XLEN),
        .PMP_LEN(PMP_LEN)
    ) i_pmp_tor_entry(
    	.addr_i,
        .conf_addr_lo_i (conf_addr_prev_i),
        .conf_addr_hi_i (conf_addr_i ),
        .match_o        (match[riscv::TOR])
    );

    pmp_na4_entry #(
        .XLEN(XLEN),
        .PMP_LEN(PMP_LEN)
    ) i_pmp_na4_entry(
    	.addr_i,
        .conf_addr_i,
        .match_o     (match[riscv::NA4])
    );

    pmp_napot_entry #(
        .XLEN(XLEN),
        .PMP_LEN(PMP_LEN)
    ) i_pmp_napot_entry(
    	.addr_i,
        .conf_addr_i,
        .match_o     (match[riscv::NAPOT])
    );

    assign match[riscv::OFF] = 0;

    always_comb begin
        unique case (conf_addr_mode_i)
            riscv::TOR:     match_o = match[riscv::TOR];
            riscv::NA4:     match_o = match[riscv::NA4];
            riscv::NAPOT:   match_o = match[riscv::NAPOT];
            riscv::OFF:     match_o = match[riscv::OFF];
            default: match_o = 0;
        endcase
    end

    `ifdef FORMAL
    always @(*) begin
        if(conf_addr_mode_i == riscv::OFF) begin
            assert(match_o == '0);
        end
    end
    `endif

endmodule