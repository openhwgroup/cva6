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
// Description: purely combinatorial PMP unit (with extraction for more complex configs such as NAPOT)

module pmp #(
    parameter int unsigned XLEN = 32,       // rv64: 64
    parameter int unsigned PMP_LEN = 32,    // rv64: 54
    parameter int unsigned NR_ENTRIES = 4
) (
    // Input
    input logic [XLEN-1:0] addr_i,
    input riscv::pmp_access_t access_type_i,
    input riscv::priv_lvl_t priv_lvl_i,
    // Configuration
    input logic [NR_ENTRIES-1:0][PMP_LEN-1:0] conf_addr_i,
    input riscv::pmpcfg_t [NR_ENTRIES-1:0] conf_i,
    // Output
    output logic allow_o
);
    logic [NR_ENTRIES-1:0] match;

    for (genvar i = 0; i < NR_ENTRIES; i++) begin
        pmp_entry #(
            .XLEN    ( XLEN    ),
            .PMP_LEN ( PMP_LEN )
        ) i_pmp_entry(
            .addr_i           ( addr_i                         ),
            .conf_addr_i      ( conf_addr_i[i]                 ),
            .conf_addr_prev_i ( i == 0 ? '0 : conf_addr_i[i-1] ),
            .conf_addr_mode_i ( conf_i[i].addr_mode            ),
            .match_o          ( match[i]                       )
        );
    end

    always_comb begin
        allow_o = 1'b1;
        if (access_type_i == 3'b000) begin
            allow_o = 1'b0;
        end else if (priv_lvl_i != riscv::PRIV_LVL_M) begin
            for (int j = 0; j < NR_ENTRIES; j++) begin
                if (match[j]) begin
                    if ((access_type_i & conf_i[j].access_type) != access_type_i) allow_o &= 1'b0;
                    else allow_o &= 1'b1;
                end
            end
        end
    end
endmodule
