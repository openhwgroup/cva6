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
// Description: NAPOT PMP entry

module pmp_napot_entry #(
    parameter int unsigned XLEN = 64,
    parameter int unsigned PMP_LEN = 54
) (
    input logic [XLEN-1:0] addr_i,
    input logic [PMP_LEN-1:0] conf_addr_i,

    output logic match_o
);
    int unsigned size;

    napot_extract #(.PMP_LEN(PMP_LEN)) i_napot_extract (
        .conf_addr_i,
        .size_o(size)
    );

    always_comb begin
        logic [XLEN-1:0] padded_addr;
        logic [XLEN-1:0] mask;
        logic [XLEN-1:0] base;

        mask = '1 << size;
        // pad the addr such that size_i lower bits are zero
        padded_addr = addr_i & mask;

        base = (conf_addr_i << 2) & mask;

        if (padded_addr == base) begin
            match_o = '1; 
        end else begin
            match_o = '0;
        end

    end

    `ifdef FORMAL
    always @(*) begin
        logic[XLEN-1:0] base_lo;
        logic[XLEN:0] base_hi; 
        base_lo = (conf_addr_i << 2) & ('1 << size);
        base_hi = base_lo + 2**size;
        if (base_hi < base_lo) begin
            base_hi = '1;
        end
        if (size < XLEN) begin
            if (match_o == 0) begin
                assert(addr_i >= base_hi || addr_i < base_lo);
            end else begin
                assert(addr_i < base_hi && addr_i >= base_lo);
            end
        end else begin
            assert(match_o == 1);
        end
    end
    `endif

endmodule