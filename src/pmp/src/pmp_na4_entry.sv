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
// Description: NA4 PMP entry

module pmp_na4_entry #(
    parameter int unsigned XLEN = 64,
    parameter int unsigned PMP_LEN = 54
) (
    input logic [XLEN-1:0] addr_i,
    input logic [PMP_LEN-1:0] conf_addr_i,

    output logic match_o
);
    always_comb begin
        logic [XLEN-1:0] base;
        logic [XLEN-1:0] padded_addr;
        logic [XLEN-1:0] mask;

        mask = '1 << 2;
        // pad the addr such that size_i lower bits are zero
        padded_addr = addr_i & mask;

        base = (conf_addr_i << 2) & mask;

        if (padded_addr == base) begin
            match_o = '1; 
        end else begin
            match_o = '0;
        end

        `ifdef FORMAL
        if (base + 2**2 > base) begin // check for overflow
            if (match_o == 0) begin
                assert(addr_i >= base + 2**2 || addr_i < base);
            end else begin
                assert(addr_i < base + 2**2 && addr_i >= base);
            end
        end else begin
            if (match_o == 0) begin
                assert(addr_i - 2**2 >= base || addr_i < base);
            end else begin
                assert(addr_i - 2**2 < base && addr_i >= base);
            end
        end
        `endif
    end
endmodule