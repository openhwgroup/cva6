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
// Description: TOR PMP entry

module pmp_tor_entry #(
    parameter int unsigned XLEN = 64,
    parameter int unsigned PMP_LEN = 54
) (
    input logic [XLEN-1:0] addr_i,
    input logic [PMP_LEN-1:0] conf_addr_lo_i,
    input logic [PMP_LEN-1:0] conf_addr_hi_i,

    output logic match_o
);
    logic [XLEN-1:0] addr_lo, addr_hi;
    assign addr_lo = conf_addr_lo_i << 2;
    assign addr_hi = conf_addr_hi_i << 2;
    always_comb begin
        if (addr_i >= addr_lo && addr_i < addr_hi ) begin
            match_o = '1;
        end else begin
            match_o = '0;
        end
    end

    `ifdef FORMAL
    always @(*) begin
        if (match_o == 0) begin
            assert(addr_i >= addr_hi || addr_i < addr_lo);
        end else begin
            assert(addr_i < addr_hi || addr_i >= addr_lo);
        end
    end
    `endif
endmodule