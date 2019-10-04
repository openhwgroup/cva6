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
// Description: 

module pmp_tor_entry_tb;
    timeunit 1ns;
    timeprecision 1ps;

    localparam int unsigned WIDTH = 16;
    localparam int unsigned PMP_LEN = 13;

    logic[WIDTH-1:0] addr;
    logic[PMP_LEN-1:0] addr_lo;
    logic[PMP_LEN-1:0] addr_hi;

    logic out;

    pmp_tor_entry #(.XLEN(WIDTH), .PMP_LEN(PMP_LEN)) 
        i_iopmp(
            .addr_i(addr),
            .conf_addr_lo_i(addr_lo),
            .conf_addr_hi_i(addr_hi),
            .match_o(out)
        );

    initial begin
        addr = 16'h1a54;
        addr_lo = 16'h1a53 >> 2;
        addr_hi = 16'h1a5F >> 2;
        #5ns;
        assert(out == 1);
        addr = 16'h1a54;
        addr_lo = 16'h1a54 >> 2;
        addr_hi = 16'h1a5F >> 2;
        #5ns;
        assert(out == 1);
        addr = 16'h1a54;
        addr_lo = 16'h1a50 >> 2;
        addr_hi = 16'h1a54 >> 2;
        #5ns;
        assert(out == 0);
        addr = 16'h1a50;
        addr_lo = 16'h1a54 >> 2;
        addr_hi = 16'h1a5F >> 2;
        #5ns;
        assert(out == 0);
    end
endmodule