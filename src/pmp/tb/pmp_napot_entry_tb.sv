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

import tb_pkg::*;

module pmp_napot_entry_tb;
    timeunit 1ns;
    timeprecision 1ps;

    localparam int unsigned WIDTH = 16;
    localparam int unsigned PMP_LEN = 13;

    logic[WIDTH-1:0] addr;
    logic[WIDTH-1:0] base;
    int unsigned size;

    logic[PMP_LEN-1:0] conf_addr;

    logic out;

    pmp_napot_entry #(.XLEN(WIDTH), .PMP_LEN(PMP_LEN)) 
        i_iopmp(
            .addr_i(addr),
            .conf_addr_i(conf_addr),
            .match_o(out)
        );

    initial begin
        addr = 16'b00011001_10111010;
        base = 16'b00011001_10110000;
        size = 4;
        conf_addr = P#(.WIDTH(WIDTH), .PMP_LEN(PMP_LEN))::base_to_conf(base, size);
        assert(conf_addr == 16'b00000110_01101101);
        #5ns;
        assert(out == 1);
        addr = 16'b00011001_10110000;
        base = 16'b00011001_10100000;
        size = 4;
        conf_addr = P#(.WIDTH(WIDTH), .PMP_LEN(PMP_LEN))::base_to_conf(base, size);
        #5ns;
        assert(out == 0);
        addr = 16'b00011001_10111000;
        base = 16'b00011001_10100000;
        size = 5;
        conf_addr = P#(.WIDTH(WIDTH), .PMP_LEN(PMP_LEN))::base_to_conf(base, size);
        #5ns;
        assert(out == 1);
        addr = 16'b00011001_10111000;
        base = 16'b00011001_10100000;
        size = 6;
        conf_addr = P#(.WIDTH(WIDTH), .PMP_LEN(PMP_LEN))::base_to_conf(base, size);
        #5ns;
        assert(out == 1);
    end
endmodule