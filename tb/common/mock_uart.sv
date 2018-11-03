// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Florian Zaruba, ETH Zurich
// Date: 28/09/2018
// Description: Mock replacement for UART in testbench

module mock_uart (
    input  logic          clk_i,
    input  logic          rst_ni,
    input  logic          penable_i,
    input  logic          pwrite_i,
    input  logic [31:0]   paddr_i,
    input  logic          psel_i,
    input  logic [31:0]   pwdata_i,
    output logic [31:0]   prdata_o,
    output logic          pready_o,
    output logic          pslverr_o
);

    // string buffer
    byte buffer [$];

    function void flush();
        string s;
        // dump the buffer out the whole buffer
        foreach (buffer[i]) begin
            s = $sformatf("%s%c",s, buffer[i]);
        end

        $display(s);

        // clear buffer afterwards
        buffer = {};
    endfunction : flush

    // put a char into the buffer
    function void append(byte ch);

        // wait for the new line
        if (ch == 8'hA)
            flush();
        else
            buffer.push_back(ch);

    endfunction : append

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (rst_ni) begin
            if (psel_i & penable_i & pwrite_i & paddr_i[3:0] == 'h4) append(byte'(pwdata_i[7:0]));
        end
    end
endmodule
