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

module mock_uartlite (
    input logic clk_i,    // Clock
    input logic rst_ni,
    AXI_BUS.Slave slave
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

    // put a char to the buffer
    function void append(byte ch);

        // wait for the new line
        if (ch == 8'hA)
            flush();
        else
            buffer.push_back(ch);

    endfunction : append

    logic req_o;
    logic we_o;
    logic [63:0] addr_o;
    logic [64/8-1:0] be_o;
    logic [63:0] data_o;

    axi2mem #(
        .AXI_ID_WIDTH($bits(slave.aw_id)),
        .AXI_USER_WIDTH($bits(slave.aw_user))
    ) i_axi2mem (
        .clk_i  ( clk_i  ),
        .rst_ni ( rst_ni ),
        .slave  ( slave  ),
        .req_o  ( req_o  ),
        .we_o   ( we_o   ),
        .addr_o ( addr_o ),
        .be_o   ( be_o   ),
        .data_o ( data_o ),
        .data_i ( '0     )
    );

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (rst_ni) begin
            if (req_o & we_o & addr_o[3:0] == 'h4) append(byte'(data_o[40:32]));
        end
    end
endmodule