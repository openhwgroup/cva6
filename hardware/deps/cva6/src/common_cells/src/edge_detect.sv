// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Author: Florian Zaruba
// Description: Edge detector, clock needs to oversample for proper edge detection

module edge_detect (
    input  logic clk_i,   // Clock
    input  logic rst_ni,  // Asynchronous reset active low
    input  logic d_i,     // data stream in
    output logic re_o,    // rising edge detected
    output logic fe_o     // falling edge detected
);

    sync_wedge i_sync_wedge (
        .clk_i    ( clk_i  ),
        .rst_ni   ( rst_ni ),
        .en_i     ( 1'b1   ),
        .serial_i ( d_i    ),
        .r_edge_o ( re_o   ),
        .f_edge_o ( fe_o   ),
        .serial_o (        )
    );

endmodule