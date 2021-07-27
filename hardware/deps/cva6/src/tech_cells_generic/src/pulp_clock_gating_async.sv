// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

module pulp_clock_gating_async
(
    input  logic clk_i,
    input  logic rstn_i,
    input  logic en_async_i,
    output logic en_ack_o,
    input  logic test_en_i,
    output logic clk_o
);

    logic     r_sync_0;
    logic     r_sync_1;

    assign en_ack_o = r_sync_1;
    
    always_ff @ (posedge clk_i or negedge rstn_i)
    begin
        if(~rstn_i)
        begin
            r_sync_0 <= 1'b0;
            r_sync_1 <= 1'b0;
        end
        else
        begin
            r_sync_0 <= en_async_i;
            r_sync_1 <= r_sync_0;
        end
    end

    pulp_clock_gating i_clk_gate
    (
        .clk_i    ( clk_i     ),
        .en_i     ( r_sync_1  ),
        .test_en_i( test_en_i ),
        .clk_o    ( clk_o     )
    );

endmodule
