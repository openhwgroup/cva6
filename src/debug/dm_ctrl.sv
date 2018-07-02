/* Copyright 2018 ETH Zurich and University of Bologna.
 * Copyright and related rights are licensed under the Solderpad Hardware
 * License, Version 0.51 (the “License”); you may not use this file except in
 * compliance with the License.  You may obtain a copy of the License at
 * http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
 * or agreed to in writing, software, hardware and materials distributed under
 * this License is distributed on an “AS IS” BASIS, WITHOUT WARRANTIES OR
 * CONDITIONS OF ANY KIND, either express or implied. See the License for the
 * specific language governing permissions and limitations under the License.
 *
 * File:   axi_riscv_debug_module.sv
 * Author: Florian Zaruba <zarubaf@iis.ee.ethz.ch>
 * Date:   1.7.2018
 *
 * Description: Debug-module per HART ctrl
 *
 */

module dm_ctrl #(
    parameter dm::hartinfo_t HartInfo = '0
)(
    input  logic          clk_i,    // Clock
    input  logic          rst_ni,   // Asynchronous reset active low
    // to/from CSRs
    input  logic          halt_req_i,
    output logic          halted_o,
    output logic          running_o,
    output logic          unavailable_o,
    output dm::hartinfo_t hartinfo_o,
    input  dm::command_t  command_i,
    output dm::cmderr_t   cmderror_o,
    output logic          cmdbusy_o
);

    assign hartinfo_o = HartInfo;

    typedef enum logic [1:0] {
        kRunning
    } state_t;
    state_t state_d, state_q;

    always_comb begin
        state_d = state_q;

    end

    // sequential process
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (~rst_ni) begin
            state_q <= kIdle;
        end else begin
            state_q <= state_d;
        end
    end
endmodule
