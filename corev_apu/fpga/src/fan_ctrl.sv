// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Description: PWM Fan Control for Genesys II board
// Author: Florian Zaruba, zarubaf@iis.ee.ethz.ch

module fan_ctrl (
    input  logic       clk_i,
    input  logic       rst_ni,
    input  logic [3:0] pwm_setting_i,
    output logic       fan_pwm_o
);
    logic [3:0]  ms_clock_d, ms_clock_q;
    logic [19:0] cycle_counter_d, cycle_counter_q;

    // clock divider
    always_comb begin
        cycle_counter_d = cycle_counter_q;
        ms_clock_d = ms_clock_q;

        // divide clock by 499999
        if (cycle_counter_q == 499_999) begin
            cycle_counter_d = 0;
            ms_clock_d = ms_clock_q + 1;
        end else begin
            cycle_counter_d = cycle_counter_q + 1;
        end

        if (ms_clock_q == 15) begin
            ms_clock_d = 0;
        end
    end

    // duty cycle
    always_comb begin
        if (ms_clock_q < pwm_setting_i) begin
            fan_pwm_o = 1'b1;
        end else begin
            fan_pwm_o = 1'b0;
        end
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (~rst_ni) begin
            ms_clock_q      <= '0;
            cycle_counter_q <= '0;
        end else begin
            ms_clock_q      <= ms_clock_d;
            cycle_counter_q <= cycle_counter_d;
        end
    end
endmodule
