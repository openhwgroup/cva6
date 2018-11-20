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
//-------------------------------------------------------------------------------
//-- Title      : Interrupt Gateway
//-- File       : plic_gateway.sv
//-- Author     : Gian Marti      <gimarti.student.ethz.ch>
//-- Author     : Thomas Kramer   <tkramer.student.ethz.ch>
//-- Author     : Thomas E. Benz  <tbenz.student.ethz.ch>
//-- Company    : Integrated Systems Laboratory, ETH Zurich
//-- Created    : 2018-03-31
//-- Last update: 2018-03-31
//-- Platform   : ModelSim (simulation), Synopsys (synthesis)
//-- Standard   : SystemVerilog IEEE 1800-2012
//-------------------------------------------------------------------------------
//-- Description: Implementation of the Irq Gateway
//-------------------------------------------------------------------------------
//-- Revisions  :
//-- Date        Version  Author  Description
//-- 2018-03-31  2.0      tbenz   Created header
//-------------------------------------------------------------------------------

// the gateway does enable or disable itself depending on the signals claim_i, completed_i
// the gateway knows neither its gateway_id nor its priority
module plic_gateway (
    input  logic       clk_i,
    input  logic       rst_ni,
    input  logic       irq_source_i,
    input  logic       claim_i,
    input  logic       completed_i,
    output logic       irq_pending_o
);
    logic irq_pending_q;        // is 1 when an interrupt appears until the interrupt is claimed
    logic wait_completion_q;    // is 1 when an interrupt appears until the interrupt is completed
                                // also determines if the gateway is disabled, i.e. if interrupts are masked
    logic irq_trigger;

    assign irq_trigger = (~wait_completion_q | completed_i) & irq_source_i;

    always_ff @(posedge clk_i or negedge rst_ni) begin : proc_update_ff
        if (~rst_ni) begin
            irq_pending_q     <= 1'b0;
            wait_completion_q <= 1'b0;
        end else begin
            //pragma translate_off
            `ifndef VERILATOR
            assert (~(claim_i & (~wait_completion_q & irq_source_i)));
            assert (~(completed_i & (~wait_completion_q & irq_source_i)));
            `endif
            //pragma translate_on

            //interrupts not masked and interrupt received -> output to 1
            if (irq_trigger) begin
                irq_pending_q <= 1;
            //interrupt claimed -> output to 0
            end else if (claim_i) begin
                irq_pending_q <= 0;
            end

            //interrupts not masked and interrupt received -> interrupts masked from know on
            if (irq_trigger) begin
                wait_completion_q <= 1;
            //interrupt completed -> demask interrupts
            end else if (completed_i) begin
                wait_completion_q <= 0;
            end
        end
    end

    // Make sure there is 0 cycles delay from claim_i to irq_pending_o.
    assign irq_pending_o = (irq_pending_q | irq_trigger) & ~claim_i;

endmodule
