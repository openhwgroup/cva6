// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
//                                                                                                          //
// Author:                              Francesco Minervini - minervif@student.ethz.ch                      //
//                                                                                                          //
// Additional contributions by:         Davide Schiavone - pschiavo@iis.ee.ethz.ch                          //
// Design Name:                         Interrupt generator                                                 //
// Project Name:                        RI5CY, Zeroriscy                                                    //
// Language:                            SystemVerilog                                                       //
//                                                                                                          //
// Description:                         Send interrupt request to core choosing one option between:         //
//                                      - Random;                                                           //
//                                      - Standard;                                                         //
//                                      - PC value-triggering                                               //
//                                                                                                          //
//////////////////////////////////////////////////////////////////////////////////////////////////////////////
//import riscv_defines::*;
import perturbation_defines::*;

module riscv_random_interrupt_generator
(
    input logic           rst_ni,
    input logic           clk_i,
    input logic           irq_i,
    input logic   [4:0]   irq_id_i,
    input logic           irq_ack_i,
    output logic          irq_o,
    output logic  [4:0]   irq_id_o,
    output logic          irq_ack_o,
    input logic  [31:0]   irq_mode_i,
    input logic  [31:0]   irq_min_cycles_i,
    input logic  [31:0]   irq_max_cycles_i,
    input logic  [31:0]   irq_min_id_i,
    input logic  [31:0]   irq_max_id_i,
    output logic [31:0]   irq_act_id_o,
    output logic          irq_id_we_o,
    input logic  [31:0]   irq_pc_id_i,
    input logic  [31:0]   irq_pc_trig_i
);

`ifndef VERILATOR
class rand_irq_cycles;
    rand int n;
endclass : rand_irq_cycles

class rand_irq_id;
    rand int n;
endclass : rand_irq_id

logic [31:0] irq_mode_q;
logic        irq_random;
logic  [4:0] irq_id_random;
logic        irq_ack_random;
logic        irq_monitor;
logic  [4:0] irq_id_monitor;
logic        irq_ack_monitor;

assign irq_ack_o = irq_ack_i;

always_ff @(posedge clk_i or negedge rst_ni)
begin
    if(~rst_ni) begin
        irq_mode_q <= 0;
    end else begin
        irq_mode_q <= irq_mode_i;
    end
end

always_comb
begin
    unique case (irq_mode_q)
        RANDOM:
        begin
         irq_o     = irq_random;
         irq_id_o  = irq_id_random;
        end

        PC_TRIG:
        begin
         irq_o     = irq_monitor;
         irq_id_o  = irq_id_monitor;
        end

        default:
        begin
         irq_o     = irq_i;
         irq_id_o  = irq_id_i;
        end
    endcase
end

//Random Process
initial
begin
    automatic rand_irq_cycles wait_cycles = new();
    automatic rand_irq_id value = new();
    int temp,i, min_irq_cycles, max_irq_cycles, min_irq_id, max_irq_id;
    irq_random = 1'b0;
    irq_id_random  = '0;
    while(1) begin

        irq_random    = 1'b0;
        irq_id_random = '0;

        @(posedge clk_i);

        wait(irq_mode_q == RANDOM);
        min_irq_id     = irq_min_id_i;
        max_irq_id     = irq_max_id_i;
        min_irq_cycles = irq_min_cycles_i;
        max_irq_cycles = irq_max_cycles_i;

        temp = value.randomize() with{
            n >= min_irq_id;
            n <= max_irq_id;
        };
        temp = wait_cycles.randomize() with{
            n >= min_irq_cycles;
            n <= max_irq_cycles;
        };
        while(wait_cycles.n != 0) begin
            @(posedge clk_i);
            wait_cycles.n--;
        end

        irq_id_random = value.n;
        irq_random    = 1'b1;
        irq_act_id_o  = value.n;
        @(posedge clk_i);
        //we don't care about the ack in this mode
        for(i=0; i<max_irq_cycles; i++) begin
            @(posedge clk_i);
        end
    end
end


//Monitor Process
initial
begin
    int pc_value;
    irq_monitor    = 1'b0;
    irq_id_monitor = '0;
    pc_value = 0;
    wait(irq_mode_q == PC_TRIG);
    wait(irq_pc_id_i == irq_pc_trig_i);
    irq_monitor    = 1'b1;
    irq_id_monitor = irq_min_id_i;
    while(irq_ack_i != 1'b1) begin
        @(posedge clk_i);   //Keep the request high until the acknowledge is received
    end
    @(posedge clk_i);
    irq_monitor    = 1'b0;
    irq_id_monitor = '0;
end

initial
begin
    while(1) begin
        irq_id_we_o = 1'b0;
        wait(irq_ack_i == 1'b1);
        irq_id_we_o = 1'b1;   //Give the write enable to store the core response
        @(posedge clk_i);
    end
end

`endif
endmodule
