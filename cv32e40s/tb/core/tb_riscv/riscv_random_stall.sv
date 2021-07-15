// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

//////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//                                                                                                              //
// Author:                      Andreas Traber - atraber@student.ethz.ch                                        //
//                                                                                                              //
// Additional contributions by: Francesco Minervini - minervif@student.ethz.ch                                  //
//                              Davide Schiavone    - pschiavo@iis.ee.ethz.ch                                   //
// Design Name:                 Perturbation Unit                                                               //
// Project Name:                RI5CY, Zeroriscy                                                                //
// Language:                    SystemVerilog                                                                   //
//                                                                                                              //
// Description:                 Introduce stalls on core standard execution for both data and instructions      //
//                                                                                                              //
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////

//import riscv_defines::*;
import perturbation_defines::*;

module riscv_random_stall

 #(
    parameter MAX_STALL_N    = 1,
              RAM_ADDR_WIDTH = 32,
              DATA_WIDTH     = 32
  )

(
    input logic                             clk_i,
    input logic                             rst_ni,
    //grant from memory
    input logic                             grant_mem_i,
    input logic                             rvalid_mem_i,
    input logic [DATA_WIDTH-1:0]            rdata_mem_i,

    output logic                            grant_core_o,
    output logic                            rvalid_core_o,
    output logic [DATA_WIDTH-1:0]           rdata_core_o,

    input logic                             req_core_i,
    output logic                            req_mem_o,

    input logic  [RAM_ADDR_WIDTH-1:0]       addr_core_i,
    output logic [RAM_ADDR_WIDTH-1:0]       addr_mem_o,

    input logic [DATA_WIDTH-1:0]            wdata_core_i,
    output logic [DATA_WIDTH-1:0]           wdata_mem_o,

    input logic                             we_core_i,
    output logic                            we_mem_o,

    input logic [3:0]                       be_core_i,
    output logic [3:0]                      be_mem_o,

    input logic [31:0]                      stall_mode_i,
    input logic [31:0]                      max_stall_i,
    input logic [31:0]                      gnt_stall_i,
    input logic [31:0]                      valid_stall_i
);
`ifndef VERILATOR
logic req_per_q, grant_per_q, rvalid_per_q;

typedef struct {
     logic [31:0]                  addr;
     logic                         we;
     logic [ 3:0]                  be;
     logic [DATA_WIDTH-1:0]        wdata;
     logic [DATA_WIDTH-1:0]        rdata;
   } stall_mem_t;

class rand_gnt_cycles;
     rand int n;
endclass : rand_gnt_cycles

class rand_data_cycles;
     rand int n;
endclass : rand_data_cycles

mailbox #(stall_mem_t) core_reqs          = new (4);
mailbox #(stall_mem_t) core_resps         = new (4);
mailbox #(logic)       core_resps_granted = new (4);
mailbox #(stall_mem_t) memory_transfers   = new (4);

 always_comb begin
   if (req_core_i) begin
     req_per_q <= 1'b1;
   end
   else begin
     req_per_q <= 1'b0;
   end
 end

 always_comb begin
   if (rvalid_mem_i) begin
     rvalid_per_q <= 1'b1;
   end
   else begin
     rvalid_per_q <= 1'b0;
   end
 end


 always_comb begin
   if (grant_mem_i) begin
     grant_per_q <= 1'b1;
   end
   else begin
     grant_per_q <= 1'b0;
   end
  end



 //Grant Process
 initial
 begin : grant_process
     stall_mem_t mem_acc;
     automatic rand_gnt_cycles wait_cycles = new ();

     int temp;

     int stalls, max_val;
     #10;//wait at the very beginning
     while(1) begin
         @(posedge clk_i);
         #1;
         grant_core_o = 1'b0;
         if (!req_per_q) begin
            wait(req_per_q == 1'b1);
         end

         if(stall_mode_i == STANDARD) begin  //FIXED NUMBER OF STALLS MODE
             stalls = gnt_stall_i;
         end else if(stall_mode_i == RANDOM) begin
             max_val = max_stall_i;
             temp = wait_cycles.randomize() with{
                 n >= 0;
                 n<= max_val;
             };
             stalls = wait_cycles.n;

         end else begin
             stalls = 0;
         end


         while(stalls != 0) begin
            @(negedge clk_i);
            stalls--;
         end

         @(negedge clk_i);
         if(req_per_q == 1'b1) begin
             grant_core_o   = 1'b1;
             mem_acc.addr  = addr_core_i;
             mem_acc.be    = be_core_i;
             mem_acc.we    = we_core_i;
             mem_acc.wdata = wdata_core_i;
             core_reqs.put(mem_acc);
             core_resps_granted.put(1'b1);
         end

     end
 end

 initial
 begin : data_process
     stall_mem_t mem_acc;
     automatic rand_data_cycles wait_cycles = new ();
     logic granted;
     int temp, stalls, max_val;

     while(1) begin
         @(posedge clk_i);
         #1;
         rvalid_core_o = 1'b0;
         rdata_core_o  = 'x;

         core_resps_granted.get(granted);

         core_resps.get(mem_acc);

         if(stall_mode_i == STANDARD) begin  //FIXED NUMBER OF STALLS MODE
             stalls = valid_stall_i;
         end else if(stall_mode_i == RANDOM) begin
             max_val = max_stall_i;
             temp = wait_cycles.randomize() with {
                 n>= 0;
                 n<= max_val;
             };
             stalls = wait_cycles.n;

         end else begin

             stalls = 0;
         end


         while(stalls != 0) begin
             @(negedge clk_i);
             stalls--;
         end

         rdata_core_o  = mem_acc.rdata;
         rvalid_core_o = 1'b1;
     end
 end

 initial
 begin : wait_for_grant
     stall_mem_t mem_acc;
     we_mem_o    = 1'b0;
     req_mem_o   = 1'b0;
     addr_mem_o  = '0;
     be_mem_o    = 4'b0;
     wdata_mem_o = 'x;

     while(1) begin
         @(posedge clk_i);
         #1;
         req_mem_o   = 1'b0;
         addr_mem_o  = '0;
         wdata_mem_o = 'x;
         core_reqs.get(mem_acc);
         req_mem_o   = 1'b1;
         addr_mem_o  = mem_acc.addr;
         we_mem_o    = mem_acc.we;
         be_mem_o    = mem_acc.be;
         wdata_mem_o = mem_acc.wdata;

         wait(grant_per_q);
         memory_transfers.put(mem_acc);

     end
 end

 initial
 begin : wait_for_valid
     stall_mem_t mem_acc;
     while(1) begin
         memory_transfers.get(mem_acc);

         wait(rvalid_per_q == 1'b1);
         @(negedge clk_i);
         mem_acc.rdata = rdata_mem_i;

         core_resps.put(mem_acc);

     end
 end
 `endif
 endmodule
