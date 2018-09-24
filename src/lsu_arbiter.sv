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
// Author: Florian Zaruba    <zarubaf@iis.ee.ethz.ch>, ETH Zurich
//         Michael Schaffner <schaffner@iis.ee.ethz.ch>, ETH Zurich
// Date: 15.08.2018
// Description: Arbitrates the LSU result port

import ariane_pkg::*;

module lsu_arbiter (
    input  logic                     clk_i,    // Clock
    input  logic                     rst_ni,   // Asynchronous reset active low
    input  logic                     flush_i,
    // Load Port
    input logic                      ld_valid_i,
    input logic [TRANS_ID_BITS-1:0]  ld_trans_id_i,
    input logic [63:0]               ld_result_i,
    input exception_t                ld_ex_i,
    // Store Port
    input logic                      st_valid_i,
    input logic [TRANS_ID_BITS-1:0]  st_trans_id_i,
    input logic [63:0]               st_result_i,
    input exception_t                st_ex_i,
    // Output Port
    output logic                     valid_o,
    output logic [TRANS_ID_BITS-1:0] trans_id_o,
    output logic [63:0]              result_o,
    output exception_t               ex_o
);

    // the two fifos are used to buffer results from ld and st paths, and arbits between these results in
    // RR fashion. FIFOs need to be 3 deep in order to unconditionally accept loads and stores since we can
    // have a maximum of 2 outstanding loads (valid elements are unconditionally posted to the output and hence
    // we do not need 4 entries).
    localparam DEPTH = 3;

    typedef struct packed {
        logic                     valid;
        logic [TRANS_ID_BITS-1:0] trans_id;
        logic [63:0]              result;
        exception_t               ex;
    } fifo_t;

    fifo_t regs_d[DEPTH:0], regs_q[DEPTH:0];
    logic [$clog2(DEPTH):0]  cnt_d, cnt_q, cnt_inc;

    assign w_one   = ld_valid_i ^ st_valid_i;
    assign w_two   = ld_valid_i & st_valid_i;

    assign cnt_inc = cnt_q+1;
    assign cnt_d   = (w_two)    ? cnt_inc :
                     (w_one)    ? cnt_q   :
                     (cnt_q>0)  ? cnt_q-1 :
                                  cnt_q;

    assign regs_d[DEPTH] = '0;                                                        
    generate
        for(genvar k=0; k<DEPTH; k++) begin
           assign regs_d[k] =  (ld_valid_i & (k==cnt_q))   ?  {1'b1, ld_trans_id_i, ld_result_i, ld_ex_i} : 
                               (w_one      & (k==cnt_q))   ?  {1'b1, st_trans_id_i, st_result_i, st_ex_i} : 
                               (w_two      & (k==cnt_inc)) ?  {1'b1, st_trans_id_i, st_result_i, st_ex_i} : 
                                                              regs_q[k+1];
        end
    endgenerate

    // unconditionally output valid data
    assign valid_o    =  regs_q[0].valid;
    assign trans_id_o =  regs_q[0].trans_id;
    assign result_o   =  regs_q[0].result;
    assign ex_o       =  regs_q[0].ex;  

    always_ff @(posedge clk_i or negedge rst_ni) begin : p_regs
        if(~rst_ni) begin
            regs_q <= '{default:'0};
            cnt_q  <= '0;
        end else begin
            regs_q <= regs_d;
            cnt_q  <= cnt_d;
        end
    end


///////////////////////////////////////////////////////
// assertions
///////////////////////////////////////////////////////

    //pragma translate_off
    `ifndef VERILATOR
        cnt: assert property (
          @(posedge clk_i) disable iff (~rst_ni) cnt_q<DEPTH)      
             else $fatal(1,"cnt_q must be lower than DEPTH");

    `endif
    //pragma translate_on

endmodule
