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
    // RR fashion. FIFOs need to be 2 deep in order to unconditionally accept loads and stores since we can
    // have a maximum of 2 outstanding loads.
    // if there are valid elements in the fifos, the unit posts the result on its output ports and expects it
    // to be consumed unconditionally 

    localparam int DEPTH = 2;

    typedef struct packed {
        logic [TRANS_ID_BITS-1:0] trans_id;
        logic [63:0]              result;
        exception_t               ex;
    } fifo_t;

    fifo_t st_in, st_out, ld_in, ld_out;

    logic ld_full, ld_empty, ld_ren;
    logic st_full, st_empty, st_ren;
    logic rrstate_q, rrstate_d;

    assign st_in.trans_id = st_trans_id_i;
    assign st_in.result   = st_result_i;
    assign st_in.ex       = st_ex_i;

    assign ld_in.trans_id = ld_trans_id_i;
    assign ld_in.result   = ld_result_i;
    assign ld_in.ex       = ld_ex_i;

    assign trans_id_o     = (st_ren) ? st_out.trans_id : ld_out.trans_id; 
    assign result_o       = (st_ren) ? st_out.result   : ld_out.result;   
    assign ex_o           = (st_ren) ? st_out.ex       : ld_out.ex;      

    assign valid_o        = (~ld_empty) | (~st_empty);

    // round robin with "lookahead" for 2 requesters
    assign ld_ren         = ((~rrstate_q) | ( rrstate_q & st_empty)) & ~ld_empty;
    assign st_ren         = (( rrstate_q) | (~rrstate_q & ld_empty)) & ~st_empty;

    assign rrstate_d      = (valid_o) ? ~st_ren : rrstate_q;

    always_ff @(posedge clk_i or negedge rst_ni) begin : p_regs
        if(~rst_ni) begin
            rrstate_q <= 0;
        end else begin
            rrstate_q <= rrstate_d;
        end
    end

    fifo #(
        .dtype             (  fifo_t     ),
        .DEPTH             (  DEPTH      )
    ) ld_fifo (       
        .clk_i             (  clk_i      ),
        .rst_ni            (  rst_ni     ),
        .flush_i           (  flush_i    ),
        .testmode_i        (  1'b0       ),
        .full_o            (  ld_full    ),
        .empty_o           (  ld_empty   ),
        .alm_full_o        (             ),
        .alm_empty_o       (             ),
        .data_i            (  ld_in      ),
        .push_i            (  ld_valid_i ),
        .data_o            (  ld_out     ),
        .pop_i             (  ld_ren     )
    );  

    fifo #(
        .dtype             (  fifo_t     ),
        .DEPTH             (  DEPTH      )
    ) st_fifo (       
        .clk_i             (  clk_i      ),
        .rst_ni            (  rst_ni     ),
        .flush_i           (  flush_i    ),
        .testmode_i        (  1'b0       ),
        .full_o            (  st_full    ),
        .empty_o           (  st_empty   ),
        .alm_full_o        (             ),
        .alm_empty_o       (             ),
        .data_i            (  st_in      ),
        .push_i            (  st_valid_i ),
        .data_o            (  st_out     ),
        .pop_i             (  st_ren     )
    ); 


`ifndef SYNTHESIS
`ifndef VERILATOR
    // check fifo control signals
    assert property (@(posedge clk_i) disable iff (~rst_ni) ld_full |-> !ld_valid_i) else $fatal ("cannot write full ld_fifo");
    assert property (@(posedge clk_i) disable iff (~rst_ni) st_full |-> !st_valid_i) else $fatal ("cannot write full st_fifo");
    assert property (@(posedge clk_i) disable iff (~rst_ni) ld_empty |-> !ld_ren)    else $fatal ("cannot read empty ld_fifo");
    assert property (@(posedge clk_i) disable iff (~rst_ni) st_empty |-> !st_ren)    else $fatal ("cannot read empty st_fifo");
`endif
`endif


endmodule
