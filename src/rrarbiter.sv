// Copyright (c) 2018 ETH Zurich, University of Bologna
// All rights reserved.
//
// This code is under development and not yet released to the public.
// Until it is released, the code is under the copyright of ETH Zurich and
// the University of Bologna, and may contain confidential and/or unpublished
// work. Any reuse/redistribution is strictly forbidden without written
// permission from ETH Zurich.
//
// Bug fixes and contributions will eventually be released under the
// SolderPad open hardware license in the context of the PULP platform
// (http://www.pulp-platform.org), under the copyright of ETH Zurich and the
// University of Bologna.
//
// Author: Michael Schaffner <schaffner@iis.ee.ethz.ch>, ETH Zurich
// Date: 16.08.2018
// Description: Round robin arbiter with lookahead
//  
// this unit is a generic round robin arbiter with "look ahead" - i.e. it jumps 
// to the next valid request signal instead of stepping around with stepsize 1. 
// if the current req signal has been acknowledged in the last cycle, and it is 
// again valid in the current cycle, the arbiter will first serve the other req 
// signals (if there is a valid one) in the req vector before acknowledging the 
// same signal again (this prevents starvation).
//
// the arbiter has a request signal vector input (req_i) and an ack 
// signal vector ouput (ack_o). to enable the arbiter the signal 
// en_i has to be asserted. vld_o is high when one of the 
// req_i signals is acknowledged.
//
// the entity has one register which stores the index of the last request signal 
// that was served.
// 
// dependencies: relies on fast leading zero counter tree "ff1" in common_cells
//

module rrarbiter #(
    parameter NUM_REQ = 13
)(
    input logic                         clk_i,
    input logic                         rst_ni,
 
    input logic                         flush_i, // clears the fsm and control signal registers 
    input logic                         en_i,    // arbiter enable
    input logic [NUM_REQ-1:0]           req_i,   // request signals
 
    output logic [NUM_REQ-1:0]          ack_o,   // acknowledge signals
    output logic                        vld_o,   // valid signals
    output logic [$clog2(NUM_REQ)-1:0]  idx_o    // idx output
    );

localparam SEL_WIDTH = $clog2(NUM_REQ);

logic [SEL_WIDTH-1:0] arb_sel_d;
logic [SEL_WIDTH-1:0] arb_sel_q;        


// only used in case of more than 2 requesters
logic [NUM_REQ-1:0] mask_lut[NUM_REQ-1:0];
logic [NUM_REQ-1:0] mask;
logic [NUM_REQ-1:0] masked_lower;
logic [NUM_REQ-1:0] masked_upper;
logic [SEL_WIDTH-1:0] lower_idx;
logic [SEL_WIDTH-1:0] upper_idx;
logic [SEL_WIDTH-1:0] next_idx;
logic [SEL_WIDTH-1:0] idx;
logic no_lower_ones;


// shared
assign idx_o          = arb_sel_d;
assign vld_o          = (|req_i) & en_i;

// only 2 input requesters
generate 
    if (NUM_REQ == 2) begin

        assign ack_o[0]       = ((~arb_sel_q) | ( arb_sel_q & ~req_i[1])) & req_i[0] & en_i;
        assign arb_sel_d      = (( arb_sel_q) | (~arb_sel_q & ~req_i[0])) & req_i[1];
        assign ack_o[1]       = arb_sel_d                                            & en_i;
    
    end    
endgenerate        

// more than 2 requesters
generate 
    if (NUM_REQ > 2) begin

        // this mask is used to mask the incoming req vector 
        // depending on the index of the last served index
        assign mask = mask_lut[arb_sel_q];

        // get index from masked vectors
        ff1 #(
            .LEN(NUM_REQ)
        ) i_lower_ff1 (
            .in_i        ( masked_lower  ),
            .first_one_o ( lower_idx     ),
            .no_ones_o   ( no_lower_ones )
        );    

        ff1 #(
            .LEN(NUM_REQ)
        ) i_upper_ff1 (
            .in_i        ( masked_upper  ),
            .first_one_o ( upper_idx     ),
            .no_ones_o   (               )
        );    

        // wrap around
        assign next_idx   = (no_lower_ones) ? upper_idx : lower_idx;
        assign arb_sel_d  = (next_idx < NUM_REQ) ? next_idx : NUM_REQ-1;
        
    end
endgenerate  

genvar k;
generate
    for (k=0; (k < NUM_REQ) && NUM_REQ > 2; k++) begin
        assign mask_lut[k]     = 2**(k+1)-1;
        assign masked_lower[k] = (~ mask[k]) & req_i[k];
        assign masked_upper[k] = mask[k]     & req_i[k];
        assign ack_o[k]        = ((arb_sel_d == k) & vld_o ) ? 1'b1 : 1'b0;
    end
endgenerate

// regs
always_ff @(posedge clk_i or negedge rst_ni) begin : p_regs
    if(~rst_ni) begin
        arb_sel_q <= 0;
    end else begin
        if (flush_i) begin
            arb_sel_q <= 0;
        end else if (vld_o) begin
            arb_sel_q <= arb_sel_d;
        end
    end
end


`ifndef SYNTHESIS
`ifndef VERILATOR
    // check parameterization, enable and hot1 property of acks
    // todo: check RR fairness with sequence assertion
    initial begin
        assert (NUM_REQ>=2) else $fatal ("minimum input width of req vecor is 2");
    end
    ack_implies_vld: assert property (@(posedge clk_i) disable iff (~rst_ni) |ack_o |-> vld_o)              else $fatal ("an asserted ack signal implies that vld_o must be asserted, too");
    vld_implies_ack: assert property (@(posedge clk_i) disable iff (~rst_ni) vld_o  |-> |ack_o)             else $fatal ("an asserted vld_o signal implies that one ack_o must be asserted, too");
    en_vld_check:    assert property (@(posedge clk_i) disable iff (~rst_ni) !en_i  |-> !vld_o)             else $fatal ("vld must not be asserted when arbiter is disabled");
    en_ack_check:    assert property (@(posedge clk_i) disable iff (~rst_ni) !en_i  |-> !ack_o)             else $fatal ("ack_o must not be asserted when arbiter is disabled");
    ack_idx_check:   assert property (@(posedge clk_i) disable iff (~rst_ni) vld_o |-> ack_o[idx_o])        else $fatal ("index / ack_o do not match");
    hot1_check:      assert property (@(posedge clk_i) disable iff (~rst_ni) ((~(1<<idx_o)) & ack_o) == 0 ) else $fatal ("only one ack_o can be asserted at a time (i.e. ack_o must be hot1)");
`endif
`endif


endmodule // rrarbiter



