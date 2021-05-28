// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

////////////////////////////////////////////////////////////////////////////////
//                                                                            //
// Company:        Multitherman Laboratory @ DEIS - University of Bologna     //
//                    Viale Risorgimento 2 40136                              //
//                    Bologna - fax 0512093785 -                              //
//                                                                            //
// Engineer:       Antonio Pullini - pullinia@iis.ee.ethz.ch                  //
//                                                                            //
// Additional contributions by:                                               //
//                                                                            //
//                                                                            //
//                                                                            //
// Create Date:    13/02/2013                                                 //
// Design Name:    ULPSoC                                                     //
// Module Name:    clock_divider                                              //
// Project Name:   ULPSoC                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Clock Divider                                              //
//                                                                            //
//                                                                            //
// Revision:                                                                  //
// Revision v0.1 - File Created                                               //
// Revision v0.2 - (19/03/2015)   clock_gating swapped in pulp_clock_gating   //
//                                                                            //
//                                                                            //
//                                                                            //
//                                                                            //
//                                                                            //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module clock_divider
#(
    parameter DIV_INIT     = 0,
    parameter BYPASS_INIT  = 1
)
(
    input  logic       clk_i,
    input  logic       rstn_i,
    input  logic       test_mode_i,
    input  logic       clk_gate_async_i,
    input  logic [7:0] clk_div_data_i,
    input  logic       clk_div_valid_i,
    output logic       clk_div_ack_o,
    output logic       clk_o
);

   enum                logic [1:0] {IDLE, STOP, WAIT, RELEASE} state, state_next;

   logic               s_clk_out;
   logic               s_clock_enable;
   logic               s_clock_enable_gate;
   logic               s_clk_div_valid;

   logic [7:0]         reg_clk_div;
   logic               s_clk_div_valid_sync;

   logic               s_rstn_sync;

   logic [1:0]         reg_ext_gate_sync;

    assign s_clock_enable_gate =  s_clock_enable & reg_ext_gate_sync;

`ifndef PULP_FPGA_EMUL
    rstgen i_rst_gen
    (
        // PAD FRAME SIGNALS
        .clk_i(clk_i),
        .rst_ni(rstn_i),            //async signal coming from pads

        // TEST MODE
        .test_mode_i(test_mode_i),

        // OUTPUT RESET
        .rst_no(s_rstn_sync),
        .init_no()                 //not used
    );
  `else
  assign s_rstn_sync = rstn_i;
`endif


    //handle the handshake with the soc_ctrl. Interface is now async
    pulp_sync_wedge i_edge_prop
    (
        .clk_i(clk_i),
        .rstn_i(s_rstn_sync),
        .en_i(1'b1),
        .serial_i(clk_div_valid_i),
        .serial_o(clk_div_ack_o),
        .r_edge_o(s_clk_div_valid_sync),
        .f_edge_o()
    );

    clock_divider_counter
    #(
        .BYPASS_INIT(BYPASS_INIT),
        .DIV_INIT(DIV_INIT)
    )
    i_clkdiv_cnt
    (
        .clk(clk_i),
        .rstn(s_rstn_sync),
        .test_mode(test_mode_i),
        .clk_div(reg_clk_div),
        .clk_div_valid(s_clk_div_valid),
        .clk_out(s_clk_out)
    );

    pulp_clock_gating i_clk_gate
    (
        .clk_i(s_clk_out),
        .en_i(s_clock_enable_gate),
        .test_en_i(test_mode_i),
        .clk_o(clk_o)
    );

    always_comb
    begin
        case(state)
        IDLE:
        begin
            s_clock_enable   = 1'b1;
            s_clk_div_valid  = 1'b0;
            if (s_clk_div_valid_sync)
                state_next = STOP;
            else
                state_next = IDLE;
        end

        STOP:
        begin
            s_clock_enable   = 1'b0;
            s_clk_div_valid  = 1'b1;
            state_next = WAIT;
        end

        WAIT:
        begin
            s_clock_enable   = 1'b0;
            s_clk_div_valid  = 1'b0;
            state_next = RELEASE;
        end

        RELEASE:
        begin
            s_clock_enable   = 1'b0;
            s_clk_div_valid  = 1'b0;
            state_next = IDLE;
        end
        endcase
    end

    always_ff @(posedge clk_i or negedge s_rstn_sync)
    begin
        if (!s_rstn_sync)
            state <= IDLE;
        else
            state <= state_next;
    end

    //sample the data when valid has been sync and there is a rise edge
    always_ff @(posedge clk_i or negedge s_rstn_sync)
    begin
        if (!s_rstn_sync)
            reg_clk_div <= '0;
        else if (s_clk_div_valid_sync)
                  reg_clk_div <= clk_div_data_i;
    end

    //sample the data when valid has been sync and there is a rise edge
    always_ff @(posedge clk_i or negedge s_rstn_sync)
    begin
        if (!s_rstn_sync)
            reg_ext_gate_sync <= 2'b00;
        else
            reg_ext_gate_sync <= {clk_gate_async_i, reg_ext_gate_sync[1]};
    end

endmodule
