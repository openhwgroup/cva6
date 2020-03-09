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
// Module Name:    clock_divider_counter                                      //
// Project Name:   ULPSoC                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    clock_divider_counter                                      //
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


module clock_divider_counter
#(
    parameter BYPASS_INIT = 1,
    parameter DIV_INIT    = 'hFF
)
(
    input  logic       clk,
    input  logic       rstn,
    input  logic       test_mode,
    input  logic [7:0] clk_div,
    input  logic       clk_div_valid,
    output logic       clk_out
);

    logic [7:0]         counter;
    logic [7:0]         counter_next;
    logic [7:0]         clk_cnt;
    logic               en1;
    logic               en2;

    logic               is_odd;

    logic               div1;
    logic               div2;
    logic               div2_neg_sync;

    logic [7:0]         clk_cnt_odd;
    logic [7:0]         clk_cnt_odd_incr;
    logic [7:0]         clk_cnt_even;
    logic [7:0]         clk_cnt_en2;

    logic               bypass;

    logic               clk_out_gen;
    logic               clk_div_valid_reg;

    logic               clk_inv_test;
    logic               clk_inv;

    //        assign clk_cnt_odd_incr = clk_div + 1;
    //        assign clk_cnt_odd  = {1'b0,clk_cnt_odd_incr[7:1]}; //if odd divider than clk_cnt = (clk_div+1)/2
    assign clk_cnt_odd  = clk_div - 8'h1; //if odd divider than clk_cnt = clk_div - 1
    assign clk_cnt_even = (clk_div == 8'h2) ? 8'h0 : ({1'b0,clk_div[7:1]} - 8'h1);   //if even divider than clk_cnt = clk_div/2
    assign clk_cnt_en2  = {1'b0,clk_cnt[7:1]} + 8'h1;

    always_comb
    begin
        if (counter == 'h0)
            en1 = 1'b1;
        else
            en1 = 1'b0;

        if (clk_div_valid)
            counter_next = 'h0;
        else if (counter == clk_cnt)
                counter_next = 'h0;
             else
                counter_next = counter + 1;

        if (clk_div_valid)
            en2 = 1'b0;
        else if (counter == clk_cnt_en2)
                en2 = 1'b1;
             else
                en2 = 1'b0;
    end

   always_ff @(posedge clk, negedge rstn)
   begin
        if (~rstn)
        begin
             counter            <=  'h0;
             div1               <= 1'b0;
             bypass             <= BYPASS_INIT;
             clk_cnt            <= DIV_INIT;
             is_odd             <= 1'b0;
             clk_div_valid_reg  <= 1'b0;
        end
        else
        begin
              if (!bypass)
                  counter <= counter_next;

              clk_div_valid_reg <= clk_div_valid;
              if (clk_div_valid)
              begin
                if ((clk_div == 8'h0) || (clk_div == 8'h1))
                  begin
                      bypass <= 1'b1;
                      clk_cnt <= 'h0;
                      is_odd  <= 1'b0;
                  end
                else
                  begin
                      bypass <= 1'b0;
                      if (clk_div[0])
                        begin
                          is_odd  <= 1'b1;
                          clk_cnt <= clk_cnt_odd;
                        end
                      else
                        begin
                          is_odd  <= 1'b0;
                          clk_cnt <= clk_cnt_even;
                        end
                  end
                div1 <= 1'b0;
              end
              else
              begin
                if (en1 && !bypass)
                  div1 <= ~div1;
              end
        end
    end

    pulp_clock_inverter clk_inv_i
    (
        .clk_i(clk),
        .clk_o(clk_inv)
    );

`ifndef PULP_FPGA_EMUL
 `ifdef PULP_DFT
   pulp_clock_mux2 clk_muxinv_i
     (
      .clk0_i(clk_inv),
      .clk1_i(clk),
      .clk_sel_i(test_mode),
      .clk_o(clk_inv_test)
      );
 `else
   assign clk_inv_test = clk_inv;
 `endif
`else
   assign clk_inv_test = clk_inv;
`endif

    always_ff @(posedge clk_inv_test or negedge rstn)
    begin
        if (!rstn)
        begin
            div2    <= 1'b0;
        end
        else
        begin
            if (clk_div_valid_reg)
                div2 <= 1'b0;
            else if (en2 && is_odd && !bypass)
                    div2 <= ~div2;
        end
    end // always_ff @ (posedge clk_inv_test or negedge rstn)

    pulp_clock_xor2 clock_xor_i
    (
        .clk_o(clk_out_gen),
        .clk0_i(div1),
        .clk1_i(div2)
    );

    pulp_clock_mux2 clk_mux_i
    (
        .clk0_i(clk_out_gen),
        .clk1_i(clk),
        .clk_sel_i(bypass || test_mode),
        .clk_o(clk_out)
    );

endmodule
