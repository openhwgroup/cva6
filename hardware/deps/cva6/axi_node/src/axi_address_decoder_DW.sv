// Copyright 2014-2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// ============================================================================= //
// Company:        Multitherman Laboratory @ DEIS - University of Bologna        //
//                    Viale Risorgimento 2 40136                                 //
//                    Bologna - fax 0512093785 -                                 //
//                                                                               //
// Engineer:       Igor Loi - igor.loi@unibo.it                                  //
//                                                                               //
//                                                                               //
// Additional contributions by:                                                  //
//                                                                               //
//                                                                               //
//                                                                               //
// Create Date:    01/02/2014                                                    //
// Design Name:    AXI 4 INTERCONNECT                                            //
// Module Name:    axi_address_decoder_DW                                        //
// Project Name:   PULP                                                          //
// Language:       SystemVerilog                                                 //
//                                                                               //
// Description:   Address decoder for the  write channel: Decoding information   //
//                is passed from the axi_address_decoder_AW. Once it recevices   //
//                a routing infotmation, it sets the multiplexer to the rigth    //
//                master ports. Information are pushed in a fifo and served      //
//                in order. Fifo are pushed when wlast comes                     //
//                                                                               //
// Revision:                                                                     //
// Revision v0.1 - 01/02/2014 : File Created                                     //
//                                                                               //
//                                                                               //
//                                                                               //
//                                                                               //
//                                                                               //
//                                                                               //
// ============================================================================= //

module axi_address_decoder_DW
#(
    parameter  N_INIT_PORT    = 4,
    parameter  FIFO_DEPTH     = 8
)
(
    input  logic                       clk,
    input  logic                       rst_n,
    input  logic                       test_en_i,

    input  logic                       wvalid_i,
    input  logic                       wlast_i,
    output logic                       wready_o,

    output logic [N_INIT_PORT-1:0]     wvalid_o,
    input  logic [N_INIT_PORT-1:0]     wready_i,

    output logic                       grant_FIFO_DEST_o,
    input  logic [N_INIT_PORT-1:0]     DEST_i,
    input  logic                       push_DEST_i,

    input  logic                       handle_error_i,
    output logic                       wdata_error_completed_o
);


  logic                                valid_DEST;
  logic                                pop_from_DEST_FIFO;
  logic [N_INIT_PORT-1:0]              DEST_int;


  logic empty, full;
  fifo_v2 #(
      .FALL_THROUGH(1'b0),
      .DATA_WIDTH(N_INIT_PORT),
      .DEPTH(FIFO_DEPTH)
  ) MASTER_ID_FIFO (
      .clk_i        (clk              ),
      .rst_ni       (rst_n            ),
      .testmode_i   (test_en_i        ),
      .flush_i      (1'b0             ),
      .alm_empty_o  ( ), // open
      .alm_full_o   ( ), // open
      .data_i       (DEST_i             ),
      .push_i       (push_DEST_i        ),
      .full_o       (full               ),
      .data_o       (DEST_int           ),
      .empty_o      (empty              ),
      .pop_i        (pop_from_DEST_FIFO )
  );

  assign grant_FIFO_DEST_o = ~full;
  assign valid_DEST = ~empty;

  assign pop_from_DEST_FIFO = wlast_i & wvalid_i & wready_o & valid_DEST;

  always_comb
  begin

      if(handle_error_i)
      begin
          wready_o = 1'b1;
          wvalid_o = '0;

          wdata_error_completed_o = wlast_i & wvalid_i;
      end
      else
      begin
          wready_o = |(wready_i & DEST_int);
          wdata_error_completed_o           = 1'b0;

          if(wvalid_i & valid_DEST)
          begin
              wvalid_o  = {N_INIT_PORT{wvalid_i}} & DEST_int;
          end
          else
          begin
              wvalid_o  = '0;
          end
      end

  end

endmodule
