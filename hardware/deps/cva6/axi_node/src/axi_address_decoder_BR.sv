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
// Module Name:    axi_address_decoder_BR                                        //
// Project Name:   PULP                                                          //
// Language:       SystemVerilog                                                 //
//                                                                               //
// Description:   Address decoder for the READ channel: Decoding                 //
//                is performed on the ID R. This block calculates the            //
//                destination slave port to backroute the read response          //
//                and read data                                                  //
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

module axi_address_decoder_BR
#(
   parameter int unsigned N_TARG_PORT     = 8,
   parameter int unsigned AXI_ID_IN       = 16,
   parameter int unsigned AXI_ID_OUT      = AXI_ID_IN+$clog2(N_TARG_PORT)
)
(
   //AXI BACKWARD write response bus -----------------------------------------------------//
   input  logic [AXI_ID_OUT-1:0]          rid_i,
   input  logic                           rvalid_i,
   output logic                           rready_o,
   // To BW ALLOC --> FROM BW DECODER
   output logic [N_TARG_PORT-1:0]         rvalid_o,
   input  logic [N_TARG_PORT-1:0]         rready_i
);

   logic [N_TARG_PORT-1:0]                req_mask;
   logic [$clog2(N_TARG_PORT)-1:0]        ROUTING;


   assign ROUTING = rid_i[AXI_ID_IN + $clog2(N_TARG_PORT) - 1:AXI_ID_IN];

   always_comb begin
      req_mask = '0;
      req_mask[ROUTING] = 1'b1;
   end

   always_comb begin
      if (rvalid_i) begin
         rvalid_o = {N_TARG_PORT{rvalid_i}} & req_mask;
      end else begin
         rvalid_o = '0;
      end

      rready_o = |(rready_i & req_mask);
   end

 endmodule
