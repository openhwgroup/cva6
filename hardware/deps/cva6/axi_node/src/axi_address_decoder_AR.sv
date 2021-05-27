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
// Module Name:    axi_address_decoder_AR                                        //
// Project Name:   PULP                                                          //
// Language:       SystemVerilog                                                 //
//                                                                               //
// Description:   Address decoder for the address read channel                   //
//                                                                               //
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

module axi_address_decoder_AR
#(
    parameter  ADDR_WIDTH     = 32,
    parameter  N_INIT_PORT    = 8,
    parameter  N_REGION       = 4
)
(
    input  logic                                                        clk,
    input  logic                                                        rst_n,

    input  logic                                                        arvalid_i,
    input  logic [ADDR_WIDTH-1:0]                                       araddr_i,
    output logic                                                        arready_o,

    output logic [N_INIT_PORT-1:0]                                      arvalid_o,
    input  logic [N_INIT_PORT-1:0]                                      arready_i,

    input  logic [N_REGION-1:0][N_INIT_PORT-1:0][ADDR_WIDTH-1:0]        START_ADDR_i,
    input  logic [N_REGION-1:0][N_INIT_PORT-1:0][ADDR_WIDTH-1:0]        END_ADDR_i,
    input  logic [N_REGION-1:0][N_INIT_PORT-1:0]                        enable_region_i,

    input  logic [N_INIT_PORT-1:0]                                      connectivity_map_i,

    output logic                                                        incr_req_o,
    input  logic                                                        full_counter_i,
    input  logic                                                        outstanding_trans_i,

    output logic                                                        error_req_o,
    input  logic                                                        error_gnt_i,
    output logic                                                        sample_ardata_info_o
);

  logic [N_INIT_PORT-1:0]                               match_region;
  logic [N_INIT_PORT:0]                                 match_region_masked;
  logic [N_REGION-1:0][N_INIT_PORT-1:0]                 match_region_int;
  logic [N_INIT_PORT-1:0][N_REGION-1:0]                 match_region_rev;


  logic                                                 arready_int;
  logic [N_INIT_PORT-1:0]                               arvalid_int;

  genvar i,j;

  enum logic    {OPERATIVE, ERROR} CS, NS;


  generate

      // First calculate for each region where what slave ist matching
      for(j=0;j<N_REGION;j++)
      begin
           for(i=0;i<N_INIT_PORT;i++)
           begin
              assign match_region_int[j][i]  =  (enable_region_i[j][i] == 1'b1 ) ? (araddr_i >= START_ADDR_i[j][i]) && (araddr_i <= END_ADDR_i[j][i]) : 1'b0;
           end
      end

      // transpose the match_region_int bidimensional array
      for(j=0;j<N_INIT_PORT;j++)
      begin
           for(i=0;i<N_REGION;i++)
           begin
             assign match_region_rev[j][i] = match_region_int[i][j];
           end
      end


      //Or reduction
      for(i=0;i<N_INIT_PORT;i++)
      begin
        assign match_region[i]  =  | match_region_rev[i];
      end

      assign match_region_masked[N_INIT_PORT-1:0] = match_region & connectivity_map_i;

      // if there are no moatches, then assert an error
      assign match_region_masked[N_INIT_PORT] = ~(|match_region_masked[N_INIT_PORT-1:0]);
  endgenerate







 always_comb
 begin

    if(arvalid_i)
    begin
        {error_req_o,arvalid_int} = {N_INIT_PORT+1{arvalid_i} } & match_region_masked;
    end
    else
    begin
        arvalid_int = '0;
        error_req_o = 1'b0;
    end

    arready_int = |({error_gnt_i,arready_i} & match_region_masked);

 end



  // --------------------------------------------------------------------------------------------------------------------------------------------------//
  // ERROR MANAGMENT BLOCK - STALL in case of ERROR, WAIT untill there are no more pending tranaction then deliver the error req to the BR ALLOCATOR.
  // --------------------------------------------------------------------------------------------------------------------------------------------------//
  always_ff @(posedge clk, negedge rst_n)
  begin
    if(rst_n == 1'b0)
    begin
        CS <= OPERATIVE;
    end
    else
    begin
        CS <= NS;
    end
  end



  always_comb
  begin
      arready_o = 1'b0;
      arvalid_o = arvalid_int;

      sample_ardata_info_o = 1'b0;

      incr_req_o = 1'b0;

      case(CS)
          OPERATIVE:
          begin
              if(error_req_o)
              begin
                NS = ERROR;
                arready_o = 1'b1; // granbt then stall any incoming resposnses
                sample_ardata_info_o = 1'b1;
                arvalid_o = '0;
              end
              else
              begin
                NS = OPERATIVE;
                arready_o = arready_int;
                sample_ardata_info_o = 1'b0;
                incr_req_o = |(arvalid_o & arready_i);
                arvalid_o = arvalid_int;
              end
          end

          ERROR:
          begin
              arready_o = 1'b0;
              arvalid_o = '0;

              if(outstanding_trans_i)
              begin
                NS = ERROR;
              end
              else
              begin
                if(error_gnt_i)
                begin
                  NS        = OPERATIVE;
                end
                else
                begin
                  NS        = ERROR;
                end

              end
          end

          default :
          begin
              NS        = OPERATIVE;
              arready_o = arready_int;
          end
      endcase
  end

  // --------------------------------------------------------------------------------------------------------------------------------------------------//
  //                                                                                                                                                   //
  // --------------------------------------------------------------------------------------------------------------------------------------------------//

endmodule
