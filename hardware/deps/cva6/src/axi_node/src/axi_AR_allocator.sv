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
// Module Name:    axi_AR_allocator                                              //
// Project Name:   PULP                                                          //
// Language:       SystemVerilog                                                 //
//                                                                               //
// Description:   Address Read Allocator: it performs a round robin arbitration  //
//                between pending read requests from each slave port.            //
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

module axi_AR_allocator
#(
      parameter AXI_ADDRESS_W  = 32,
      parameter AXI_USER_W     = 6,
      parameter N_TARG_PORT    = 7,
      parameter LOG_N_TARG     = $clog2(N_TARG_PORT),
      parameter AXI_ID_IN      = 16,
      parameter AXI_ID_OUT     = AXI_ID_IN + $clog2(N_TARG_PORT)
)
(
      input  logic                                          clk,
      input  logic                                          rst_n,

      //AXI Read address bus ----------------------------------------------------------------
      input  logic [N_TARG_PORT-1:0][AXI_ID_IN-1:0]         arid_i,
      input  logic [N_TARG_PORT-1:0][AXI_ADDRESS_W-1:0]     araddr_i,
      input  logic [N_TARG_PORT-1:0][ 7:0]                  arlen_i,   //burst length - 1 to 16
      input  logic [N_TARG_PORT-1:0][ 2:0]                  arsize_i,  //size of each transfer in burst
      input  logic [N_TARG_PORT-1:0][ 1:0]                  arburst_i, //for bursts>1, accept only incr burst=01
      input  logic [N_TARG_PORT-1:0]                        arlock_i,  //only normal access supported axs_arlock=00
      input  logic [N_TARG_PORT-1:0][ 3:0]                  arcache_i,
      input  logic [N_TARG_PORT-1:0][ 2:0]                  arprot_i,
      input  logic [N_TARG_PORT-1:0][ 3:0]                  arregion_i,     //
      input  logic [N_TARG_PORT-1:0][ AXI_USER_W-1:0]       aruser_i,       //
      input  logic [N_TARG_PORT-1:0][ 3:0]                  arqos_i,        //
      input  logic [N_TARG_PORT-1:0]                        arvalid_i, //master addr valid
      output logic [N_TARG_PORT-1:0]                        arready_o, //slave ready to accept


      //AXI Read address bus--> OUT----------------------------------------------------------------
      output  logic [AXI_ID_OUT-1:0]                        arid_o,
      output  logic [AXI_ADDRESS_W-1:0]                     araddr_o,
      output  logic [ 7:0]                                  arlen_o,   //burst length - 1 to 16
      output  logic [ 2:0]                                  arsize_o,  //size of each transfer in burst
      output  logic [ 1:0]                                  arburst_o, //for bursts>1, accept only incr burst=01
      output  logic                                         arlock_o,  //only normal access supported axs_arlock=00
      output  logic [ 3:0]                                  arcache_o,
      output  logic [ 2:0]                                  arprot_o,
      output  logic [ 3:0]                                  arregion_o,     //
      output  logic [ AXI_USER_W-1:0]                       aruser_o,       //
      output  logic [ 3:0]                                  arqos_o,        //
      output  logic                                         arvalid_o, //master addr valid
      input   logic                                         arready_i //slave ready to accept
);

localparam      AUX_WIDTH = AXI_ID_IN + AXI_ADDRESS_W + 8 + 3 + 2 + 1 + 4 + 3 +    4 + AXI_USER_W + 4;


logic [N_TARG_PORT-1:0][AUX_WIDTH-1:0]                          AUX_VECTOR_IN;
logic [AUX_WIDTH-1:0]                                           AUX_VECTOR_OUT;

logic [N_TARG_PORT-1:0][LOG_N_TARG+N_TARG_PORT-1:0]             ID_in;
logic [LOG_N_TARG+N_TARG_PORT-1:0]                              ID_int;


genvar i;


assign        { arqos_o, aruser_o, arregion_o, arprot_o, arcache_o, arlock_o, arburst_o, arsize_o, arlen_o, araddr_o, arid_o[AXI_ID_IN-1:0] }  =  AUX_VECTOR_OUT;
assign        arid_o[AXI_ID_OUT-1:AXI_ID_IN] = ID_int[LOG_N_TARG+N_TARG_PORT-1:N_TARG_PORT];




generate
  for(i=0;i<N_TARG_PORT;i++)
  begin : AUX_VECTOR_BINDING
      assign AUX_VECTOR_IN[i] =  { arqos_i[i], aruser_i[i], arregion_i[i], arprot_i[i], arcache_i[i], arlock_i[i], arburst_i[i], arsize_i[i], arlen_i[i], araddr_i[i], arid_i[i]};
  end

  for(i=0;i<N_TARG_PORT;i++)
  begin : ID_VECTOR_BINDING
      assign ID_in[i][N_TARG_PORT-1:0] =  2**i;                   // OH ENCODING
      assign ID_in[i][LOG_N_TARG+N_TARG_PORT-1:N_TARG_PORT] =  i; //BIN ENCODING
  end

endgenerate

  axi_node_arbiter #(
    .AUX_WIDTH  (AUX_WIDTH),
    .ID_WIDTH   (LOG_N_TARG+N_TARG_PORT),
    .N_MASTER   (N_TARG_PORT)
  ) i_arbiter (
    .clk_i        (clk),
    .rst_ni       (rst_n),

    .inp_id_i     (ID_in),
    .inp_aux_i    (AUX_VECTOR_IN),
    .inp_valid_i  (arvalid_i),
    .inp_ready_o  (arready_o),

    .oup_id_o     (ID_int),
    .oup_aux_o    (AUX_VECTOR_OUT),
    .oup_valid_o  (arvalid_o),
    .oup_ready_i  (arready_i)
  );

endmodule
