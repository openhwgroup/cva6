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
// Module Name:    axi_request_block                                             //
// Project Name:   PULP                                                          //
// Language:       SystemVerilog                                                 //
//                                                                               //
// Description:   It groups B and R address decoders , and AW and AR and         //
//                W allocators                                                   //
//                                                                               //
// Revision:                                                                     //
// Revision v0.1 - 01/02/2014 : File Created                                     //
//                                                                               //
// ============================================================================= //

module axi_request_block
#(
    parameter                   AXI_ADDRESS_W  = 32,
    parameter                   AXI_DATA_W     = 64,
    parameter                   AXI_NUMBYTES   = AXI_DATA_W/8,
    parameter                   AXI_USER_W     = 6,

    parameter                   N_INIT_PORT    = 5,
    parameter                   N_TARG_PORT    = 8,
    parameter                   FIFO_DW_DEPTH  = 8,

    parameter                   AXI_ID_IN      = 16,

    parameter                   LOG_N_TARG     = $clog2(N_TARG_PORT),
    parameter                   AXI_ID_OUT     = AXI_ID_IN + LOG_N_TARG
)
(
  input logic                                                           clk,
  input logic                                                           rst_n,
  input logic                                                           test_en_i,

  // -----------------------------------------------------------------------------------//
  //                           INTERNAL (N_TARGET PORT )                                //
  // -----------------------------------------------------------------------------------//
  //AXI write address bus --------------------------------------------------------------//
  input  logic [N_TARG_PORT-1:0][AXI_ID_IN-1:0]                         awid_i,         //
  input  logic [N_TARG_PORT-1:0][AXI_ADDRESS_W-1:0]                     awaddr_i,       //
  input  logic [N_TARG_PORT-1:0][ 7:0]                                  awlen_i,        //burst length is 1 + (0 - 15)
  input  logic [N_TARG_PORT-1:0][ 2:0]                                  awsize_i,       //size of each transfer in burst
  input  logic [N_TARG_PORT-1:0][ 1:0]                                  awburst_i,      //for bursts>1, accept only incr burst=01
  input  logic [N_TARG_PORT-1:0]                                        awlock_i,       //only normal access supported axs_awlock=00
  input  logic [N_TARG_PORT-1:0][ 3:0]                                  awcache_i,      //
  input  logic [N_TARG_PORT-1:0][ 2:0]                                  awprot_i,       //
  input  logic [N_TARG_PORT-1:0][ 3:0]                                  awregion_i,     //
  input  logic [N_TARG_PORT-1:0][ 5:0]                                  awatop_i,       //
  input  logic [N_TARG_PORT-1:0][ AXI_USER_W-1:0]                       awuser_i,       //
  input  logic [N_TARG_PORT-1:0][ 3:0]                                  awqos_i,        //
  input  logic [N_TARG_PORT-1:0]                                        awvalid_i,      //master addr valid
  output logic [N_TARG_PORT-1:0]                                        awready_o,      //slave ready to accept
  // -----------------------------------------------------------------------------------//

  //AXI write data bus -----------------------------------------------------------------//
  input  logic [N_TARG_PORT-1:0] [AXI_DATA_W-1:0]                       wdata_i,
  input  logic [N_TARG_PORT-1:0] [AXI_NUMBYTES-1:0]                     wstrb_i,        //1 strobe per byte
  input  logic [N_TARG_PORT-1:0]                                        wlast_i,        //last transfer in burst
  input  logic [N_TARG_PORT-1:0] [AXI_USER_W-1:0]                       wuser_i,
  input  logic [N_TARG_PORT-1:0]                                        wvalid_i,       //master data valid
  output logic [N_TARG_PORT-1:0]                                        wready_o,       //slave ready to accept
  // -----------------------------------------------------------------------------------//


  //AXI read address bus ---------------------------------------------------------------//
  input  logic [N_TARG_PORT-1:0][ AXI_ID_IN-1:0]                        arid_i,
  input  logic [N_TARG_PORT-1:0][ AXI_ADDRESS_W-1:0]                    araddr_i,
  input  logic [N_TARG_PORT-1:0][ 7:0]                                  arlen_i,        //burst length - 1 to 16
  input  logic [N_TARG_PORT-1:0][ 2:0]                                  arsize_i,       //size of each transfer in burst
  input  logic [N_TARG_PORT-1:0][ 1:0]                                  arburst_i,      //for bursts>1, accept only incr burst=01
  input  logic [N_TARG_PORT-1:0]                                        arlock_i,       //only normal access supported axs_awlock=00
  input  logic [N_TARG_PORT-1:0][ 3:0]                                  arcache_i,
  input  logic [N_TARG_PORT-1:0][ 2:0]                                  arprot_i,
  input  logic [N_TARG_PORT-1:0][ 3:0]                                  arregion_i,     //
  input  logic [N_TARG_PORT-1:0][ AXI_USER_W-1:0]                       aruser_i,       //
  input  logic [N_TARG_PORT-1:0][ 3:0]                                  arqos_i,        //
  input  logic [N_TARG_PORT-1:0]                                        arvalid_i,      //master addr valid
  output logic [N_TARG_PORT-1:0]                                        arready_o,      //slave ready to accept
  // -----------------------------------------------------------------------------------//


  // ------------------------------------------------------------------------------------//
  //                           SLAVE SIDE (ONE PORT ONLY)                                //
  // ------------------------------------------------------------------------------------//
  //AXI BACKWARD write response bus -----------------------------------------------------//
  input  logic [AXI_ID_OUT-1:0]                                         bid_i,
  input  logic                                                          bvalid_i,
  output logic                                                          bready_o,
  // To BW ALLOC --> FROM BW DECODER
  output logic [N_TARG_PORT-1:0]                                        bvalid_o,
  input  logic [N_TARG_PORT-1:0]                                        bready_i,


  //AXI BACKWARD read data bus ----------------------------------------------------------//
  input  logic [AXI_ID_OUT-1:0]                                         rid_i,
  input  logic                                                          rvalid_i,  //slave data valid
  output logic                                                          rready_o,  //master ready to accept
  // To BR ALLOC --> FROM BW DECODER
  output logic [N_TARG_PORT-1:0]                                        rvalid_o,
  input  logic [N_TARG_PORT-1:0]                                        rready_i,




  //AXI write address bus --------------------------------------------------------------//
  output  logic [AXI_ID_OUT-1:0]                                        awid_o,         //
  output  logic [AXI_ADDRESS_W-1:0]                                     awaddr_o,       //
  output  logic [ 7:0]                                                  awlen_o,        //burst length is 1 + (0 - 15)
  output  logic [ 2:0]                                                  awsize_o,       //size of each transfer in burst
  output  logic [ 1:0]                                                  awburst_o,      //for bursts>1, accept only incr burst=01
  output  logic                                                         awlock_o,       //only normal access supported axs_awlock=00
  output  logic [ 3:0]                                                  awcache_o,      //
  output  logic [ 2:0]                                                  awprot_o,       //
  output  logic [ 3:0]                                                  awregion_o,     //
  output  logic [ 5:0]                                                  awatop_o,       //
  output  logic [ AXI_USER_W-1:0]                                       awuser_o,       //
  output  logic [ 3:0]                                                  awqos_o,        //
  output  logic                                                         awvalid_o,      //master addr valid
  input   logic                                                         awready_i,      //slave ready to accept
  // -----------------------------------------------------------------------------------//

  //AXI write data bus -----------------------------------------------------------------//
  output  logic  [AXI_DATA_W-1:0]                                       wdata_o,
  output  logic  [AXI_NUMBYTES-1:0]                                     wstrb_o,        //1 strobe per byte
  output  logic                                                         wlast_o,        //last transfer in burst
  output  logic [AXI_USER_W-1:0]                                        wuser_o,
  output  logic                                                         wvalid_o,       //master data valid
  input   logic                                                         wready_i,       //slave ready to accept
  // -----------------------------------------------------------------------------------//


  //AXI read address bus ---------------------------------------------------------------//
  output  logic [ AXI_ID_OUT-1:0]                                       arid_o,
  output  logic [ AXI_ADDRESS_W-1:0]                                    araddr_o,
  output  logic [ 7:0]                                                  arlen_o,        //burst length - 1 to 16
  output  logic [ 2:0]                                                  arsize_o,       //size of each transfer in burst
  output  logic [ 1:0]                                                  arburst_o,      //for bursts>1, accept only incr burst=01
  output  logic                                                         arlock_o,       //only normal access supported axs_awlock=00
  output  logic [ 3:0]                                                  arcache_o,
  output  logic [ 2:0]                                                  arprot_o,
  output  logic [ 3:0]                                                  arregion_o,     //
  output  logic [ AXI_USER_W-1:0]                                       aruser_o,       //
  output  logic [ 3:0]                                                  arqos_o,        //
  output  logic                                                         arvalid_o,      //master addr valid
  input   logic                                                         arready_i       //slave ready to accept
  // -----------------------------------------------------------------------------------//

);





logic                                           push_ID;
logic [LOG_N_TARG+N_TARG_PORT-1:0]              ID;
logic                                           grant_FIFO_ID;




axi_AR_allocator
#(
    .AXI_ADDRESS_W (  AXI_ADDRESS_W  ),
    .AXI_USER_W    (  AXI_USER_W     ),
    .N_TARG_PORT   (  N_TARG_PORT    ),
    .AXI_ID_IN     (  AXI_ID_IN      )
)
AR_ALLOCATOR
(
  .clk       (  clk        ),
  .rst_n     (  rst_n      ),

  //AXI Read address bus ----------------------------------------------------------------
  .arid_i    (  arid_i     ),  //
  .araddr_i  (  araddr_i   ),  //
  .arlen_i   (  arlen_i    ),  //burst length - 1 to 16
  .arsize_i  (  arsize_i   ),  //size of each transfer in burst
  .arburst_i (  arburst_i  ),  //for bursts>1(), accept only incr burst=01
  .arlock_i  (  arlock_i   ),  //only normal access supported axs_arlock=00
  .arcache_i (  arcache_i  ),  //
  .arprot_i  (  arprot_i   ),  //
  .arregion_i(  arregion_i ),  //
  .aruser_i  (  aruser_i   ),  //
  .arqos_i   (  arqos_i    ),  //

  .arvalid_i (  arvalid_i  ),  //master addr valid
  .arready_o (  arready_o  ),  //slave ready to accept


  //AXI Read address bus--> OUT----------------------------------------------------------------
  .arid_o    (  arid_o    ),
  .araddr_o  (  araddr_o  ),
  .arlen_o   (  arlen_o   ),   //burst length - 1 to 16
  .arsize_o  (  arsize_o  ),  //size of each transfer in burst
  .arburst_o (  arburst_o ), //for bursts>1(), accept only incr burst=01
  .arlock_o  (  arlock_o  ),  //only normal access supported axs_arlock=00
  .arcache_o (  arcache_o ),
  .arprot_o  (  arprot_o  ),
  .arregion_o(  arregion_o),      //
  .aruser_o  (  aruser_o  ),      //
  .arqos_o   (  arqos_o   ),      //

  .arvalid_o (  arvalid_o ), //master addr valid
  .arready_i (  arready_i )  //slave ready to accept
);


axi_AW_allocator
#(
    .AXI_ADDRESS_W  (  AXI_ADDRESS_W ),
    .AXI_USER_W     (  AXI_USER_W    ),
    .N_TARG_PORT    (  N_TARG_PORT   ),
    .AXI_ID_IN      (  AXI_ID_IN     )
)
AW_ALLOCATOR
(
  .clk        (  clk        ),
  .rst_n      (  rst_n      ),

  //AXI write address bus ----------------------------------------------------------------
  .awid_i     (  awid_i     ),    //
  .awaddr_i   (  awaddr_i   ),    //
  .awlen_i    (  awlen_i    ),    //burst length is 1 + (0 - 15)
  .awsize_i   (  awsize_i   ),    //size of each transfer in burst
  .awburst_i  (  awburst_i  ),    //for bursts>1,  accept only incr burst=01
  .awlock_i   (  awlock_i   ),    //only normal access supported axs_awlock=00
  .awcache_i  (  awcache_i  ),    //
  .awprot_i   (  awprot_i   ),    //
  .awregion_i (  awregion_i ),    //
  .awatop_i   (  awatop_i   ),    //
  .awuser_i   (  awuser_i   ),    //
  .awqos_i    (  awqos_i    ),    //

  .awvalid_i  (  awvalid_i  ),    //master addr valid
  .awready_o  (  awready_o  ),    //slave ready to accept


  //AXI write address bus--> OUT----------------------------------------------------------------
  .awid_o     (  awid_o    ),     // Append the Master ID on the MSB bit
  .awaddr_o   (  awaddr_o  ),     //
  .awlen_o    (  awlen_o   ),     //burst length is 1 + (0 - 15)
  .awsize_o   (  awsize_o  ),     //size of each transfer in burst
  .awburst_o  (  awburst_o ),     //for bursts>1,  accept only incr burst=01
  .awlock_o   (  awlock_o  ),   //only normal access supported axs_awlock=00
  .awcache_o  (  awcache_o ),  //
  .awprot_o   (  awprot_o  ),     //

  .awregion_o (  awregion_o ),    //
  .awatop_o   (  awatop_o   ),    //
  .awuser_o   (  awuser_o   ),    //
  .awqos_o    (  awqos_o    ),    //

  .awvalid_o  (  awvalid_o  ),    //master addr valid
  .awready_i  (  awready_i  ),    //slave ready to accept



  // PUSH Interface to DW allocator
  .push_ID_o  (  push_ID),
  .ID_o       (  ID     ),  // {BIN_ID(  ),  OH_ID};
  .grant_FIFO_ID_i ( grant_FIFO_ID )
);


axi_DW_allocator
#(
    .AXI_USER_W     (AXI_USER_W),
    .N_TARG_PORT    (N_TARG_PORT),
    .FIFO_DEPTH     (FIFO_DW_DEPTH),
    .AXI_DATA_W     (AXI_DATA_W)
)
DW_ALLOC
(
  .clk        (  clk       ),
  .rst_n      (  rst_n     ),
  .test_en_i  ( test_en_i  ),

  //AXI write data bus --> Processor Side -----------------------------------------
  .wdata_i    (  wdata_i   ),
  .wstrb_i    (  wstrb_i   ),    //1 strobe per byte
  .wlast_i    (  wlast_i   ),    //last transfer in burst
  .wuser_i    (  wuser_i   ),    // User sideband signal

  .wvalid_i   (  wvalid_i  ),   //master data valid
  .wready_o   (  wready_o  ),   //slave ready to accept


  //AXI write data bus --> Slave Side -----------------------------------------
  .wdata_o    (  wdata_o   ),
  .wstrb_o    (  wstrb_o   ),    //1 strobe per byte
  .wlast_o    (  wlast_o   ),    //last transfer in burst
  .wuser_o    (  wuser_o   ),    // User sideband signal

  .wvalid_o   (  wvalid_o  ),   //master data valid
  .wready_i   (  wready_i  ),   //slave ready to accept


  // PUSH Interface to DW allocator
  .push_ID_i        (  push_ID  ),
  .ID_i             (  ID       ),  // {BIN_ID(  ),  OH_ID};
  .grant_FIFO_ID_o  (  grant_FIFO_ID )
);



axi_address_decoder_BW
#(
   .N_TARG_PORT  (N_TARG_PORT ),
   .AXI_ID_IN    (AXI_ID_IN )
)
BW_DECODER
(
  //AXI BACKWARD write response
  .bid_i(bid_i),
  .bvalid_i(bvalid_i),
  .bready_o(bready_o),
  // To BW ALLOC --> FROM BW DECODER
  .bvalid_o(bvalid_o),
  .bready_i(bready_i)
);


axi_address_decoder_BR
#(
   .N_TARG_PORT  (N_TARG_PORT ),
   .AXI_ID_IN    (AXI_ID_IN )
)
BR_DECODER
(
  //AXI BACKWARD write response
  .rid_i(rid_i),
  .rvalid_i(rvalid_i),
  .rready_o(rready_o),
  // To BW ALLOC --> FROM BW DECODER
  .rvalid_o(rvalid_o),
  .rready_i(rready_i)
);


endmodule
