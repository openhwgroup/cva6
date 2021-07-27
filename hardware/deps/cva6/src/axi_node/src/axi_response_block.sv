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
// Module Name:    axi_response_block                                            //
// Project Name:   PULP                                                          //
// Language:       SystemVerilog                                                 //
//                                                                               //
// Description:   It groups AW,AR,W address decoders , and B and R allocators    //
//                It handles decoding errors                                     //
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

module axi_response_block
#(
   parameter           AXI_ADDRESS_W  = 32,
   parameter           AXI_DATA_W     = 64,
   parameter           AXI_USER_W     = 6,

   parameter           N_INIT_PORT    = 4,
   parameter           N_TARG_PORT    = 8,
   parameter           FIFO_DEPTH_DW  = 8,

   parameter           AXI_ID_IN      = 16,
   parameter           AXI_ID_OUT     = AXI_ID_IN + $clog2(N_TARG_PORT),
   parameter           N_REGION       = 2
)
(
   input logic                                                       clk,
   input logic                                                       rst_n,
   input logic                                                       test_en_i,

   //AXI BACKWARD read data bus ----------------------------------------------
   input  logic [N_INIT_PORT-1:0][AXI_ID_OUT-1:0]                    rid_i,
   input  logic [N_INIT_PORT-1:0][AXI_DATA_W-1:0]                    rdata_i,
   input  logic [N_INIT_PORT-1:0][ 1:0]                              rresp_i,
   input  logic [N_INIT_PORT-1:0]                                    rlast_i,   //last transfer in burst
   input  logic [N_INIT_PORT-1:0][AXI_USER_W-1:0]                    ruser_i,   //last transfer in burst
   input  logic [N_INIT_PORT-1:0]                                    rvalid_i,  //slave data valid
   output logic [N_INIT_PORT-1:0]                                    rready_o,   //master ready to accept

   //AXI BACKWARD WRITE data bus ----------------------------------------------
   input  logic [N_INIT_PORT-1:0][AXI_ID_OUT-1:0]                    bid_i,
   input  logic [N_INIT_PORT-1:0][ 1:0]                              bresp_i,
   input  logic [N_INIT_PORT-1:0][AXI_USER_W-1:0]                    buser_i,   //last transfer in burst
   input  logic [N_INIT_PORT-1:0]                                    bvalid_i,  //slave data valid
   output logic [N_INIT_PORT-1:0]                                    bready_o,   //master ready to accept

   //AXI BACKWARD read data bus ----------------------------------------------
   output  logic [AXI_ID_IN-1:0]                                     rid_o,
   output  logic [AXI_DATA_W-1:0]                                    rdata_o,
   output  logic [ 1:0]                                              rresp_o,
   output  logic                                                     rlast_o,   //last transfer in burst
   output  logic [AXI_USER_W-1:0]                                    ruser_o,
   output  logic                                                     rvalid_o,  //slave data valid
   input   logic                                                     rready_i,   //master ready to accept

   //AXI BACKWARD WRITE data bus ----------------------------------------------
   output  logic [AXI_ID_IN-1:0]                                     bid_o,
   output  logic [ 1:0]                                              bresp_o,
   output  logic [AXI_USER_W-1:0]                                    buser_o,   //last transfer in burst
   output  logic                                                     bvalid_o,  //slave data valid
   input   logic                                                     bready_i,   //master ready to accept


   // ADDRESS READ DECODER
   input  logic                                                      arvalid_i,
   input  logic [AXI_ADDRESS_W-1:0]                                  araddr_i,
   output logic                                                      arready_o,
   input  logic [AXI_ID_IN-1:0]                                      arid_i,
   input  logic [ 7:0]                                               arlen_i,
   input  logic [ AXI_USER_W-1:0]                                    aruser_i,
   output logic [N_INIT_PORT-1:0]                                    arvalid_o,
   input  logic [N_INIT_PORT-1:0]                                    arready_i,


   // ADDRESS WRITE DECODER
   input  logic                                                      awvalid_i,
   input  logic [AXI_ADDRESS_W-1:0]                                  awaddr_i,
   output logic                                                      awready_o,
   input  logic [AXI_ID_IN-1:0]                                      awid_i,
   input  logic [AXI_USER_W-1:0]                                     awuser_i,
   output logic [N_INIT_PORT-1:0]                                    awvalid_o,
   input  logic [N_INIT_PORT-1:0]                                    awready_i,

   // DATA WRITE DECODER
   input  logic                                                      wvalid_i,
   input  logic                                                      wlast_i,
   output logic                                                      wready_o,
   output logic [N_INIT_PORT-1:0]                                    wvalid_o,
   input  logic [N_INIT_PORT-1:0]                                    wready_i,


   // FROM CFG REGS
   input  logic [N_REGION-1:0][N_INIT_PORT-1:0][AXI_ADDRESS_W-1:0]   START_ADDR_i,
   input  logic [N_REGION-1:0][N_INIT_PORT-1:0][AXI_ADDRESS_W-1:0]   END_ADDR_i,
   input  logic [N_REGION-1:0][N_INIT_PORT-1:0]                      enable_region_i,
   input  logic [N_INIT_PORT-1:0]                                    connectivity_map_i
);



logic               push_DEST_DW;
logic               grant_FIFO_DEST_DW;
logic  [N_INIT_PORT-1:0]    DEST_DW;

logic                               incr_ar_req;
logic                               full_counter_ar;
logic                               outstanding_trans_ar;

logic                               error_ar_req;
logic                               error_ar_gnt;


logic                               incr_aw_req;
logic                               full_counter_aw;
logic                               outstanding_trans_aw;
logic                               handle_error_aw;
logic                               wdata_error_completed;
logic                               sample_awdata_info;
logic                               sample_ardata_info;

logic                               error_aw_req;
logic                               error_aw_gnt;
//logic   [AXI_USER_W-1:0]            error_aw_user;
//logic   [AXI_ID_IN-1:0]             error_aw_id;

axi_BW_allocator
#(
      .AXI_USER_W  ( AXI_USER_W   ),
      .N_INIT_PORT ( N_INIT_PORT  ),
      .N_TARG_PORT ( N_TARG_PORT  ),
      .AXI_DATA_W  ( AXI_DATA_W   ),
      .AXI_ID_IN   ( AXI_ID_IN    )
)
BW_ALLOC
(
      .clk                  (  clk                  ),
      .rst_n                (  rst_n                ),

      //AXI BACKWARD read data bus ----------------------------------------------
      .bid_i                (  bid_i                ),
      .bresp_i              (  bresp_i              ),
      .buser_i              (  buser_i              ),   //last transfer in burst
      .bvalid_i             (  bvalid_i             ),  //slave data valid
      .bready_o             (  bready_o             ),   //master ready to accept

      //AXI BACKWARD read data bus ----------------------------------------------
      .bid_o                (  bid_o                ),
      .bresp_o              (  bresp_o              ),
      .buser_o              (  buser_o              ),  //last transfer in burst
      .bvalid_o             (  bvalid_o             ),  //slave data valid
      .bready_i             (  bready_i             ),  //master ready to accept

      .incr_req_i           (  incr_aw_req          ),
      .full_counter_o       (  full_counter_aw      ),
      .outstanding_trans_o  (  outstanding_trans_aw ),
      .sample_awdata_info_i (  sample_awdata_info   ),

      .error_req_i          (  error_aw_req         ),
      .error_gnt_o          (  error_aw_gnt         ),
      .error_user_i         (  awuser_i             ),
      .error_id_i           (  awid_i               )
);



axi_BR_allocator
#(
      .AXI_USER_W  ( AXI_USER_W   ),
      .N_INIT_PORT ( N_INIT_PORT  ),
      .N_TARG_PORT ( N_TARG_PORT  ),
      .AXI_DATA_W  ( AXI_DATA_W   ),
      .AXI_ID_IN   ( AXI_ID_IN    )
)
BR_ALLOC
(
      .clk                  ( clk                   ),
      .rst_n                ( rst_n                 ),

      //AXI BACKWARD read data bus ----------------------------------------------
      .rid_i                ( rid_i                 ),
      .rdata_i              ( rdata_i               ),
      .rresp_i              ( rresp_i               ),
      .rlast_i              ( rlast_i               ),
      .ruser_i              ( ruser_i               ),   //last transfer in burst
      .rvalid_i             ( rvalid_i              ),  //slave data valid
      .rready_o             ( rready_o              ),   //master ready to accept

      //AXI BACKWARD read data bus ----------------------------------------------
      .rid_o                ( rid_o                 ),
      .rdata_o              ( rdata_o               ),
      .rresp_o              ( rresp_o               ),
      .rlast_o              ( rlast_o               ),
      .ruser_o              ( ruser_o               ),   //last transfer in burst
      .rvalid_o             ( rvalid_o              ),  //slave data valid
      .rready_i             ( rready_i              ),   //master ready to accept

      .incr_req_i           ( incr_ar_req           ),
      .full_counter_o       ( full_counter_ar       ),
      .outstanding_trans_o  ( outstanding_trans_ar  ),

      .error_req_i          ( error_ar_req          ),
      .error_gnt_o          ( error_ar_gnt          ),
      .error_len_i          ( arlen_i               ),
      .error_user_i         ( aruser_i              ),
      .error_id_i           ( arid_i                ),
      .sample_ardata_info_i ( sample_ardata_info    )
);




axi_address_decoder_AR
#(
    .ADDR_WIDTH   (  AXI_ADDRESS_W   ),
    .N_INIT_PORT  (  N_INIT_PORT     ),
    .N_REGION     (  N_REGION        )
)
AR_ADDR_DEC
(
    .clk                   ( clk                   ),
    .rst_n                 ( rst_n                 ),

    .arvalid_i             ( arvalid_i             ),
    .araddr_i              ( araddr_i              ),
    .arready_o             ( arready_o             ),

    .arvalid_o             ( arvalid_o             ), // REQUEST VECTOR (one for each INIT --> OH encoding)
    .arready_i             ( arready_i             ), // Grant  VECTOR (one for each INIT --> OH encoding)

    .START_ADDR_i          ( START_ADDR_i          ),
    .END_ADDR_i            ( END_ADDR_i            ),
    .enable_region_i       ( enable_region_i       ),

    .connectivity_map_i    ( connectivity_map_i    ),

    .incr_req_o            ( incr_ar_req           ),
    .full_counter_i        ( full_counter_ar       ),
    .outstanding_trans_i   ( outstanding_trans_ar  ),

    .error_req_o           ( error_ar_req          ),
    .error_gnt_i           ( error_ar_gnt          ),
    .sample_ardata_info_o  ( sample_ardata_info    )
);


axi_address_decoder_AW
#(
    .ADDR_WIDTH      (  AXI_ADDRESS_W     ),
    .N_INIT_PORT     (  N_INIT_PORT       ),
    .N_REGION        (  N_REGION          )
)
AW_ADDR_DEC
(
    .clk                      ( clk                   ),
    .rst_n                    ( rst_n                 ),

    .awvalid_i                ( awvalid_i             ),
    .awaddr_i                 ( awaddr_i              ),
    .awready_o                ( awready_o             ),

    .awvalid_o                ( awvalid_o             ), // REQUEST VECTOR (one for each INIT --> OH encoding)
    .awready_i                ( awready_i             ), // Grant  VECTOR (one for each INIT --> OH encoding)

    .grant_FIFO_DEST_i        ( grant_FIFO_DEST_DW    ),
    .DEST_o                   ( DEST_DW               ),
    .push_DEST_o              ( push_DEST_DW          ),



    .START_ADDR_i             ( START_ADDR_i          ),
    .END_ADDR_i               ( END_ADDR_i            ),
    .enable_region_i          ( enable_region_i       ),

    .connectivity_map_i       ( connectivity_map_i    ),

    .incr_req_o               ( incr_aw_req           ),
    .full_counter_i           ( full_counter_aw       ),
    .outstanding_trans_i      ( outstanding_trans_aw  ),

    .error_req_o              ( error_aw_req          ),
    .error_gnt_i              ( error_aw_gnt          ),

    .handle_error_o           ( handle_error_aw       ),
    .wdata_error_completed_i  ( wdata_error_completed ),
    .sample_awdata_info_o     ( sample_awdata_info    )

);


axi_address_decoder_DW
#(
    .N_INIT_PORT       (  N_INIT_PORT       ),
    .FIFO_DEPTH        (  FIFO_DEPTH_DW     )
)
DW_ADDR_DEC
(
    .clk                      ( clk                    ),
    .rst_n                    ( rst_n                  ),
    .test_en_i                ( test_en_i              ),

    .wvalid_i                 ( wvalid_i               ),
    .wlast_i                  ( wlast_i                ),
    .wready_o                 ( wready_o               ),

    .wvalid_o                 ( wvalid_o               ),
    .wready_i                 ( wready_i               ),

    .grant_FIFO_DEST_o        ( grant_FIFO_DEST_DW     ),
    .DEST_i                   ( DEST_DW                ),
    .push_DEST_i              ( push_DEST_DW           ),

    .handle_error_i           ( handle_error_aw        ),
    .wdata_error_completed_o  ( wdata_error_completed  )
);


endmodule
