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
// Module Name:    axi_DW_allocator                                              //
// Project Name:   PULP                                                          //
// Language:       SystemVerilog                                                 //
//                                                                               //
// Description:   Data Write Allocator: it selects one write data channel among  //
//                the available slave ports (multiplexer). The routing info      //
//                are provided by the data ID previusly stored during the addr   //
//                phase.                                                         //
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

module axi_DW_allocator
#(
    parameter                   AXI_USER_W     = 6,
    parameter                   N_TARG_PORT    = 7,
    parameter                   LOG_N_TARG     = $clog2(N_TARG_PORT),
    parameter                   FIFO_DEPTH     = 8,

    parameter                   AXI_DATA_W     = 64,
    parameter                   AXI_NUMBYTES   = AXI_DATA_W/8
)
(
  input  logic                                                          clk,
  input  logic                                                          rst_n,
  input  logic                                                          test_en_i,

  //AXI write data bus --> Processor Side -----------------------------------------
  input  logic [N_TARG_PORT-1:0] [AXI_DATA_W-1:0]                       wdata_i,
  input  logic [N_TARG_PORT-1:0] [AXI_NUMBYTES-1:0]                     wstrb_i,   //1 strobe per byte
  input  logic [N_TARG_PORT-1:0]                                        wlast_i,   //last transfer in burst
  input  logic [N_TARG_PORT-1:0][AXI_USER_W-1:0]                        wuser_i,   // User sideband signal

  input  logic [N_TARG_PORT-1:0]                                        wvalid_i,  //master data valid
  output logic [N_TARG_PORT-1:0]                                        wready_o,  //slave ready to accept


  //AXI write data bus --> Slave Side -----------------------------------------
  output logic  [AXI_DATA_W-1:0]                                        wdata_o,
  output logic  [AXI_NUMBYTES-1:0]                                      wstrb_o,   //1 strobe per byte
  output logic                                                          wlast_o,   //last transfer in burst
  output logic  [AXI_USER_W-1:0]                                        wuser_o,   // User sideband signal

  output logic                                                          wvalid_o,  //master data valid
  input  logic                                                          wready_i,  //slave ready to accept


  // PUSH Interface to DW allocator
  input  logic                                                          push_ID_i,
  input  logic [LOG_N_TARG+N_TARG_PORT-1:0]                             ID_i, // {BIN_ID, OH_ID};
  output logic                                                          grant_FIFO_ID_o
);

localparam      AUX_WIDTH = AXI_DATA_W + AXI_NUMBYTES + 1 + AXI_USER_W;

logic                                                           pop_from_ID_FIFO;
logic                                                           valid_ID;
logic [LOG_N_TARG+N_TARG_PORT-1:0]                              ID_int;

logic [LOG_N_TARG-1:0]                                          ID_int_BIN;
logic [N_TARG_PORT-1:0]                                         ID_int_OH;

logic [AUX_WIDTH-1:0]                                           AUX_VECTOR_OUT;
logic [N_TARG_PORT-1:0][AUX_WIDTH-1:0]                          AUX_VECTOR_IN;

enum logic { SINGLE_IDLE, BURST }                               CS, NS;

genvar i;





generate

  for(i=0; i<N_TARG_PORT; i++)
  begin : AUX_VECTOR_BINDING
      assign  AUX_VECTOR_IN[i] = { wdata_i[i], wstrb_i[i], wlast_i[i], wuser_i[i] };
  end


endgenerate



assign {wdata_o,wstrb_o,wlast_o,wuser_o} = AUX_VECTOR_OUT;

logic empty, full;
fifo_v2 #(
    .FALL_THROUGH(1'b0),
    .DATA_WIDTH(LOG_N_TARG+N_TARG_PORT),
    .DEPTH(FIFO_DEPTH)
)
MASTER_ID_FIFO
(
    .clk_i        (clk              ),
    .rst_ni       (rst_n            ),
    .flush_i      ( 1'b0            ),
    .testmode_i   (test_en_i        ),
    .alm_empty_o  ( ), // open
    .alm_full_o   ( ), // open
    .data_i       (ID_i             ),
    .push_i       (push_ID_i        ),
    .full_o       (full             ),
    .data_o       (ID_int           ),
    .empty_o      (empty            ),
    .pop_i        (pop_from_ID_FIFO )
);

assign valid_ID = ~empty;
assign grant_FIFO_ID_o = ~full;

  assign  ID_int_BIN = ID_int[LOG_N_TARG+N_TARG_PORT-1:N_TARG_PORT];
  assign  ID_int_OH  = ID_int[N_TARG_PORT-1:0];






  always_ff @(posedge clk, negedge rst_n)
  begin : UPDATE_STATE_FSM
      if(rst_n == 1'b0)
      begin
        CS             <= SINGLE_IDLE;
      end
      else
      begin
        CS             <= NS;
      end
  end



  always_comb
  begin : NEXT_STATE_FSM

      pop_from_ID_FIFO = 1'b0;

      wvalid_o          = 1'b0;
      wready_o          = '0;


      case(CS)

          SINGLE_IDLE :
          begin : _CS_IN_SINGLE_IDLE
                if(valid_ID)
                begin : _valid_ID
                      wvalid_o   = wvalid_i[ID_int_BIN] ;
                      wready_o   = {N_TARG_PORT{wready_i}} & ID_int_OH;

                      if(wvalid_i[ID_int_BIN] & wready_i)
                      begin : _granted_request
                        if(wlast_i[ID_int_BIN])
                        begin : _last_packet
                          NS               = SINGLE_IDLE;
                          pop_from_ID_FIFO = 1'b1;
                        end
                        else
                        begin : _payload_packet
                          NS = BURST;
                          pop_from_ID_FIFO = 1'b0;
                        end
                      end
                      else
                      begin : _not_granted_request
                           NS                 = SINGLE_IDLE;
                           pop_from_ID_FIFO   = 1'b0;
                      end
                end
                else // not valid ID
                begin : _not_valid_ID
                           NS                 = SINGLE_IDLE;
                           pop_from_ID_FIFO   = 1'b0;
                           wvalid_o           = 1'b0;
                           wready_o           = '0;
                end
          end






          BURST : begin : _CS_IN_BUSRT

                      wvalid_o    = wvalid_i[ID_int_BIN];
                      wready_o   = {N_TARG_PORT{wready_i}} & ID_int_OH & {N_TARG_PORT{valid_ID}};


                      if(wvalid_i[ID_int_BIN] & wready_i)
                      begin
                        if(wlast_i[ID_int_BIN])
                        begin
                          NS               = SINGLE_IDLE;
                          pop_from_ID_FIFO = 1'b1;
                        end
                        else
                        begin
                          NS = BURST;
                          pop_from_ID_FIFO = 1'b0;
                        end
                      end
                      else
                      begin
                           NS                 = BURST;
                           pop_from_ID_FIFO   = 1'b0;
                      end

          end

          default : begin
                          NS               = SINGLE_IDLE;
                          pop_from_ID_FIFO = 1'b0;
                          wvalid_o         = 1'b0;
                          wready_o          = '0;
          end

          endcase


  end




  axi_multiplexer
  #(
    .DATA_WIDTH(AUX_WIDTH),
    .N_IN(N_TARG_PORT)
  )
  WRITE_DATA_MUX
  (
    .IN_DATA(AUX_VECTOR_IN),
    .OUT_DATA(AUX_VECTOR_OUT),
    .SEL(ID_int_BIN)
  );

endmodule
