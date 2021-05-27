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
// Module Name:    axi_BW_allocator                                              //
// Project Name:   PULP                                                          //
// Language:       SystemVerilog                                                 //
//                                                                               //
// Description:   Master slice ( buffer) for backward write channel              //
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

module axi_BW_allocator #(
    parameter                   AXI_USER_W     = 6,
    parameter                   N_INIT_PORT    = 1,
    parameter                   N_TARG_PORT    = 7,
    parameter                   AXI_DATA_W     = 64,
    parameter                   AXI_ID_IN      = 16,
    parameter                   AXI_ID_OUT     = AXI_ID_IN + $clog2(N_TARG_PORT)
)(
  input  logic                                                          clk,
  input  logic                                                          rst_n,

  //AXI BACKWARD read data bus ----------------------------------------------
  input  logic [N_INIT_PORT-1:0][AXI_ID_OUT-1:0]                        bid_i,
  input  logic [N_INIT_PORT-1:0][ 1:0]                                  bresp_i,
  input  logic [N_INIT_PORT-1:0][AXI_USER_W-1:0]                        buser_i,   //last transfer in burst
  input  logic [N_INIT_PORT-1:0]                                        bvalid_i,  //slave data valid
  output logic [N_INIT_PORT-1:0]                                        bready_o,   //master ready to accept

  //AXI BACKWARD read data bus ----------------------------------------------
  output  logic [AXI_ID_IN-1:0]                                         bid_o,
  output  logic [ 1:0]                                                  bresp_o,
  output  logic [AXI_USER_W-1:0]                                        buser_o,   //last transfer in burst
  output  logic                                                         bvalid_o,  //slave data valid
  input   logic                                                         bready_i,   //master ready to accept


  input   logic                                                         incr_req_i,
  output  logic                                                         full_counter_o,
  output  logic                                                         outstanding_trans_o,
  input   logic                                                         sample_awdata_info_i,

  input   logic                                                         error_req_i,
  output  logic                                                         error_gnt_o,
  input   logic [AXI_USER_W-1:0]                                        error_user_i,
  input   logic [AXI_ID_IN-1:0]                                         error_id_i
);

localparam      AUX_WIDTH = 2 + AXI_USER_W;


logic [N_INIT_PORT-1:0][AUX_WIDTH-1:0]                                  AUX_VECTOR_IN;
logic [AUX_WIDTH-1:0]                                                   AUX_VECTOR_OUT;
logic [N_INIT_PORT-1:0][AXI_ID_IN-1:0]                                  bid_int;

genvar i;

logic [9:0]                                                             outstanding_counter;
logic                                                                   decr_req;
logic   [AXI_USER_W-1:0]                                                error_user_S;
logic   [AXI_ID_IN-1:0]                                                 error_id_S;

enum logic [1:0]                                                {OPERATIVE, ERROR_SINGLE, ERROR_BURST} CS, NS;



// Output of the arbiter, to be multiplexed in the FSM
logic [AXI_ID_IN-1:0]                                                   arb_bid;
logic [1:0]                                                             arb_bresp;
logic [AXI_USER_W-1:0]                                                  arb_buser;
logic                                                                   arb_bvalid;
logic                                                                   arb_bready;





assign {arb_buser, arb_bresp} = AUX_VECTOR_OUT;


// -------------------------------------------------------------------------   //
// -------------------------------------------------------------------------   //
//                         TRACK PENDING TRANSACTIONS                          //
// -------------------------------------------------------------------------   //
// -------------------------------------------------------------------------   //





assign outstanding_trans_o = (outstanding_counter == '0) ? 1'b0 : 1'b1;

assign decr_req = bvalid_o & bready_i;

assign full_counter_o = (outstanding_counter == '1) ? 1'b1 : 1'b0;


always_ff @(posedge clk, negedge rst_n)
begin
    if(rst_n == 1'b0)
      outstanding_counter  <= '0;
    else
    begin
      case({incr_req_i, decr_req})
        2'b00: begin  outstanding_counter  <= outstanding_counter; end
        2'b01:
        begin
                if(outstanding_counter != '0)
                    outstanding_counter  <= outstanding_counter - 1'b1;
                else
                    outstanding_counter  <= '0;
        end
        2'b10:
        begin
                if(outstanding_counter != '1)
                    outstanding_counter  <= outstanding_counter + 1'b1;
                else
                    outstanding_counter  <= '1;
        end
        2'b11: begin  outstanding_counter  <= outstanding_counter; end
      endcase
    end
end


always_ff @(posedge clk, negedge rst_n)
begin
  if(rst_n == 1'b0)
  begin
    error_user_S <= '0;
    error_id_S   <= '0;
  end
  else
  begin
    if(sample_awdata_info_i)
    begin
      error_user_S <= error_user_i;
      error_id_S   <= error_id_i;
    end
  end
end



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
  //default Values
  bid_o       = arb_bid;
  bresp_o     = arb_bresp;
  buser_o     = arb_buser;
  bvalid_o    = arb_bvalid;
  arb_bready  = bready_i;

  error_gnt_o      = 1'b0;


  case(CS)

    OPERATIVE :
    begin
        error_gnt_o = 1'b0;

        if((error_req_i == 1'b1) && (outstanding_trans_o == 1'b0))
        begin
            NS = ERROR_SINGLE;
        end
        else
        begin
          NS = OPERATIVE;
        end
    end


    ERROR_SINGLE :
    begin
        arb_bready  = 1'b0;
        error_gnt_o = 1'b1;
        bresp_o     = axi_pkg::RESP_DECERR;
        bvalid_o    = 1'b1;
        buser_o     = error_user_S;
        bid_o       = error_id_S;

        if(bready_i)
          NS = OPERATIVE;
        else
          NS = ERROR_SINGLE;
    end



    default :
    begin
        NS             = OPERATIVE;
        error_gnt_o      = 1'b0;
    end



  endcase
end
// -------------------------------------------------------------------------   //
// -------------------------------------------------------------------------   //


generate

  for(i=0;i<N_INIT_PORT;i++)
  begin : AUX_VECTOR_BINDING
      assign AUX_VECTOR_IN[i] =  { buser_i[i], bresp_i[i]};
  end

  for(i=0;i<N_INIT_PORT;i++)
  begin : BID_VECTOR_BINDING
      assign bid_int[i] =  bid_i[i][AXI_ID_IN-1:0];
  end



if(N_INIT_PORT == 1)
begin : DIRECT_BINDING
    assign arb_bvalid     = bvalid_i;
    assign AUX_VECTOR_OUT = AUX_VECTOR_IN;
    assign arb_bid        = bid_int;
    assign bready_o       = bready_i;
end
else
begin : ARBITER

  axi_node_arbiter #(
    .AUX_WIDTH  (AUX_WIDTH),
    .ID_WIDTH   (AXI_ID_IN),
    .N_MASTER   (N_INIT_PORT)
  ) i_arbiter (
    .clk_i        (clk),
    .rst_ni       (rst_n),

    .inp_id_i     (bid_int),
    .inp_aux_i    (AUX_VECTOR_IN),
    .inp_valid_i  (bvalid_i),
    .inp_ready_o  (bready_o),

    .oup_id_o     (arb_bid),
    .oup_aux_o    (AUX_VECTOR_OUT),
    .oup_valid_o  (arb_bvalid),
    .oup_ready_i  (arb_bready)
  );

end

endgenerate




endmodule
