// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Igor Loi <igor.loi@unibo.it>

module generic_LFSR_8bit
  #(
    parameter OH_WIDTH      = 4,
    parameter BIN_WIDTH     = $clog2(OH_WIDTH),
    parameter SEED          = 8'b00000000
    ) 
   (
    output logic [OH_WIDTH-1:0]    data_OH_o,   // One hot encoding
    output logic [BIN_WIDTH-1:0]   data_BIN_o,  // Binary encoding
    input  logic                   enable_i,        //
    input  logic                   clk,             //
    input  logic                   rst_n            //
    );
   
   logic [7:0] 			   out;
   logic                           linear_feedback;
   logic [BIN_WIDTH-1:0] 	   temp_ref_way;
   
   
   //-------------Code Starts Here-------
   assign linear_feedback = !(out[7] ^ out[3] ^ out[2] ^ out[1]); // TAPS for XOR feedback
   
   assign data_BIN_o = temp_ref_way;
   
   always_ff @(posedge clk, negedge rst_n)
     begin
	if (rst_n == 1'b0)
	  begin
	     out <= SEED ;
	  end 
	else if (enable_i) 
          begin
             out <= {out[6],out[5],out[4],out[3],out[2],out[1],out[0], linear_feedback};
          end 
     end
   
   generate
      
      if(OH_WIDTH == 2)
	assign temp_ref_way = out[1];
      else
	assign temp_ref_way = out[BIN_WIDTH:1];
   endgenerate
   
   // Bin to One Hot Encoder
   always_comb
     begin
	data_OH_o = '0;
	data_OH_o[temp_ref_way] = 1'b1;
     end
   
endmodule
