// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Antonio Pullini <pullinia@iis.ee.ethz.ch>

module pulp_sync
  #(
    parameter STAGES = 2
    )
   (
    input  logic clk_i,
    input  logic rstn_i,
    input  logic serial_i,
    output logic serial_o
    );
   
   logic [STAGES-1:0] r_reg;
   
   always_ff @(posedge clk_i, negedge rstn_i)
     begin
	if(!rstn_i)
          r_reg <= 'h0;
	else
          r_reg <= {r_reg[STAGES-2:0], serial_i};
     end
   
   assign serial_o   =  r_reg[STAGES-1];
   
endmodule
