// Copyright 2017 Embecosm Limited <www.embecosm.com>
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// RAM wrapper for RI5CY
// Contributor: Jeremy Bennett <jeremy.bennett@embecosm.com>
//
// This maps the dp_ram module to the instruction and data ports of the RI5CY
// processor core.

module ram
    #(
    parameter ADDR_WIDTH = 22
  )(
    // Clock
    input  logic                   clk,

    input  logic                   instr_req_i,
    input  logic [ADDR_WIDTH-1:0]  instr_addr_i,
    output logic [127:0]           instr_rdata_o,
    output logic                   instr_rvalid_o,
    output logic                   instr_gnt_o,

    input  logic                   data_req_i,
    input  logic [ADDR_WIDTH-1:0]  data_addr_i,
    input  logic                   data_we_i,
    input  logic [3:0]             data_be_i,
    input  logic [31:0]            data_wdata_i,
    output logic [31:0]            data_rdata_o,
    output logic                   data_rvalid_o,
    output logic                   data_gnt_o
  );

   // Instantiate the ram

   dp_ram
     #(
       .ADDR_WIDTH (ADDR_WIDTH)
       )
   dp_ram_i
     (
      .clk       ( clk           ),

      .en_a_i    ( instr_req_i   ),
      .addr_a_i  ( instr_addr_i  ),
      .wdata_a_i ( '0            ),	// Not writing so ignored
      .rdata_a_o ( instr_rdata_o ),
      .we_a_i    ( '0            ),
      .be_a_i    ( 4'b1111       ),	// Always want 32-bits

      .en_b_i    ( data_req_i    ),
      .addr_b_i  ( data_addr_i   ),
      .wdata_b_i ( data_wdata_i  ),
      .rdata_b_o ( data_rdata_o  ),
      .we_b_i    ( data_we_i     ),
      .be_b_i    ( data_be_i     )
      );

   assign data_gnt_o  = data_req_i;
   assign instr_gnt_o = instr_req_i;

   always_ff @(posedge clk)
     begin
	data_rvalid_o  <= data_req_i;
	instr_rvalid_o <= instr_req_i;
     end

endmodule	// ram
