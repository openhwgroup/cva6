// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Description: This file contains power-related cells
//              Mainly shifters at the moment.

module cluster_level_shifter_in (
  input  logic in_i,
  output logic out_o
);

  assign out_o = in_i;

endmodule

module cluster_level_shifter_in_clamp (
  input  logic in_i,
  output logic out_o,
  input  logic clamp_i
);

  assign out_o = clamp_i ? 1'b0 : in_i;

endmodule

module cluster_level_shifter_inout (
  input  logic data_i,
  output logic data_o
);

  assign data_o = data_i;

endmodule

module cluster_level_shifter_out (
  input  logic in_i,
  output logic out_o
);

  assign out_o = in_i;

endmodule

module cluster_level_shifter_out_clamp (
  input  logic in_i,
  output logic out_o,
  input  logic clamp_i
);

  assign out_o = clamp_i ? 1'b0 : in_i;

endmodule
