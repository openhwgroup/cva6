// Copyright 2019 ETH Zurich and University of Bologna.
//
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Author: Stefan Mach <smach@iis.ee.ethz.ch>

module fpnew_rounding #(
  parameter int unsigned AbsWidth=2 // Width of the abolute value, without sign bit
) (
  // Input value
  input logic [AbsWidth-1:0]   abs_value_i,             // absolute value without sign
  input logic                  sign_i,
  // Rounding information
  input logic [1:0]            round_sticky_bits_i,     // round and sticky bits {RS}
  input fpnew_pkg::roundmode_e rnd_mode_i,
  input logic                  effective_subtraction_i, // sign of inputs affects rounding of zeroes
  // Output value
  output logic [AbsWidth-1:0]  abs_rounded_o,           // absolute value without sign
  output logic                 sign_o,
  // Output classification
  output logic                 exact_zero_o             // output is an exact zero
);

  logic round_up; // Rounding decision

  // Take the rounding decision according to RISC-V spec
  // RoundMode | Mnemonic | Meaning
  // :--------:|:--------:|:-------
  //    000    |   RNE    | Round to Nearest, ties to Even
  //    001    |   RTZ    | Round towards Zero
  //    010    |   RDN    | Round Down (towards -\infty)
  //    011    |   RUP    | Round Up (towards \infty)
  //    100    |   RMM    | Round to Nearest, ties to Max Magnitude
  //  others   |          | *invalid*
  always_comb begin : rounding_decision
    unique case (rnd_mode_i)
      fpnew_pkg::RNE: // Decide accoring to round/sticky bits
        unique case (round_sticky_bits_i)
          2'b00,
          2'b01: round_up = 1'b0;           // < ulp/2 away, round down
          2'b10: round_up = abs_value_i[0]; // = ulp/2 away, round towards even result
          2'b11: round_up = 1'b1;           // > ulp/2 away, round up
          default: round_up = fpnew_pkg::DONT_CARE;
        endcase
      fpnew_pkg::RTZ: round_up = 1'b0; // always round down
      fpnew_pkg::RDN: round_up = (| round_sticky_bits_i) ? sign_i  : 1'b0; // to 0 if +, away if -
      fpnew_pkg::RUP: round_up = (| round_sticky_bits_i) ? ~sign_i : 1'b0; // to 0 if -, away if +
      fpnew_pkg::RMM: round_up = round_sticky_bits_i[1]; // round down if < ulp/2 away, else up
      default: round_up = fpnew_pkg::DONT_CARE; // propagate x
    endcase
  end

  // Perform the rounding, exponent change and overflow to inf happens automagically
  assign abs_rounded_o = abs_value_i + round_up;

  // True zero result is a zero result without dirty round/sticky bits
  assign exact_zero_o = (abs_value_i == '0) && (round_sticky_bits_i == '0);

  // In case of effective subtraction (thus signs of addition operands must have differed) and a
  // true zero result, the result sign is '-' in case of RDN and '+' for other modes.
  assign sign_o = (exact_zero_o && effective_subtraction_i)
                  ? (rnd_mode_i == fpnew_pkg::RDN)
                  : sign_i;

endmodule
