// Copyright 2020 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Florian Zaruba <zarubaf@iis.ee.ethz.ch>
//
/// # ECC Decoder
///
/// Implements SECDED (Single Error Correction, Double Error Detection) Hamming Code
/// with extended parity bit [1].
/// The module receives a data word including parity bit and decodes it according to the
/// number of data and parity bit.
///
/// 1. If no error has been detected, the syndrome will be zero and all flags will be zero.
/// 2. If a single error has been detected, the syndrome is non-zero, and `single_error_o` will be
///    asserted. The output word contains the corrected data.
/// 3. If the parity bit contained an error, the module will assert `parity_error_o`.
/// 4. In case of a double fault the syndrome is non-zero, `double_error_o` will be asserted.
///    All other status flags will be de-asserted.
///
/// [1] https://en.wikipedia.org/wiki/Hamming_code

module ecc_decode import ecc_pkg::*; #(
  /// Data width of unencoded word.
  parameter  int unsigned DataWidth   = 64,
  // Do not change
  parameter type data_t         = logic [DataWidth-1:0],
  parameter type parity_t       = logic [get_parity_width(DataWidth)-1:0],
  parameter type code_word_t    = logic [get_cw_width(DataWidth)-1:0],
  parameter type encoded_data_t = struct packed {
                                    logic parity;
                                    code_word_t code_word;
                                  }
  ) (
  /// Encoded data in
  input  encoded_data_t data_i,
  /// Corrected data out
  output data_t         data_o,
  /// Error syndrome indicates the erroneous bit position
  output parity_t       syndrome_o,
  /// A single error occurred
  output logic          single_error_o,
  /// Error received in parity bit (MSB)
  output logic          parity_error_o,
  /// A double error occurred
  output logic          double_error_o
);

  logic       parity;
  data_t      data_wo_parity;
  parity_t    syndrome;
  logic       syndrome_not_zero;
  code_word_t correct_data;

  // Check parity bit. 0 = parity equal, 1 = different parity
  assign parity = data_i.parity ^ (^data_i.code_word);

  ///!    | 0  1  2  3  4  5  6  7  8  9 10 11 12  13  14
  ///!    |p1 p2 d1 p4 d2 d3 d4 p8 d5 d6 d7 d8 d9 d10 d11
  ///! ---|----------------------------------------------
  ///! p1 | x     x     x     x     x     x     x       x
  ///! p2 |    x  x        x  x        x  x         x   x
  ///! p4 |          x  x  x  x              x  x   x   x
  ///! p8 |                      x  x  x  x  x  x   x   x

  ///! 1. Parity bit 1 covers all bit positions which have the least significant bit
  ///!    set: bit 1 (the parity bit itself), 3, 5, 7, 9, etc.
  ///! 2. Parity bit 2 covers all bit positions which have the second least
  ///!    significant bit set: bit 2 (the parity bit itself), 3, 6, 7, 10, 11, etc.
  ///! 3. Parity bit 4 covers all bit positions which have the third least
  ///!    significant bit set: bits 4–7, 12–15, 20–23, etc.
  ///! 4. Parity bit 8 covers all bit positions which have the fourth least
  ///!    significant bit set: bits 8–15, 24–31, 40–47, etc.
  ///! 5. In general each parity bit covers all bits where the bitwise AND of the
  ///!    parity position and the bit position is non-zero.
  always_comb begin : calculate_syndrome
    syndrome = 0;
    for (int unsigned i = 0; i < unsigned'($bits(parity_t)); i++) begin
      for (int unsigned j = 0; j < unsigned'($bits(code_word_t)); j++) begin
        if (|(unsigned'(2**i) & (j + 1))) syndrome[i] = syndrome[i] ^ data_i.code_word[j];
      end
    end
  end

  assign syndrome_not_zero = |syndrome;

  // correct the data word if the syndrome is non-zero
  always_comb begin
    correct_data = data_i.code_word;
    if (syndrome_not_zero) begin
      correct_data[syndrome - 1] = ~data_i.code_word[syndrome - 1];
    end
  end

  ///! Syndrome | Overall Parity (MSB) | Error Type   | Notes
  ///! --------------------------------------------------------
  ///! 0        | 0                    | No Error     |
  ///! /=0      | 1                    | Single Error | Correctable. Syndrome holds incorrect bit position.
  ///! 0        | 1                    | Parity Error | Overall parity, MSB is in error and can be corrected.
  ///! /=0      | 0                    | Double Error | Not correctable.
  assign single_error_o = parity & syndrome_not_zero;
  assign parity_error_o = parity & ~syndrome_not_zero;
  assign double_error_o = ~parity & syndrome_not_zero;

  // Extract data vector
  always_comb begin
    automatic int unsigned idx; // bit index
    data_wo_parity = '0;
    idx = 0;

    for (int unsigned i = 1; i < unsigned'($bits(code_word_t)) + 1; i++) begin
      // if i is a power of two we are indexing a parity bit
      if (unsigned'(2**$clog2(i)) != i) begin
        data_wo_parity[idx] = correct_data[i - 1];
        idx++;
      end
    end
  end

  assign data_o = data_wo_parity;

endmodule
