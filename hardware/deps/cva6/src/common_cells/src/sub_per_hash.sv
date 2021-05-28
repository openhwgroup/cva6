// Copyright (c) 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Author: Wolfgang Roenninger <wroennin@ethz.ch>

// This module implements a fully parameterizable substitution-permutation hash
// function. The hash is structured in stages consisting of a shuffle of the input bits
// and then xoring for each bit 3 pseudo-random bits of the shuffeled vector.
// The hash function is NOT cryptographically secure!
// From the keys it computes a sequence of pseudo-random numbers, which determine the permutations
// and substitutions. As pseudo random generator a multiplicative linear congruential
// generator is used and uses different constants for the computation of the permutation
// and substitution respectively.
// The permutation shuffles the bits using a variant of the Fisher-Yates shuffle algorithm.
// The substitution per stage is the xor of 3 pseudo random bits of the previous stage.
// As shifting and xoring of a signal do not change its distribution, the distribution
// of the output hash is the same as the one of the input data.
//
// Parameters:
// - `InpWidth`:   The input width of the vector `data_i`.
// - `HashWidth`:  The output width of the substitution-permutation hash.
// - `NoRounds`:   The amount of permutation, substitution stages generated. Translates
//                 into how many levels of xor's there will be before optimization.
// - `PermuteKey`: The Key for the pseudo-random generator used for determining the exact
//                 permutation (shuffled wiring between each xor stage) at compile/elaboration.
//                 Any `int unsigned` value can be used as key, however one should examine the
//                 output of the hash function.
// - `XorKey`:     The Key for the pseudo-random generator used for determining the xor
//                 of bits between stages. The same principles as for `PermuteKey` applies,
//                 however one should look that both keys have a greatest common divisor of 1.

module sub_per_hash #(
  parameter int unsigned InpWidth   = 32'd11,
  parameter int unsigned HashWidth  = 32'd5,
  parameter int unsigned NoRounds   = 32'd1,
  parameter int unsigned PermuteKey = 32'd299034753,
  parameter int unsigned XorKey     = 32'd4094834
) (
  // is purely combinational
  input  logic [InpWidth-1:0]     data_i,
  output logic [HashWidth-1:0]    hash_o,
  output logic [2**HashWidth-1:0] hash_onehot_o
);

  // typedefs and respective localparams
  typedef int unsigned perm_lists_t [NoRounds][InpWidth];
  localparam perm_lists_t PERMUTATIONS = get_permutations(PermuteKey);
  // encoding for inner most array:
  // position 0 indicates the number of inputs, 2 or 3
  // the other positions 1 - 3 indicate the inputs
  typedef int unsigned xor_stages_t [NoRounds][InpWidth][3];
  localparam xor_stages_t XOR_STAGES = get_xor_stages(XorKey);

  // stage signals
  logic [NoRounds-1:0][InpWidth-1:0] permuted, xored;

  // for each round
  for (genvar r = 0; r < NoRounds; r++) begin : gen_round
    // for each bit
    for (genvar i = 0; i < InpWidth ; i++) begin : gen_sub_per

      // assign the permutation
      if(r == 0) begin
        assign permuted[r][i] = data_i[PERMUTATIONS[r][i]];
      end else begin
        assign permuted[r][i] = permuted[r-1][PERMUTATIONS[r][i]];
      end

      // assign the xor substitution
      assign xored[r][i] = permuted[r][XOR_STAGES[r][i][0]] ^
                           permuted[r][XOR_STAGES[r][i][1]] ^
                           permuted[r][XOR_STAGES[r][i][2]];
    end
  end

  // output assignment, take the bottom bits of the last round
  assign hash_o = xored[NoRounds-1][HashWidth-1:0];
  // for onehot run trough a decoder
  assign hash_onehot_o = 1 << hash_o;

  // PRG is MLCG (multiplicative linear congruential generator)
  // Constant values the same as RtlUniform from Native API
  // X(n+1) = (a*X(n)+c) mod m
  // a: large prime
  // c: increment
  // m: range
  // Shuffling is a variation of the Fisher-Yates shuffle algorithm
  function automatic perm_lists_t get_permutations(input int unsigned seed);
    perm_lists_t indices;
    perm_lists_t perm_array;
    longint unsigned A = 2147483629;
    longint unsigned C = 2147483587;
    longint unsigned M = 2**31 - 1;
    longint unsigned index   = 0;
    longint unsigned advance = 0;
    longint unsigned rand_number = (A * seed + C) % M;

    // do it for each round
    for (int unsigned r = 0; r < NoRounds; r++) begin
      // initialize the index array
      for (int unsigned i = 0; i < InpWidth; i++) begin
        indices[r][i] = i;
      end
      // do the shuffling
      for (int unsigned i = 0; i < InpWidth; i++) begin
        // get the 'random' number
        if (i > 0) begin
          rand_number = (A * rand_number + C) % M;
          index = rand_number % i;
        end
        // do the shuffling
        if (i != index) begin
          perm_array[r][i]     = perm_array[r][index];
          perm_array[r][index] = indices[r][i];
        end
      end
      // advance the PRG a bit
      rand_number = (A * rand_number + C) % M;
      advance     = rand_number % NoRounds;
      for (int unsigned i = 0; i < advance; i++) begin
        rand_number = (A * rand_number + C) % M;
      end
    end
    return perm_array;
  endfunction : get_permutations

  // PRG is MLCG (multiplicative linear congruential generator)
  // Constant values the same as Numerical Recipes
  // X(n+1) = (a*X(n)+c) mod m
  // a: large prime
  // c: increment
  // m: range
  function automatic xor_stages_t get_xor_stages(input int unsigned seed);
    xor_stages_t xor_array;
    longint unsigned A = 1664525;
    longint unsigned C = 1013904223;
    longint unsigned M = 2**32;
    longint unsigned index   = 0;
    // int unsigned even    = 0;
    longint unsigned advance = 0;
    longint unsigned rand_number = (A * seed + C) % M;

    // fill the array with 'randon' inputs
    // for each xor, a even random number is two input, uneven is tree
    // for each round
    for (int unsigned r = 0; r < NoRounds; r++) begin
      // for each bit
      for (int unsigned i = 0; i < InpWidth; i++) begin
        rand_number = (A * rand_number + C) % M;
        // even = rand_number[3];
        for (int unsigned j = 0; j < 3; j++) begin
          rand_number = (A * rand_number + C) % M;
          index = rand_number % InpWidth;
          xor_array[r][i][j] = index;
        end
      end
      // advance the PRG a bit
      rand_number = (A * rand_number + C) % M;
      advance     = rand_number % NoRounds;
      for (int unsigned i = 0; i < advance; i++) begin
        rand_number = (A * rand_number + C) % M;
      end
    end
    return xor_array;
  endfunction : get_xor_stages
endmodule
