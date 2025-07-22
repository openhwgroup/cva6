// Licensed under the Solderpad Hardware Licence, Version 2.1 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Author: Munail Waqar, 10xEngineers
// Date: 03.05.2025
// Description: The Zkn extension including its subsets accelerates cryptographic workloads by introducing dedicated
// scalar instructions compliant with the RISC-V Scalar Cryptography specification. The subsets include:
// Zknd (AES Decryption and related instructions), Zkne (AES Encryption support, including AES rounds and key expansion steps),
// Zknh (SHA-256 and SHA-512 hash functions for secure hashing operations).
//
package aes_pkg;

  // ----------------------
  // AES functions
  // ----------------------

  // AES MixColumns Forward
  function automatic [31:0] aes_mixcolumn_fwd(input [31:0] x);
    begin
      aes_mixcolumn_fwd = {
        (((x[7:0] << 1) ^ ((x[7]) ? 8'h1B : 8'h00)) ^ x[7:0]) ^ x[15:8] ^ x[23:16] ^ ((x[31:24] << 1) ^ ((x[31]) ? 8'h1B : 8'h00)),
        x[7:0] ^ x[15:8] ^ ((x[23:16] << 1) ^ ((x[23]) ? 8'h1B : 8'h00)) ^ (((x[31:24] << 1) ^ ((x[31]) ? 8'h1B : 8'h00)) ^ x[31:24]),
        x[7:0] ^ ((x[15:8] << 1) ^ ((x[15]) ? 8'h1B : 8'h00)) ^ (((x[23:16] << 1) ^ ((x[23]) ? 8'h1B : 8'h00)) ^ x[23:16]) ^ x[31:24],
        ((x[7:0] << 1) ^ ((x[7]) ? 8'h1B : 8'h00)) ^ (((x[15:8] << 1) ^ ((x[15]) ? 8'h1B : 8'h00)) ^ x[15:8]) ^ x[23:16] ^ x[31:24]
      };
    end
  endfunction
  // AES subword Forward
  function automatic [31:0] aes_subword_fwd(input [31:0] word);
    aes_subword_fwd = {
      aes_sbox_fwd(word[31:24]),
      aes_sbox_fwd(word[23:16]),
      aes_sbox_fwd(word[15:8]),
      aes_sbox_fwd(word[7:0])
    };
  endfunction
  // AES Round Constant
  function automatic [31:0] aes_decode_rcon(input [3:0] r);
    case (r)
      4'h0: aes_decode_rcon = 32'h00000001;
      4'h1: aes_decode_rcon = 32'h00000002;
      4'h2: aes_decode_rcon = 32'h00000004;
      4'h3: aes_decode_rcon = 32'h00000008;
      4'h4: aes_decode_rcon = 32'h00000010;
      4'h5: aes_decode_rcon = 32'h00000020;
      4'h6: aes_decode_rcon = 32'h00000040;
      4'h7: aes_decode_rcon = 32'h00000080;
      4'h8: aes_decode_rcon = 32'h0000001b;
      4'h9: aes_decode_rcon = 32'h00000036;
      4'hA: aes_decode_rcon = 32'h00000000;
      4'hB: aes_decode_rcon = 32'h00000000;
      4'hC: aes_decode_rcon = 32'h00000000;
      4'hD: aes_decode_rcon = 32'h00000000;
      4'hE: aes_decode_rcon = 32'h00000000;
      4'hF: aes_decode_rcon = 32'h00000000;
      default: aes_decode_rcon = 32'h00000000;
    endcase
  endfunction
  // AES MixColumns Inverse
  function automatic logic [31:0] aes_mixcolumn_inv(input logic [31:0] x);
    aes_mixcolumn_inv = {
      (gfmul(x[7:0], 4'hB) ^ gfmul(x[15:8], 4'hD) ^ gfmul(x[23:16], 4'h9) ^ gfmul(x[31:24], 4'hE)),
      (gfmul(x[7:0], 4'hD) ^ gfmul(x[15:8], 4'h9) ^ gfmul(x[23:16], 4'hE) ^ gfmul(x[31:24], 4'hB)),
      (gfmul(x[7:0], 4'h9) ^ gfmul(x[15:8], 4'hE) ^ gfmul(x[23:16], 4'hB) ^ gfmul(x[31:24], 4'hD)),
      (gfmul(x[7:0], 4'hE) ^ gfmul(x[15:8], 4'hB) ^ gfmul(x[23:16], 4'hD) ^ gfmul(x[31:24], 4'h9))
    };
  endfunction
  // GF multiplication
  function automatic logic [7:0] gfmul(input logic [7:0] x, input logic [3:0] y);
    logic [7:0] result, temp;
    result = 8'h00;
    if (y[0]) result ^= x;
    if (y[1]) begin
      result ^= ((x << 1) ^ ((x[7]) ? 8'h1B : 8'h00));
    end
    if (y[2]) begin
      temp = (x << 1) ^ ((x[7]) ? 8'h1B : 8'h00);
      result ^= (temp << 1) ^ ((temp[7]) ? 8'h1B : 8'h00);
    end
    if (y[3]) begin
      temp = (x << 1) ^ ((x[7]) ? 8'h1B : 8'h00);
      temp = (temp << 1) ^ ((temp[7]) ? 8'h1B : 8'h00);
      result ^= (temp << 1) ^ ((temp[7]) ? 8'h1B : 8'h00);
    end
    return result;
  endfunction
  // AES Sbox implementation based on https://github.com/riscv/riscv-crypto
  // AES Sbox Forward
  function automatic logic [7:0] aes_sbox_fwd(input logic [7:0] in_byte);
    logic [20:0] expanded;
    logic [17:0] non_linear;
    logic [ 7:0] compressed;
    expanded = linear_top_layer(in_byte);
    non_linear = non_linear_layer(expanded);
    compressed = linear_bottom_layer(non_linear);
    aes_sbox_fwd = compressed;
  endfunction
  // AES Sbox Inverse
  function automatic logic [7:0] aes_sbox_inv(input logic [7:0] in_byte);
    logic [20:0] expanded;
    logic [17:0] non_linear;
    logic [ 7:0] compressed;
    expanded = aes_sbox_inv_top(in_byte);
    non_linear = non_linear_layer(expanded);
    compressed = aes_sbox_inv_out(non_linear);
    aes_sbox_inv = compressed;
  endfunction
  // AES Sbox Forward Top Layer
  function automatic logic [20:0] linear_top_layer(input logic [7:0] x);
    return {
      ((x[7] ^ x[4]) ^ (x[5] ^ x[2])),
      (((x[7] ^ x[4])  ^ ((x[6] ^ x[5])  ^ (x[4] ^ x[0]))) ^ ((x[0] ^ (x[6] ^ x[5]))  ^ ((x[3] ^ x[1])  ^ (x[5] ^ x[2])))),
      ((x[7] ^ x[2]) ^ (((x[7] ^ x[4]) ^ (x[3] ^ x[1])) ^ (x[6] ^ x[5]))),
      ((x[7] ^ x[2]) ^ ((x[6] ^ x[5]) ^ (x[1] ^ x[0]))),
      ((x[6] ^ x[5]) ^ (x[1] ^ x[0])),
      ((x[7] ^ x[4]) ^ ((x[6] ^ x[5]) ^ (x[4] ^ x[0]))),
      ((x[6] ^ x[5]) ^ (x[4] ^ x[0])),
      ((x[0] ^ (x[6] ^ x[5])) ^ ((x[3] ^ x[1]) ^ (x[5] ^ x[2]))),
      ((x[3] ^ x[1]) ^ (x[5] ^ x[2])),
      ((x[3] ^ x[1]) ^ (x[6] ^ x[2])),
      (((x[7] ^ x[4]) ^ (x[3] ^ x[1])) ^ (x[6] ^ x[2])),
      ((x[7] ^ x[1]) ^ (x[4] ^ x[2])),
      (((x[7] ^ x[4]) ^ (x[3] ^ x[1])) ^ (x[6] ^ x[5])),
      (x[0] ^ (x[6] ^ x[5])),
      (x[0] ^ ((x[7] ^ x[4]) ^ (x[3] ^ x[1]))),
      ((x[7] ^ x[4]) ^ (x[3] ^ x[1])),
      (x[4] ^ x[2]),
      (x[7] ^ x[1]),
      (x[7] ^ x[2]),
      (x[7] ^ x[4]),
      (x[0])
    };
  endfunction
  // AES Sbox Middle Layer
  function automatic logic [17:0] non_linear_layer(input logic [20:0] x);
    logic t1, t2, t3, t4, t5;
    logic [17:0] y;
    t1 = (((x[10] ^ (x[9] & x[5])) ^ (x[17] & x[6])) ^ ((x[4] & x[20]) ^ (x[1] & x[11])));
    t2 = ((((x[14] & x[0]) ^ (x[9] & x[5])) ^ x[18]) ^ ((x[2] & x[8]) ^ (x[1] & x[11])));
    t3 = ((((x[3] ^ x[12]) ^ (x[3] & x[12])) ^ (x[16] & x[7])) ^ ((x[4] & x[20]) ^ (x[1] & x[11])));
    t4 = ((((x[15] & x[13]) ^ (x[3] & x[12])) ^ ((x[2] & x[8]) ^ (x[1] & x[11]))) ^ x[19]);
    t5 = ((((t1 ^ t2) & (t1 & t4)) ^ ((t1 ^ t2) ^ (t3 & t1))) ^ (((t3 ^ t4) & (t2 & t3)) ^ ((t3 ^ t4) ^ (t3 & t1))));

    y[0] = (((t1 ^ t2) & (t1 & t4)) ^ ((t1 ^ t2) ^ (t3 & t1))) & x[7];
    y[1] = (t2 ^ ((t4 ^ (t3 & t1)) & (t1 ^ t2))) & x[13];
    y[2] = ((t2 ^ ((t4 ^ (t3 & t1)) & (t1 ^ t2))) ^ (t4 ^ ((t2 ^ (t3 & t1)) & (t3 ^ t4)))) & x[11];
    y[3] = (((t2 ^ ((t4 ^ (t3 & t1)) & (t1 ^ t2))) ^ (t4 ^ ((t2 ^ (t3 & t1)) & (t3 ^ t4)))) ^ t5) & x[20];
    y[4] = t5 & x[8];
    y[5] = ((t4 ^ ((t2 ^ (t3 & t1)) & (t3 ^ t4))) ^ (((t3 ^ t4) & (t2 & t3)) ^ ((t3 ^ t4) ^ (t3 & t1)))) & x[9];
    y[6] = (((t3 ^ t4) & (t2 & t3)) ^ ((t3 ^ t4) ^ (t3 & t1))) & x[17];
    y[7] = (t4 ^ ((t2 ^ (t3 & t1)) & (t3 ^ t4))) & x[14];
    y[8] = ((t2 ^ ((t4 ^ (t3 & t1)) & (t1 ^ t2))) ^ (((t1 ^ t2) & (t1 & t4)) ^ ((t1 ^ t2) ^ (t3 & t1)))) & x[3];
    y[9] = (((t1 ^ t2) & (t1 & t4)) ^ ((t1 ^ t2) ^ (t3 & t1))) & x[16];
    y[10] = (t2 ^ ((t4 ^ (t3 & t1)) & (t1 ^ t2))) & x[15];
    y[11] = ((t2 ^ ((t4 ^ (t3 & t1)) & (t1 ^ t2))) ^ (t4 ^ ((t2 ^ (t3 & t1)) & (t3 ^ t4)))) & x[1];
    y[12] = (((t2 ^ ((t4 ^ (t3 & t1)) & (t1 ^ t2))) ^ (t4 ^ ((t2 ^ (t3 & t1)) & (t3 ^ t4)))) ^ t5) & x[4];
    y[13] = t5 & x[2];
    y[14] = ((t4 ^ ((t2 ^ (t3 & t1)) & (t3 ^ t4))) ^ (((t3 ^ t4) & (t2 & t3)) ^ ((t3 ^ t4) ^ (t3 & t1)))) & x[5];
    y[15] = (((t3 ^ t4) & (t2 & t3)) ^ ((t3 ^ t4) ^ (t3 & t1))) & x[6];
    y[16] = (t4 ^ ((t2 ^ (t3 & t1)) & (t3 ^ t4))) & x[0];
    y[17] = ((t2 ^ ((t4 ^ (t3 & t1)) & (t1 ^ t2))) ^ (((t1 ^ t2) & (t1 & t4)) ^ ((t1 ^ t2) ^ (t3 & t1)))) & x[12];
    return y;
  endfunction
  // AES Sbox Forward Bottom Layer
  function automatic logic [7:0] linear_bottom_layer(input logic [17:0] x);
    logic [7:0] y;
    y[0] = ((x[12] ^ (x[17] ^ x[11])) ^~ ((x[8] ^ (x[1] ^ x[9])) ^ (x[14] ^ x[16])));
    y[1] = ((x[0] ^ (x[11] ^ x[12])) ^~ ((x[1] ^ x[9]) ^ (x[3] ^ (x[4] ^ x[8]))));
    y[2] = (((x[12] ^ (x[17] ^ x[11])) ^ (x[3] ^ (x[4] ^ x[8]))) ^ ((x[10] ^ (x[14] ^ x[16])) ^ (x[7] ^ (x[0] ^ x[6]))));
    y[3] = (((x[11] ^ x[12]) ^ (x[0] ^ x[6])) ^ ((x[15] ^ x[5]) ^ (x[16] ^ x[1])));
    y[4] = ((x[12] ^ (x[17] ^ x[11])) ^ ((x[0] ^ x[6]) ^ (x[14] ^ (x[15] ^ x[5]))));
    y[5] = ((x[13] ^ (x[4] ^ x[8])) ^~ ((x[10] ^ (x[14] ^ x[16])) ^ (x[2] ^ x[11])));
    y[6] = ((x[6] ^ (x[11] ^ x[12])) ^~ ((x[14] ^ (x[15] ^ x[5])) ^ (x[2] ^ x[3])));
    y[7] = ((x[12] ^ (x[17] ^ x[11])) ^ ((x[5] ^ (x[0] ^ x[6])) ^ (x[2] ^ x[3])));
    return y;
  endfunction
  // AES Sbox Inverse Top Layer
  function automatic logic [20:0] aes_sbox_inv_top(input logic [7:0] x);
    return {
      ((x[4] ^ x[3]) ^ (x[2] ^~ x[1])),
      (x[5] ^~ (x[4] ^ x[3])),
      (x[3] ^~ x[0]),
      (x[7] ^ x[4]),
      (x[6] ^~ x[4]),
      ((x[3] ^~ x[0]) ^ (x[6] ^ x[1])),
      ((x[6] ^~ x[4]) ^ (x[1] ^ x[0])),
      (x[5] ^~ ((x[6] ^~ x[4]) ^ (x[1] ^ x[0]))),
      ((x[6] ^ x[1]) ^ (x[5] ^~ x[3])),
      (((x[7] ^~ x[6]) ^ (x[3] ^~ x[0])) ^ ((x[4] ^ x[3]) ^ (x[2] ^~ x[1]))),
      (((x[7] ^~ x[6]) ^ (x[3] ^~ x[0])) ^ (x[2] ^~ x[1])),
      ((x[7] ^~ x[6]) ^ (x[1] ^ x[0])),
      ((x[7] ^~ x[6]) ^ (x[3] ^~ x[0])),
      (x[0] ^~ (x[4] ^ x[3])),
      (x[6] ^~ (x[7] ^ x[4])),
      ((x[6] ^~ x[4]) ^ (x[5] ^~ x[2])),
      (x[3] ^ (x[6] ^~ (x[7] ^ x[4]))),
      ((x[4] ^ x[3]) ^ (x[1] ^ x[0])),
      (x[7] ^~ x[6]),
      (x[4] ^ x[3]),
      (x[7] ^ (x[5] ^~ x[2]))
    };
  endfunction
  // AES Sbox Inverse Bottom Layer
  function automatic logic [7:0] aes_sbox_inv_out(input logic [17:0] x);
    logic [7:0] y;
    y[0] = ((x[5] ^ x[13]) ^ (x[7] ^ x[11]));
    y[1] = ((x[17] ^ x[12]) ^ (((x[2] ^ x[11]) ^ (x[8] ^ x[9])) ^ (x[0] ^ x[3])));
    y[2] = (((x[4] ^ x[12]) ^ (x[15] ^ x[0])) ^ ((x[14] ^ x[1]) ^ ((x[2] ^ x[11]) ^ (x[8] ^ x[9]))));
    y[3] = ((((x[2] ^ x[11]) ^ (x[8] ^ x[9])) ^ (x[0] ^ x[3])) ^ ((x[7] ^ (x[16] ^ x[6])) ^ (x[13] ^ (x[14] ^ x[1]))));
    y[4] = ((x[14] ^ x[16]) ^ ((x[4] ^ x[12]) ^ ((x[2] ^ x[11]) ^ (x[8] ^ x[9]))));
    y[5] = ((x[8] ^ (x[4] ^ x[12])) ^ (((x[2] ^ x[11]) ^ (x[15] ^ x[0])) ^ ((x[17] ^ x[10]) ^ (x[7] ^ (x[16] ^ x[6])))));
    y[6] = (((x[5] ^ x[13]) ^ ((x[2] ^ x[11]) ^ (x[15] ^ x[0]))) ^ ((x[4] ^ x[9]) ^ ((x[16] ^ x[6]) ^ (x[17] ^ x[10]))));
    y[7] = ((x[17] ^ x[1]) ^ ((x[4] ^ x[12]) ^ ((x[2] ^ x[11]) ^ (x[8] ^ x[9]))));
    return y;
  endfunction

endpackage
