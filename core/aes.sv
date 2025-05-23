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
module aes
  import ariane_pkg::*;
  import aes_pkg::*;
#(
    parameter config_pkg::cva6_cfg_t CVA6Cfg = config_pkg::cva6_cfg_empty,
    parameter type fu_data_t = logic
) (
    // Subsystem Clock - SUBSYSTEM
    input  logic                        clk_i,
    // Asynchronous reset active low - SUBSYSTEM
    input  logic                        rst_ni,
    // FU data needed to execute instruction - ISSUE_STAGE
    input  fu_data_t                    fu_data_i,
    // Original instruction bits for aes
    input  logic     [             5:0] orig_instr_aes,
    // AES result - ISSUE_STAGE
    output logic     [CVA6Cfg.XLEN-1:0] result_o
);

  logic [63:0] sr;
  logic [ 7:0] sbox_in;
  logic [31:0] aes32esi_gen;
  logic [31:0] aes32esmi_gen;
  logic [63:0] aes64es_gen;
  logic [63:0] aes64esm_gen;
  logic [31:0] aes32dsi_gen;
  logic [31:0] aes32dsmi_gen;
  logic [63:0] sr_inv;
  logic [63:0] aes64ds_gen;
  logic [63:0] aes64dsm_gen;
  logic [63:0] aes64im_gen;
  logic [63:0] aes64ks1i_gen;
  logic [63:0] aes64ks2_gen;

  logic [31:0] sha256sig0_gen;
  logic [31:0] sha256sig1_gen;
  logic [31:0] sha256sum0_gen;
  logic [31:0] sha256sum1_gen;

  logic [31:0] sha512sig0h_gen;
  logic [31:0] sha512sig0l_gen;
  logic [31:0] sha512sig1h_gen;
  logic [31:0] sha512sig1l_gen;
  logic [31:0] sha512sum0r_gen;
  logic [31:0] sha512sum1r_gen;

  logic [63:0] sha512sig0_gen;
  logic [63:0] sha512sig1_gen;
  logic [63:0] sha512sum0_gen;
  logic [63:0] sha512sum1_gen;

  // AES gen block
  if (CVA6Cfg.ZKN && CVA6Cfg.RVB) begin : aes_gen_block
    // SHA256 sigma0 transformation function by rotating, shifting and XORing rs1
    assign sha256sig0_gen = (fu_data_i.operand_a[31:0] >> 7 | fu_data_i.operand_a[31:0] << 25) ^ (fu_data_i.operand_a[31:0] >> 18 | fu_data_i.operand_a[31:0] << 14) ^ (fu_data_i.operand_a[31:0] >> 3);
    // SHA256 sigma1 transformation function by rotating, shifting and XORing rs1
    assign sha256sig1_gen = (fu_data_i.operand_a[31:0] >> 17 | fu_data_i.operand_a[31:0] << 15) ^ (fu_data_i.operand_a[31:0] >> 19 | fu_data_i.operand_a[31:0] << 13) ^ (fu_data_i.operand_a[31:0] >> 10);
    // SHA256 sum0 transformation function by rotating, shifting and XORing rs1
    assign sha256sum0_gen = (fu_data_i.operand_a[31:0] >> 2 | fu_data_i.operand_a[31:0] << 30) ^ (fu_data_i.operand_a[31:0] >> 13 | fu_data_i.operand_a[31:0] << 19) ^ (fu_data_i.operand_a[31:0] >> 22 | fu_data_i.operand_a[31:0] << 10);
    // SHA256 sum1 transformation function by rotating, shifting and XORing rs1
    assign sha256sum1_gen = (fu_data_i.operand_a[31:0] >> 6 | fu_data_i.operand_a[31:0] << 26) ^ (fu_data_i.operand_a[31:0] >> 11 | fu_data_i.operand_a[31:0] << 21) ^ (fu_data_i.operand_a[31:0] >> 25 | fu_data_i.operand_a[31:0] << 7);
    if (CVA6Cfg.IS_XLEN32) begin
      assign sbox_in = fu_data_i.operand_b >> {orig_instr_aes[5:4], 3'b000};
      // AES 32-bit final round encryption by applying rotations and the forward sbox to a single byte of rs2 based on the MSB byte of the instruction itself  
      assign aes32esi_gen = (fu_data_i.operand_a ^ ({24'b0, aes_sbox_fwd(
          sbox_in[7:0]
      )} << {orig_instr_aes[5:4], 3'b000}) | ({24'b0, aes_sbox_fwd(
          sbox_in[7:0]
      )} >> (32 - {orig_instr_aes[5:4], 3'b000})));
      // AES 32-bit middle round encryption by applying rotations, forward mix-columns and the forward sbox to a single byte of rs2 based on the MSB byte of the instruction itself
      assign aes32esmi_gen = fu_data_i.operand_a ^ ((aes_mixcolumn_fwd(
          {24'h000000, aes_sbox_fwd(sbox_in[7:0])}
      ) << {orig_instr_aes[5:4], 3'b000}) | (aes_mixcolumn_fwd(
          {24'h000000, aes_sbox_fwd(sbox_in[7:0])}
      ) >> (32 - {orig_instr_aes[5:4], 3'b000})));
      // AES 32-bit final round decryption by applying rotations and the inverse sbox to a single byte of rs2 based on the MSB byte of the instruction itself
      assign aes32dsi_gen = (fu_data_i.operand_a ^ ({24'b0, aes_sbox_inv(
          sbox_in[7:0]
      )} << {orig_instr_aes[5:4], 3'b000}) | ({24'b0, aes_sbox_inv(
          sbox_in[7:0]
      )} >> (32 - {orig_instr_aes[5:4], 3'b000})));
      // AES 32-bit middle round decryption by applying rotations, inverse mix-columns and the inverse sbox to a single byte of rs2 based on the MSB byte of the instruction itself
      assign aes32dsmi_gen = fu_data_i.operand_a ^ ((aes_mixcolumn_inv(
          {24'h000000, aes_sbox_inv(sbox_in[7:0])}
      ) << {orig_instr_aes[5:4], 3'b000}) | (aes_mixcolumn_inv(
          {24'h000000, aes_sbox_inv(sbox_in[7:0])}
      ) >> (32 - {orig_instr_aes[5:4], 3'b000})));
      // SHA512 32-bit shifting and XORing rs1 and rs2
      assign sha512sig0h_gen = (fu_data_i.operand_a >> 1) ^ (fu_data_i.operand_a >> 7) ^ (fu_data_i.operand_a >> 8) ^ (fu_data_i.operand_b << 31) ^ (fu_data_i.operand_b << 24);
      assign sha512sig0l_gen = (fu_data_i.operand_a >> 1) ^ (fu_data_i.operand_a >> 7) ^ (fu_data_i.operand_a >> 8) ^ (fu_data_i.operand_b << 31) ^ (fu_data_i.operand_b << 25) ^ (fu_data_i.operand_b << 24);
      assign sha512sig1h_gen = (fu_data_i.operand_a << 3) ^ (fu_data_i.operand_a >> 6) ^ (fu_data_i.operand_a >> 19) ^ (fu_data_i.operand_b >> 29) ^ (fu_data_i.operand_b << 13);
      assign sha512sig1l_gen = (fu_data_i.operand_a << 3) ^ (fu_data_i.operand_a >> 6) ^ (fu_data_i.operand_a >> 19) ^ (fu_data_i.operand_b >> 29) ^ (fu_data_i.operand_b << 26) ^ (fu_data_i.operand_b << 13);
      assign sha512sum0r_gen = (fu_data_i.operand_a << 25) ^ (fu_data_i.operand_a << 30) ^ (fu_data_i.operand_a >> 28) ^ (fu_data_i.operand_b >> 7) ^ (fu_data_i.operand_b >> 2) ^ (fu_data_i.operand_b << 4);
      assign sha512sum1r_gen = (fu_data_i.operand_a << 23) ^ (fu_data_i.operand_a >> 14) ^ (fu_data_i.operand_a >> 18) ^ (fu_data_i.operand_b >> 9) ^ (fu_data_i.operand_b << 18) ^ (fu_data_i.operand_b << 14);
    end else if (CVA6Cfg.IS_XLEN64) begin
      // AES Shift rows forward and inverse step
      assign sr = {
        fu_data_i.operand_a[31:24],
        fu_data_i.operand_b[55:48],
        fu_data_i.operand_b[15:8],
        fu_data_i.operand_a[39:32],
        fu_data_i.operand_b[63:56],
        fu_data_i.operand_b[23:16],
        fu_data_i.operand_a[47:40],
        fu_data_i.operand_a[7:0]
      };
      assign sr_inv = {
        fu_data_i.operand_b[31:24],
        fu_data_i.operand_b[55:48],
        fu_data_i.operand_a[15:8],
        fu_data_i.operand_a[39:32],
        fu_data_i.operand_a[63:56],
        fu_data_i.operand_b[23:16],
        fu_data_i.operand_b[47:40],
        fu_data_i.operand_a[7:0]
      };
      // AES 64-bit final round encryption by applying forward shift-rows and the forward sbox to each byte
      assign aes64es_gen = {
        aes_sbox_fwd(sr[63:56]),
        aes_sbox_fwd(sr[55:48]),
        aes_sbox_fwd(sr[47:40]),
        aes_sbox_fwd(sr[39:32]),
        aes_sbox_fwd(sr[31:24]),
        aes_sbox_fwd(sr[23:16]),
        aes_sbox_fwd(sr[15:8]),
        aes_sbox_fwd(sr[7:0])
      };
      // AES 64-bit middle round encryption by applying forward shift-rows, forward sbox and forward mix-columns to all bytes
      assign aes64esm_gen = {
        aes_mixcolumn_fwd(aes64es_gen[63:32]), aes_mixcolumn_fwd(aes64es_gen[31:0])
      };
      // AES 64-bit final round decryption by applying inverse shift-rows and the inverse sbox to each byte
      assign aes64ds_gen = {
        aes_sbox_inv(sr_inv[63:56]),
        aes_sbox_inv(sr_inv[55:48]),
        aes_sbox_inv(sr_inv[47:40]),
        aes_sbox_inv(sr_inv[39:32]),
        aes_sbox_inv(sr_inv[31:24]),
        aes_sbox_inv(sr_inv[23:16]),
        aes_sbox_inv(sr_inv[15:8]),
        aes_sbox_inv(sr_inv[7:0])
      };
      // AES 64-bit middle round decryption by applying inverse shift-rows, inverse sbox and inverse mix-columns to all bytes
      assign aes64dsm_gen = {
        aes_mixcolumn_inv(aes64ds_gen[63:32]), aes_mixcolumn_inv(aes64ds_gen[31:0])
      };
      // AES 64-bit keySchedule decryption by applying inverse mix-columns on rs1 
      assign aes64im_gen = {
        aes_mixcolumn_inv(fu_data_i.operand_a[63:32]), aes_mixcolumn_inv(fu_data_i.operand_a[31:0])
      };
      // AES Key Schedule part by XORing different slices of rs1 and rs2 
      assign aes64ks2_gen = {
        (fu_data_i.operand_a[63:32] ^ fu_data_i.operand_b[31:0] ^ fu_data_i.operand_b[63:32]),
        (fu_data_i.operand_a[63:32] ^ fu_data_i.operand_b[31:0])
      };
      // AES Key Schedule part by substituting round constant based on round number(from instruction), rotations and forward subword substitutions
      assign aes64ks1i_gen = (orig_instr_aes[3:0] <= 4'hA) ? {((aes_subword_fwd(
          (orig_instr_aes[3:0] == 4'hA) ? fu_data_i.operand_a[63:32] : ((fu_data_i.operand_a[63:32] >> 8) | (fu_data_i.operand_a[63:32] << 24))
      )) ^ (aes_decode_rcon(
          orig_instr_aes[3:0]
      ))), ((aes_subword_fwd(
          (orig_instr_aes[3:0] == 4'hA) ? fu_data_i.operand_a[63:32] : ((fu_data_i.operand_a[63:32] >> 8) | (fu_data_i.operand_a[63:32] << 24))
      )) ^ (aes_decode_rcon(
          orig_instr_aes[3:0]
      )))} : 64'h0;
      // SHA512 64bit rotating, shifting and XORing rs1
      assign sha512sig0_gen = (fu_data_i.operand_a >> 1 | fu_data_i.operand_a << 63) ^ (fu_data_i.operand_a >> 8 | fu_data_i.operand_a << 56) ^ (fu_data_i.operand_a >> 7);
      assign sha512sig1_gen = (fu_data_i.operand_a >> 19 | fu_data_i.operand_a << 45) ^ (fu_data_i.operand_a >> 61 | fu_data_i.operand_a << 3) ^ (fu_data_i.operand_a >> 6);
      assign sha512sum0_gen = (fu_data_i.operand_a >> 28 | fu_data_i.operand_a << 36) ^ (fu_data_i.operand_a >> 34 | fu_data_i.operand_a << 30) ^ (fu_data_i.operand_a >> 39 | fu_data_i.operand_a << 25);
      assign sha512sum1_gen = (fu_data_i.operand_a >> 14 | fu_data_i.operand_a << 50) ^ (fu_data_i.operand_a >> 18 | fu_data_i.operand_a << 46) ^ (fu_data_i.operand_a >> 41 | fu_data_i.operand_a << 23);
    end
  end

  // -----------
  // Result MUX
  // -----------
  always_comb begin
    result_o = '0;
    // AES instructions
    if (CVA6Cfg.ZKN && CVA6Cfg.RVB) begin
      if (CVA6Cfg.IS_XLEN32) begin
        unique case (fu_data_i.operation)
          AES32ESI: result_o = aes32esi_gen;
          AES32ESMI: result_o = aes32esmi_gen;
          AES32DSI: result_o = aes32dsi_gen;
          AES32DSMI: result_o = aes32dsmi_gen;
          SHA256SIG0: result_o = sha256sig0_gen;
          SHA256SIG1: result_o = sha256sig1_gen;
          SHA256SUM0: result_o = sha256sum0_gen;
          SHA256SUM1: result_o = sha256sum1_gen;
          SHA512SIG0H: result_o = sha512sig0h_gen;
          SHA512SIG0L: result_o = sha512sig0l_gen;
          SHA512SIG1H: result_o = sha512sig1h_gen;
          SHA512SIG1L: result_o = sha512sig1l_gen;
          SHA512SUM0R: result_o = sha512sum0r_gen;
          SHA512SUM1R: result_o = sha512sum1r_gen;
          default: ;
        endcase
      end
      if (CVA6Cfg.IS_XLEN64) begin
        unique case (fu_data_i.operation)
          AES64ES: result_o = aes64es_gen;
          AES64ESM: result_o = aes64esm_gen;
          AES64DS: result_o = aes64ds_gen;
          AES64DSM: result_o = aes64dsm_gen;
          AES64IM: result_o = aes64im_gen;
          AES64KS1I: result_o = aes64ks1i_gen;
          AES64KS2: result_o = aes64ks2_gen;
          SHA256SIG0: result_o = {{32{sha256sig0_gen[31]}}, sha256sig0_gen};
          SHA256SIG1: result_o = {{32{sha256sig1_gen[31]}}, sha256sig1_gen};
          SHA256SUM0: result_o = {{32{sha256sum0_gen[31]}}, sha256sum0_gen};
          SHA256SUM1: result_o = {{32{sha256sum1_gen[31]}}, sha256sum1_gen};
          SHA512SIG0: result_o = sha512sig0_gen;
          SHA512SIG1: result_o = sha512sig1_gen;
          SHA512SUM0: result_o = sha512sum0_gen;
          SHA512SUM1: result_o = sha512sum1_gen;
          default: ;
        endcase
      end
    end
  end
endmodule
