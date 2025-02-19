module aes_fu
  import ariane_pkg::*;
#(
    parameter config_pkg::cva6_cfg_t CVA6Cfg = config_pkg::cva6_cfg_empty,
    parameter type fu_data_t = logic
) (
    // Subsystem Clock - SUBSYSTEM
    input  logic                                 clk_i,
    // Asynchronous reset active low - SUBSYSTEM
    input  logic                                 rst_ni,
    // FU data needed to execute instruction - ISSUE_STAGE
    input  fu_data_t                             fu_data_i,
    // Original instruction bits for aes
    input  logic [                          5:0] orig_instr_aes,
    // Crypto result - ISSUE_STAGE
    output logic     [         CVA6Cfg.XLEN-1:0] result_o
);
  logic aes_valid_op;

  // ---------------------
  // Input
  // ---------------------

  assign aes_valid_op = fu_data_i.operation inside { AES32ESI, AES32ESMI, AES64ES, AES64ESM, AES32DSI, AES32DSMI, AES64DS, AES64DSM, AES64IM, AES64KS1I, AES64KS2 };


  logic [            63:0] sr;
  logic [            31:0] aes32esi_gen;
  logic [            31:0] aes32esmi_gen;
  logic [            63:0] aes64es_gen;
  logic [            63:0] aes64esm_gen;
  logic [            31:0] aes32dsi_gen;
  logic [            31:0] aes32dsmi_gen;
  logic [            63:0] sr_inv;
  logic [            63:0] aes64ds_gen;
  logic [            63:0] aes64dsm_gen;
  logic [            63:0] aes64im_gen;
  logic [            63:0] aes64ks1i_gen;
  logic [            63:0] aes64ks2_gen;
  
  // AES gen block
  if (CVA6Cfg.ZKN && CVA6Cfg.RVB) begin : aes_gen_block
    if (CVA6Cfg.IS_XLEN32) begin
        // AES 32-bit final round encryption by applying rotations and the forward sbox to a single byte of rs2 based on the MSB byte of the instruction itself  
        assign aes32esi_gen = (fu_data_i.operand_a ^ ({24'b0, aes_sbox_fwd((fu_data_i.operand_b >> {orig_instr_aes[5:4], 3'b000}[7:0]))} << {orig_instr_aes[5:4], 3'b000}) | ({24'b0, aes_sbox_fwd((fu_data_i.operand_b >> {orig_instr_aes[5:4], 3'b000}[7:0]))} >> (32 - {orig_instr_aes[5:4], 3'b000})));
        // AES 32-bit middle round encryption by applying rotations, forward mix-columns and the forward sbox to a single byte of rs2 based on the MSB byte of the instruction itself
        assign aes32esmi_gen = fu_data_i.operand_a ^ ((aes_mixcolumn_fwd({24'h000000, aes_sbox_fwd((fu_data_i.operand_b >> {orig_instr_aes[5:4], 3'b000}[7:0]))}) << {orig_instr_aes[5:4], 3'b000}) | (aes_mixcolumn_fwd({24'h000000, aes_sbox_fwd((fu_data_i.operand_b >> {orig_instr_aes[5:4], 3'b000}[7:0]))}) >> (32 - {orig_instr_aes[5:4], 3'b000})));
        // AES 32-bit final round decryption by applying rotations and the inverse sbox to a single byte of rs2 based on the MSB byte of the instruction itself
        assign aes32dsi_gen = (fu_data_i.operand_a ^ ({24'b0, aes_sbox_inv((fu_data_i.operand_b >> {orig_instr_aes[5:4], 3'b000}[7:0]))} << {orig_instr_aes[5:4], 3'b000}) | ({24'b0, aes_sbox_inv((fu_data_i.operand_b >> {orig_instr_aes[5:4], 3'b000}[7:0]))} >> (32 - {orig_instr_aes[5:4], 3'b000})));
        // AES 32-bit middle round decryption by applying rotations, inverse mix-columns and the inverse sbox to a single byte of rs2 based on the MSB byte of the instruction itself
        assign aes32dsmi_gen = fu_data_i.operand_a ^ ((aes_mixcolumn_inv({24'h000000, aes_sbox_inv((fu_data_i.operand_b >> {orig_instr_aes[5:4], 3'b000}[7:0]))}) << {orig_instr_aes[5:4], 3'b000}) | (aes_mixcolumn_inv({24'h000000, aes_sbox_inv((fu_data_i.operand_b >> {orig_instr_aes[5:4], 3'b000}[7:0]))}) >> (32 - {orig_instr_aes[5:4], 3'b000})));
    end
    else if (CVA6Cfg.IS_XLEN64) begin
      // AES Shift rows forward and inverse step
      assign sr = {fu_data_i.operand_a[31:24], fu_data_i.operand_b[55:48], fu_data_i.operand_b[15:8], fu_data_i.operand_a[39:32], fu_data_i.operand_b[63:56], fu_data_i.operand_b[23:16], fu_data_i.operand_a[47:40], fu_data_i.operand_a[7:0]};
      assign sr_inv = {fu_data_i.operand_b[31:24], fu_data_i.operand_b[55:48], fu_data_i.operand_a[15:8], fu_data_i.operand_a[39:32], fu_data_i.operand_a[63:56], fu_data_i.operand_b[23:16], fu_data_i.operand_b[47:40], fu_data_i.operand_a[7:0]};
      // AES 64-bit final round encryption by applying forward shift-rows and the forward sbox to each byte
      assign aes64es_gen = {aes_sbox_fwd(sr[63:56]), aes_sbox_fwd(sr[55:48]), aes_sbox_fwd(sr[47:40]), aes_sbox_fwd(sr[39:32]), aes_sbox_fwd(sr[31:24]), aes_sbox_fwd(sr[23:16]), aes_sbox_fwd(sr[15:8]),  aes_sbox_fwd(sr[7:0])};
      // AES 64-bit middle round encryption by applying forward shift-rows, forward sbox and forward mix-columns to all bytes
      assign aes64esm_gen = {aes_mixcolumn_fwd(aes64es_gen[63:32]), aes_mixcolumn_fwd(aes64es_gen[31:0])};
      // AES 64-bit final round decryption by applying inverse shift-rows and the inverse sbox to each byte
      assign aes64ds_gen = {aes_sbox_inv(sr_inv[63:56]), aes_sbox_inv(sr_inv[55:48]), aes_sbox_inv(sr_inv[47:40]), aes_sbox_inv(sr_inv[39:32]), aes_sbox_inv(sr_inv[31:24]), aes_sbox_inv(sr_inv[23:16]), aes_sbox_inv(sr_inv[15:8]),  aes_sbox_inv(sr_inv[7:0])};
      // AES 64-bit middle round decryption by applying inverse shift-rows, inverse sbox and inverse mix-columns to all bytes
      assign aes64dsm_gen = {aes_mixcolumn_inv(aes64ds_gen[63:32]), aes_mixcolumn_inv(aes64ds_gen[31:0])};
      // AES 64-bit keySchedule decryption by applying inverse mix-columns on rs1 
      assign aes64im_gen = {aes_mixcolumn_inv(fu_data_i.operand_a[63:32]), aes_mixcolumn_inv(fu_data_i.operand_a[31:0])};
      // AES Key Schedule part by XORing different slices of rs1 and rs2 
      assign aes64ks2_gen = {(fu_data_i.operand_a[63:32] ^ fu_data_i.operand_b[31:0] ^ fu_data_i.operand_b[63:32]), (fu_data_i.operand_a[63:32] ^ fu_data_i.operand_b[31:0])};      
      // AES Key Schedule part by substituting round constant based on round number(from instruction), rotations and forward subword substitutions
      assign aes64ks1i_gen = (orig_instr_aes[3:0] <= 4'hA) ? {((aes_subword_fwd((orig_instr_aes[3:0] == 4'hA) ? fu_data_i.operand_a[63:32] : ((fu_data_i.operand_a[63:32] >> 8) | (fu_data_i.operand_a[63:32] << 24)))) ^ (aes_decode_rcon(orig_instr_aes[3:0]))), ((aes_subword_fwd((orig_instr_aes[3:0] == 4'hA) ? fu_data_i.operand_a[63:32] : ((fu_data_i.operand_a[63:32] >> 8) | (fu_data_i.operand_a[63:32] << 24)))) ^ (aes_decode_rcon(orig_instr_aes[3:0])))} : 64'h0;
    end
  end

  // -----------
  // Result MUX
  // -----------
  always_comb begin
    result_o = '0;
    // AES instructions
    if (CVA6Cfg.ZKN && CVA6Cfg.RVB) begin
      if (fu_data_i.operation == AES32ESI && CVA6Cfg.IS_XLEN32) result_o = aes32esi_gen;
      if (fu_data_i.operation == AES32ESMI && CVA6Cfg.IS_XLEN32) result_o = aes32esmi_gen;
      if (fu_data_i.operation == AES64ES && CVA6Cfg.IS_XLEN64) result_o = aes64es_gen;
      if (fu_data_i.operation == AES64ESM && CVA6Cfg.IS_XLEN64) result_o = aes64esm_gen;
      if (fu_data_i.operation == AES32DSI && CVA6Cfg.IS_XLEN32) result_o = aes32dsi_gen;
      if (fu_data_i.operation == AES32DSMI && CVA6Cfg.IS_XLEN32) result_o = aes32dsmi_gen;
      if (fu_data_i.operation == AES64DS && CVA6Cfg.IS_XLEN64) result_o = aes64ds_gen;
      if (fu_data_i.operation == AES64DSM && CVA6Cfg.IS_XLEN64) result_o = aes64dsm_gen;
      if (fu_data_i.operation == AES64IM && CVA6Cfg.IS_XLEN64) result_o = aes64im_gen;
      if (fu_data_i.operation == AES64KS1I && CVA6Cfg.IS_XLEN64) result_o = aes64ks1i_gen;
      if (fu_data_i.operation == AES64KS2 && CVA6Cfg.IS_XLEN64) result_o = aes64ks2_gen;
    end
  end
endmodule
