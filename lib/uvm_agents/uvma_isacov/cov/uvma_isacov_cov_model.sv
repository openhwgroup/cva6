// Copyright 2021 OpenHW Group
// Copyright 2021 Silicon Labs, Inc.
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://solderpad.org/licenses/
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0

`ifdef UNSUPPORTED_WITH //TODO - Remove ifdef when the issue in VCS simulator is fixed
  `define WITH iff
`else
   `define WITH with
`endif

covergroup cg_executed_type(
    string name,
    instr_name_t instr_name
) with function sample (
    uvma_isacov_instr_c instr
);
  option.per_instance = 1;
  option.name = name;

  cp_executed: coverpoint instr.name {
    bins EXECUTED = {[0:$]};
  }

endgroup : cg_executed_type

// There isn't a defined instruction type/format (yet in Zbb)
// The 2-source register format is mapped to R=type (from I spec)
// The 1-source register format is encompassed here
covergroup cg_zb_rstype(
    string name,
    bit reg_crosses_enabled,
    bit reg_hazards_enabled,
    bit rs_is_signed,
    bit rd_is_signed
) with function sample (
    uvma_isacov_instr_c instr
);
  option.per_instance = 1;
  option.name = name;

  cp_rs: coverpoint instr.rs1;
  cp_rd: coverpoint instr.rd;

  cp_rd_rs_hazard: coverpoint instr.rd {
    ignore_bins IGN_RS_HAZARD_OFF = {[0:$]} `WITH (!reg_hazards_enabled);
    bins RD[] = {[0:31]} iff (instr.rd == instr.rs1);
  }

  cross_rd_rs: cross cp_rd, cp_rs {
    ignore_bins IGN_OFF = cross_rd_rs `WITH (!reg_crosses_enabled);
  }

  cp_rs_value: coverpoint instr.rs1_value_type {
    ignore_bins POS_OFF = {POSITIVE} `WITH (!rs_is_signed);
    ignore_bins NEG_OFF = {NEGATIVE} `WITH (!rs_is_signed);
    ignore_bins NON_ZERO_OFF = {NON_ZERO} `WITH (rs_is_signed);
  }

  cp_rd_value: coverpoint instr.rd_value_type {
    ignore_bins POS_OFF = {POSITIVE} `WITH (!rd_is_signed);
    ignore_bins NEG_OFF = {NEGATIVE} `WITH (!rd_is_signed);
    ignore_bins NON_ZERO_OFF = {NON_ZERO} `WITH (rd_is_signed);
  }

  `ISACOV_CP_BITWISE(cp_rs_toggle, instr.rs1_value, 1)
  `ISACOV_CP_BITWISE(cp_rd_toggle,  instr.rd_value,  1)

endgroup : cg_zb_rstype

covergroup cg_zb_itype_shift (
    string name,
    bit reg_crosses_enabled,
    bit reg_hazards_enabled,
    bit rs_is_signed,
    bit rd_is_signed
) with function sample (
    uvma_isacov_instr_c instr
);
  option.per_instance = 1;
  option.name = name;

  cp_rs: coverpoint instr.rs1;
  cp_rd: coverpoint instr.rd;

  cp_rd_rs_hazard: coverpoint instr.rd {
    ignore_bins IGN_RS1_HAZARD_OFF = {[0:$]} `WITH (!reg_hazards_enabled);
    bins RD[] = {[0:31]} iff (instr.rd == instr.rs1);
  }

  cross_rd_rs: cross cp_rd, cp_rs {
    ignore_bins IGN_OFF = cross_rd_rs `WITH (!reg_crosses_enabled);
  }

  cp_rs_value: coverpoint instr.rs1_value_type {
    ignore_bins POS_OFF = {POSITIVE} `WITH (!rs_is_signed);
    ignore_bins NEG_OFF = {NEGATIVE} `WITH (!rs_is_signed);
    ignore_bins NON_ZERO_OFF = {NON_ZERO} `WITH (rs_is_signed);
  }

  cp_shamt: coverpoint instr.immi {
    bins SHAMT[] = {[0:31]};
  }

  cp_rd_value: coverpoint instr.rd_value_type {
    ignore_bins POS_OFF = {POSITIVE} `WITH (!rd_is_signed);
    ignore_bins NEG_OFF = {NEGATIVE} `WITH (!rd_is_signed);
    ignore_bins NON_ZERO_OFF = {NON_ZERO} `WITH (rd_is_signed);
  }

  `ISACOV_CP_BITWISE(cp_rs_toggle,  instr.rs1_value, 1)
  `ISACOV_CP_BITWISE(cp_rd_toggle,  instr.rd_value,  1)

endgroup : cg_zb_itype_shift

covergroup cg_zb_rstype_ext(
    string name,
    bit reg_crosses_enabled,
    bit reg_hazards_enabled,
    bit rs1_is_signed,
    bit rs2_is_signed,
    bit rd_is_signed
) with function sample (
    uvma_isacov_instr_c instr
);
  option.per_instance = 1;
  option.name = name;

  cp_rs1: coverpoint instr.rs1;
  cp_rs2: coverpoint instr.rs2;
  cp_rd: coverpoint instr.rd;

  cp_rd_rs1_hazard: coverpoint instr.rd {
    ignore_bins IGN_RS1_HAZARD_OFF = {[0:$]} `WITH (!reg_hazards_enabled);
    bins RD[] = {[0:31]} iff (instr.rd == instr.rs1);
  }

  cp_rd_rs2_hazard: coverpoint instr.rd {
    ignore_bins IGN_RS1_HAZARD_OFF = {[0:$]} `WITH (!reg_hazards_enabled);
    bins RD[] = {[0:31]} iff (instr.rd == instr.rs2);
  }

  cross_rd_rs1_rs2: cross cp_rd, cp_rs1, cp_rs2 {
    ignore_bins IGN_OFF = cross_rd_rs1_rs2 `WITH (!reg_crosses_enabled);
  }

  cp_rs1_value: coverpoint instr.rs1_value_type {
    ignore_bins POS_OFF = {POSITIVE} `WITH (!rs1_is_signed);
    ignore_bins NEG_OFF = {NEGATIVE} `WITH (!rs1_is_signed);
    ignore_bins NON_ZERO_OFF = {NON_ZERO} `WITH (rs1_is_signed);
  }

  cp_index: coverpoint instr.rs2[4:0] {
    bins INDEX[] = {[0:31]};
  }

  cp_rd_value: coverpoint instr.rd_value {
    bins ZERO = {0};
    bins ONE  = {1};
  }

  `ISACOV_CP_BITWISE(cp_rs1_toggle,  instr.rs1_value, 1)
  `ISACOV_CP_BITWISE(cp_rs2_toggle,  instr.rs2_value, 1)

endgroup : cg_zb_rstype_ext

covergroup cg_zb_itype_ext(
    string name,
    bit reg_crosses_enabled,
    bit reg_hazards_enabled,
    bit rs_is_signed,
    bit rd_is_signed
) with function sample (
    uvma_isacov_instr_c instr
);
  option.per_instance = 1;
  option.name = name;

  cp_rs: coverpoint instr.rs1;
  cp_rd: coverpoint instr.rd;

  cp_rd_rs_hazard: coverpoint instr.rd {
    ignore_bins IGN_RS1_HAZARD_OFF = {[0:$]} `WITH (!reg_hazards_enabled);
    bins RD[] = {[0:31]} iff (instr.rd == instr.rs1);
  }

  cross_rd_rs: cross cp_rd, cp_rs {
    ignore_bins IGN_OFF = cross_rd_rs `WITH (!reg_crosses_enabled);
  }

  cp_rs_value: coverpoint instr.rs1_value_type {
    ignore_bins POS_OFF = {POSITIVE} `WITH (!rs_is_signed);
    ignore_bins NEG_OFF = {NEGATIVE} `WITH (!rs_is_signed);
    ignore_bins NON_ZERO_OFF = {NON_ZERO} `WITH (rs_is_signed);
  }

  cp_shift: coverpoint instr.immi {
    bins SHIFT[] = {[0:31]};
  }

  cp_rd_value: coverpoint instr.rd_value {
    bins ZERO = {0};
    bins ONE  = {1};
  }

  `ISACOV_CP_BITWISE(cp_rs_toggle,  instr.rs1_value, 1)

endgroup : cg_zb_itype_ext

covergroup cg_rtype(
    string name,
    bit reg_crosses_enabled,
    bit reg_hazards_enabled,
    bit rs1_is_signed,
    bit rs2_is_signed,
    bit rd_is_signed
) with function sample (
    uvma_isacov_instr_c instr
);
  option.per_instance = 1;
  option.name = name;

  cp_rs1: coverpoint instr.rs1;
  cp_rs2: coverpoint instr.rs2;
  cp_rd: coverpoint instr.rd;

  cp_rd_rs1_hazard: coverpoint instr.rd {
    ignore_bins IGN_RS1_HAZARD_OFF = {[0:$]} `WITH (!reg_hazards_enabled);
    bins RD[] = {[0:31]} iff (instr.rd == instr.rs1);
  }

  cp_rd_rs2_hazard: coverpoint instr.rd {
    ignore_bins IGN_RS2_HAZARD_OFF = {[0:$]} `WITH (!reg_hazards_enabled);
    bins RD[] = {[0:31]} iff (instr.rd == instr.rs2);
  }

  cross_rd_rs1_rs2: cross cp_rd, cp_rs1, cp_rs2 {
    ignore_bins IGN_OFF = cross_rd_rs1_rs2 `WITH (!reg_crosses_enabled);
  }

  cp_rs1_value: coverpoint instr.rs1_value_type {
    ignore_bins POS_OFF = {POSITIVE} `WITH (!rs1_is_signed);
    ignore_bins NEG_OFF = {NEGATIVE} `WITH (!rs1_is_signed);
    ignore_bins NON_ZERO_OFF = {NON_ZERO} `WITH (rs1_is_signed);
  }

  cp_rs2_value: coverpoint instr.rs2_value_type {
    ignore_bins POS_OFF = {POSITIVE} `WITH (!rs2_is_signed);
    ignore_bins NEG_OFF = {NEGATIVE} `WITH (!rs2_is_signed);
    ignore_bins NON_ZERO_OFF = {NON_ZERO} `WITH (rs2_is_signed);
  }

  cross_rs1_rs2_value: cross cp_rs1_value, cp_rs2_value;

  cp_rd_value: coverpoint instr.rd_value_type {
    ignore_bins POS_OFF = {POSITIVE} `WITH (!rd_is_signed);
    ignore_bins NEG_OFF = {NEGATIVE} `WITH (!rd_is_signed);
    ignore_bins NON_ZERO_OFF = {NON_ZERO} `WITH (rd_is_signed);
  }

  `ISACOV_CP_BITWISE(cp_rs1_toggle, instr.rs1_value, 1)
  `ISACOV_CP_BITWISE(cp_rs2_toggle, instr.rs2_value, 1)
  `ISACOV_CP_BITWISE(cp_rd_toggle,  instr.rd_value,  1)

endgroup : cg_rtype

covergroup cg_rtype_lr_w(
    string name,
    bit reg_hazards_enabled,
    bit rs1_is_signed,
    bit rd_is_signed,
    bit unaligned_access_amo_supported
) with function sample (
    uvma_isacov_instr_c instr
);
  option.per_instance = 1;
  option.name = name;

  cp_rs1: coverpoint instr.rs1;
  cp_rd: coverpoint instr.rd;

  cp_rd_rs1_hazard: coverpoint instr.rd {
    ignore_bins IGN_RS1_HAZARD_OFF = {[0:$]} `WITH (!reg_hazards_enabled);
    bins RD[] = {[0:31]} iff (instr.rd == instr.rs1);
  }

  cp_rs1_value: coverpoint instr.rs1_value_type {
    ignore_bins POS_OFF = {POSITIVE} `WITH (!rs1_is_signed);
    ignore_bins NEG_OFF = {NEGATIVE} `WITH (!rs1_is_signed);
    ignore_bins NON_ZERO_OFF = {NON_ZERO} `WITH (rs1_is_signed);
  }

  cp_rd_value: coverpoint instr.rd_value_type {
    ignore_bins POS_OFF = {POSITIVE} `WITH (!rd_is_signed);
    ignore_bins NEG_OFF = {NEGATIVE} `WITH (!rd_is_signed);
    ignore_bins NON_ZERO_OFF = {NON_ZERO} `WITH (rd_is_signed);
  }

  cp_align_word: coverpoint (instr.rvfi.mem_addr[1:0]) {
    ignore_bins IGN_OFF = {[0:$]} `WITH (!unaligned_access_amo_supported);
    bins ALIGNED     = {0};
    bins UNALIGNED[] = {[1:3]};
  }

  `ISACOV_CP_BITWISE(cp_rs1_toggle, instr.rs1_value, 1)
  `ISACOV_CP_BITWISE(cp_rd_toggle,  instr.rd_value,  1)

endgroup : cg_rtype_lr_w

covergroup cg_rtype_sc_w (
    string name,
    bit reg_crosses_enabled,
    bit reg_hazards_enabled,
    bit rs1_is_signed,
    bit rs2_is_signed,
    bit unaligned_access_amo_supported
) with function sample (
    uvma_isacov_instr_c instr
);
  option.per_instance = 1;
  option.name = name;

  cp_rs1: coverpoint instr.rs1;
  cp_rs2: coverpoint instr.rs2;
  cp_rd: coverpoint instr.rd;

  cp_rd_rs1_hazard: coverpoint instr.rd {
    ignore_bins IGN_RS1_HAZARD_OFF = {[0:$]} `WITH (!reg_hazards_enabled);
    bins RD[] = {[0:31]} iff (instr.rd == instr.rs1);
  }

  cp_rd_rs2_hazard: coverpoint instr.rd {
    ignore_bins IGN_RS2_HAZARD_OFF = {[0:$]} `WITH (!reg_hazards_enabled);
    bins RD[] = {[0:31]} iff (instr.rd == instr.rs2);
  }

  cross_rd_rs1_rs2: cross cp_rd, cp_rs1, cp_rs2 {
    ignore_bins IGN_OFF = cross_rd_rs1_rs2 `WITH (!reg_crosses_enabled);
  }

  cp_rs1_value: coverpoint instr.rs1_value_type {
    ignore_bins POS_OFF = {POSITIVE} `WITH (!rs1_is_signed);
    ignore_bins NEG_OFF = {NEGATIVE} `WITH (!rs1_is_signed);
    ignore_bins NON_ZERO_OFF = {NON_ZERO} `WITH (rs1_is_signed);
  }

  cp_rs2_value: coverpoint instr.rs2_value_type {
    ignore_bins POS_OFF = {POSITIVE} `WITH (!rs2_is_signed);
    ignore_bins NEG_OFF = {NEGATIVE} `WITH (!rs2_is_signed);
    ignore_bins NON_ZERO_OFF = {NON_ZERO} `WITH (rs2_is_signed);
  }

  cross_rs1_rs2_value: cross cp_rs1_value, cp_rs2_value;

  cp_align_word: coverpoint (instr.rvfi.mem_addr[1:0]) {
    ignore_bins IGN_OFF = {[0:$]} `WITH (!unaligned_access_amo_supported);
    bins ALIGNED     = {0};
    bins UNALIGNED[] = {[1:3]};
  }

  `ISACOV_CP_BITWISE(cp_rs1_toggle, instr.rs1_value, 1)
  `ISACOV_CP_BITWISE(cp_rs2_toggle, instr.rs2_value, 1)
  `ISACOV_CP_BITWISE_0_0(cp_rd_toggle, instr.rd_value,  1)

endgroup : cg_rtype_sc_w


covergroup cg_rtype_amo (
    string name,
    bit reg_crosses_enabled,
    bit reg_hazards_enabled,
    bit rs1_is_signed,
    bit rd_is_signed,
    bit unaligned_access_amo_supported
) with function sample (
    uvma_isacov_instr_c instr
);
  option.per_instance = 1;
  option.name = name;

  cp_rs1: coverpoint instr.rs1;
  cp_rs2: coverpoint instr.rs2;
  cp_rd: coverpoint instr.rd;

  cp_rd_rs1_hazard: coverpoint instr.rd {
    ignore_bins IGN_RS1_HAZARD_OFF = {[0:$]} `WITH (!reg_hazards_enabled);
    bins RD[] = {[0:31]} iff (instr.rd == instr.rs1);
  }

  cp_rd_rs2_hazard: coverpoint instr.rd {
    ignore_bins IGN_RS2_HAZARD_OFF = {[0:$]} `WITH (!reg_hazards_enabled);
    bins RD[] = {[0:31]} iff (instr.rd == instr.rs2);
  }

  cross_rd_rs1_rs2: cross cp_rd, cp_rs1, cp_rs2 {
    ignore_bins IGN_OFF = cross_rd_rs1_rs2 `WITH (!reg_crosses_enabled);
  }

  cp_rs1_value: coverpoint instr.rs1_value_type {
    ignore_bins POS_OFF = {POSITIVE} `WITH (!rs1_is_signed);
    ignore_bins NEG_OFF = {NEGATIVE} `WITH (!rs1_is_signed);
    ignore_bins NON_ZERO_OFF = {NON_ZERO} `WITH (rs1_is_signed);
  }

  cp_align_word: coverpoint (instr.rvfi.mem_addr[1:0]) {
    ignore_bins IGN_OFF = {[0:$]} `WITH (!unaligned_access_amo_supported);
    bins ALIGNED     = {0};
    bins UNALIGNED[] = {[1:3]};
  }

  `ISACOV_CP_BITWISE(cp_rs1_toggle, instr.rs1_value, 1)
  `ISACOV_CP_BITWISE(cp_rs2_toggle, instr.rs2_value, 1)
  `ISACOV_CP_BITWISE(cp_rd_toggle,  instr.rd_value,  1)

endgroup : cg_rtype_amo

covergroup cg_rtype_slt(
    string name,
    bit reg_crosses_enabled,
    bit reg_hazards_enabled,
    bit rs1_is_signed,
    bit rs2_is_signed,
    bit rd_is_signed
) with function sample (
    uvma_isacov_instr_c instr
);
  option.per_instance = 1;
  option.name = name;

  cp_rs1: coverpoint instr.rs1;
  cp_rs2: coverpoint instr.rs2;
  cp_rd: coverpoint instr.rd;

  cp_rd_rs1_hazard: coverpoint instr.rd {
    ignore_bins IGN_RS1_HAZARD_OFF = {[0:$]} `WITH (!reg_hazards_enabled);
    bins RD[] = {[0:31]} iff (instr.rd == instr.rs1);
  }

  cp_rd_rs2_hazard: coverpoint instr.rd {
    ignore_bins IGN_RS2_HAZARD_OFF = {[0:$]} `WITH (!reg_hazards_enabled);
    bins RD[] = {[0:31]} iff (instr.rd == instr.rs2);
  }

  cross_rd_rs1_rs2: cross cp_rd, cp_rs1, cp_rs2 {
    ignore_bins IGN_OFF = cross_rd_rs1_rs2 `WITH (!reg_crosses_enabled);
  }

  cp_rs1_value: coverpoint instr.rs1_value_type {
    ignore_bins POS_OFF = {POSITIVE} `WITH (!rs1_is_signed);
    ignore_bins NEG_OFF = {NEGATIVE} `WITH (!rs1_is_signed);
    ignore_bins NON_ZERO_OFF = {NON_ZERO} `WITH (rs1_is_signed);
  }

  cp_rs2_value: coverpoint instr.rs2_value_type {
    ignore_bins POS_OFF = {POSITIVE} `WITH (!rs2_is_signed);
    ignore_bins NEG_OFF = {NEGATIVE} `WITH (!rs2_is_signed);
    ignore_bins NON_ZERO_OFF = {NON_ZERO} `WITH (rs2_is_signed);
  }

  cross_rs1_rs2_value: cross cp_rs1_value, cp_rs2_value;

  cp_rd_value: coverpoint instr.rd_value {
    bins SLT[] = {[0:1]};
  }

  `ISACOV_CP_BITWISE(cp_rs1_toggle, instr.rs1_value, 1)
  `ISACOV_CP_BITWISE(cp_rs2_toggle, instr.rs2_value, 1)

endgroup : cg_rtype_slt

covergroup cg_rtype_shift (
    string name,
    bit reg_crosses_enabled,
    bit reg_hazards_enabled,
    bit rs1_is_signed,
    bit rs2_is_signed,
    bit rd_is_signed
) with function sample (
    uvma_isacov_instr_c instr
);
  option.per_instance = 1;
  option.name = name;

  cp_rs1: coverpoint instr.rs1;
  cp_rs2: coverpoint instr.rs2;
  cp_rd: coverpoint instr.rd;

  cp_rd_rs1_hazard: coverpoint instr.rd {
    ignore_bins IGN_RS1_HAZARD_OFF = {[0:$]} `WITH (!reg_hazards_enabled);
    bins RD[] = {[0:31]} iff (instr.rd == instr.rs1);
  }

  cp_rd_rs2_hazard: coverpoint instr.rd {
    ignore_bins IGN_RS2_HAZARD_OFF = {[0:$]} `WITH (!reg_hazards_enabled);
    bins RD[] = {[0:31]} iff (instr.rd == instr.rs2);
  }

  cross_rd_rs1_rs2: cross cp_rd, cp_rs1, cp_rs2 {
    ignore_bins IGN_OFF = cross_rd_rs1_rs2 `WITH (!reg_crosses_enabled);
  }

  cp_rs1_value: coverpoint instr.rs1_value_type {
    ignore_bins POS_OFF = {POSITIVE} `WITH (!rs1_is_signed);
    ignore_bins NEG_OFF = {NEGATIVE} `WITH (!rs1_is_signed);
    ignore_bins NON_ZERO_OFF = {NON_ZERO} `WITH (rs1_is_signed);
  }

  cp_rs2_value: coverpoint (instr.rs2_value[4:0]) {
    bins SHAMT[] = {[0:31]};
  }

  cross_rs1_rs2_value: cross cp_rs1_value, cp_rs2_value;

  cp_rd_value: coverpoint instr.rd_value_type {
    ignore_bins POS_OFF = {POSITIVE} `WITH (!rd_is_signed);
    ignore_bins NEG_OFF = {NEGATIVE} `WITH (!rd_is_signed);
    ignore_bins NON_ZERO_OFF = {NON_ZERO} `WITH (rd_is_signed);
  }

  `ISACOV_CP_BITWISE(cp_rs1_toggle, instr.rs1_value, 1)
  `ISACOV_CP_BITWISE(cp_rs2_toggle, instr.rs2_value, 1)
  `ISACOV_CP_BITWISE(cp_rd_toggle,  instr.rd_value,  1)

endgroup : cg_rtype_shift

covergroup cg_div_special_results(
    string name,
    bit check_overflow
) with function sample (
    uvma_isacov_instr_c instr
);
  option.per_instance = 1;
  option.name = name;

  cp_div_zero : coverpoint instr.rs2_value_type {
    bins ZERO = {ZERO};
  }

  cp_div_arithmetic_overflow : coverpoint instr.rs1_value {
    `ifdef UNSUPPORTED_WITH
     ignore_bins IGN_OVERFLOW = cp_div_arithmetic_overflow iff (!check_overflow);
     bins OFLOW = {32'h8000_0000} iff (instr.rs2_value == 32'hffff_ffff); //TODO
    `else
     bins OFLOW = {32'h8000_0000} with (check_overflow) iff (instr.rs2_value == 32'hffff_ffff);
    `endif
  }

endgroup : cg_div_special_results

covergroup cg_itype(
    string name,
    bit reg_crosses_enabled,
    bit reg_hazards_enabled,
    bit rs1_is_signed,
    bit immi_is_signed,
    bit rd_is_signed
) with function sample (
    uvma_isacov_instr_c instr
);
  option.per_instance = 1;
  option.name = name;

  cp_rs1: coverpoint instr.rs1;
  cp_rd: coverpoint instr.rd;

  cp_rd_rs1_hazard: coverpoint instr.rd {
    ignore_bins IGN_RS1_HAZARD_OFF = {[0:$]} `WITH (!reg_hazards_enabled);
    bins RD[] = {[0:31]} iff (instr.rd == instr.rs1);
  }

  cross_rd_rs1: cross cp_rd, cp_rs1 {
    ignore_bins IGN_OFF = cross_rd_rs1 `WITH (!reg_crosses_enabled);
  }

  cp_rs1_value: coverpoint instr.rs1_value_type {
    ignore_bins POS_OFF = {POSITIVE} `WITH (!rs1_is_signed);
    ignore_bins NEG_OFF = {NEGATIVE} `WITH (!rs1_is_signed);
    ignore_bins NON_ZERO_OFF = {NON_ZERO} `WITH (rs1_is_signed);
  }

  cp_immi_value: coverpoint instr.immi_value_type {
    ignore_bins POS_OFF = {POSITIVE} `WITH (!immi_is_signed);
    ignore_bins NEG_OFF = {NEGATIVE} `WITH (!immi_is_signed);
    ignore_bins NON_ZERO_OFF = {NON_ZERO} `WITH (immi_is_signed);
  }

  cross_rs1_immi_value: cross cp_rs1_value, cp_immi_value;

  cp_rd_value: coverpoint instr.rd_value_type {
    ignore_bins POS_OFF = {POSITIVE} `WITH (!rd_is_signed);
    ignore_bins NEG_OFF = {NEGATIVE} `WITH (!rd_is_signed);
    ignore_bins NON_ZERO_OFF = {NON_ZERO} `WITH (rd_is_signed);
  }

  `ISACOV_CP_BITWISE(cp_rs1_toggle,  instr.rs1_value, 1)
  `ISACOV_CP_BITWISE_11_0(cp_imm1_toggle, instr.immi, 1)
  `ISACOV_CP_BITWISE(cp_rd_toggle,   instr.rd_value,  1)

endgroup : cg_itype

covergroup cg_itype_load (
    string name,
    bit reg_crosses_enabled,
    bit reg_hazards_enabled,
    bit rs1_is_signed,
    bit immi_is_signed,
    bit rd_is_signed,
    bit align_halfword,
    bit align_word
) with function sample (
    uvma_isacov_instr_c instr
);
  option.per_instance = 1;
  option.name = name;

  cp_rs1: coverpoint instr.rs1;
  cp_rd: coverpoint instr.rd;

  cp_rd_rs1_hazard: coverpoint instr.rd {
    ignore_bins IGN_RS1_HAZARD_OFF = {[0:$]} `WITH (!reg_hazards_enabled);
    bins RD[] = {[0:31]} iff (instr.rd == instr.rs1);
  }

  cross_rd_rs1: cross cp_rd, cp_rs1 {
    ignore_bins IGN_OFF = cross_rd_rs1 `WITH (!reg_crosses_enabled);
  }

  cp_rs1_value: coverpoint instr.rs1_value_type {
    ignore_bins POS_OFF = {POSITIVE} `WITH (!rs1_is_signed);
    ignore_bins NEG_OFF = {NEGATIVE} `WITH (!rs1_is_signed);
    ignore_bins NON_ZERO_OFF = {NON_ZERO} `WITH (rs1_is_signed);
  }

  cp_immi_value: coverpoint instr.immi_value_type {
    ignore_bins POS_OFF = {POSITIVE} `WITH (!immi_is_signed);
    ignore_bins NEG_OFF = {NEGATIVE} `WITH (!immi_is_signed);
    ignore_bins NON_ZERO_OFF = {NON_ZERO} `WITH (immi_is_signed);
  }

  cross_rs1_immi_value: cross cp_rs1_value, cp_immi_value;

  cp_rd_value: coverpoint instr.rd_value_type {
    ignore_bins POS_OFF = {POSITIVE} `WITH (!rd_is_signed);
    ignore_bins NEG_OFF = {NEGATIVE} `WITH (!rd_is_signed);
    ignore_bins NON_ZERO_OFF = {NON_ZERO} `WITH (rd_is_signed);
  }

  `ISACOV_CP_BITWISE(cp_rs1_toggle,  instr.rs1_value, 1)
  `ISACOV_CP_BITWISE_11_0(cp_imm1_toggle, instr.immi, 1)
  `ISACOV_CP_BITWISE(cp_rd_toggle,   instr.rd_value,  1)

  cp_align_halfword: coverpoint (instr.rvfi.mem_addr[0]) {
    ignore_bins IGN_OFF = {[0:$]} `WITH (!align_halfword);
    bins ALIGNED  = {0};
    bins UNALIGNED = {1};
  }

  cp_align_word: coverpoint (instr.rvfi.mem_addr[1:0]) {
    ignore_bins IGN_OFF = {[0:$]} `WITH (!align_word);
    bins ALIGNED     = {0};
    bins UNALIGNED[] = {[1:3]};
  }

endgroup : cg_itype_load

covergroup cg_itype_slt (
    string name,
    bit reg_crosses_enabled,
    bit reg_hazards_enabled,
    bit rs1_is_signed,
    bit immi_is_signed,
    bit rd_is_signed
) with function sample (
    uvma_isacov_instr_c instr
);
  option.per_instance = 1;
  option.name = name;

  cp_rs1: coverpoint instr.rs1;
  cp_rd: coverpoint instr.rd;

  cp_rd_rs1_hazard: coverpoint instr.rd {
    ignore_bins IGN_RS1_HAZARD_OFF = {[0:$]} `WITH (!reg_hazards_enabled);
    bins RD[] = {[0:31]} iff (instr.rd == instr.rs1);
  }

  cross_rd_rs1: cross cp_rd, cp_rs1 {
    ignore_bins IGN_OFF = cross_rd_rs1 `WITH (!reg_crosses_enabled);
  }

  cp_rs1_value: coverpoint instr.rs1_value_type {
    ignore_bins POS_OFF = {POSITIVE} `WITH (!rs1_is_signed);
    ignore_bins NEG_OFF = {NEGATIVE} `WITH (!rs1_is_signed);
    ignore_bins NON_ZERO_OFF = {NON_ZERO} `WITH (rs1_is_signed);
  }

  cp_immi_value: coverpoint instr.immi_value_type {
    ignore_bins POS_OFF = {POSITIVE} `WITH (!immi_is_signed);
    ignore_bins NEG_OFF = {NEGATIVE} `WITH (!immi_is_signed);
    ignore_bins NON_ZERO_OFF = {NON_ZERO} `WITH (immi_is_signed);
  }

  cross_rs1_immi_value: cross cp_rs1_value, cp_immi_value;

  cp_rd_value: coverpoint instr.rd_value {
    bins SLT[] = {[0:1]};
  }

  `ISACOV_CP_BITWISE(cp_rs1_toggle,  instr.rs1_value, 1)
  `ISACOV_CP_BITWISE_11_0(cp_imm1_toggle, instr.immi, 1)

endgroup : cg_itype_slt

covergroup cg_itype_shift (
    string name,
    bit reg_crosses_enabled,
    bit reg_hazards_enabled,
    bit rs1_is_signed,
    bit immi_is_signed,
    bit rd_is_signed
) with function sample (
    uvma_isacov_instr_c instr
);
  option.per_instance = 1;
  option.name = name;

  cp_rs1: coverpoint instr.rs1;
  cp_rd: coverpoint instr.rd;

  cp_rd_rs1_hazard: coverpoint instr.rd {
    ignore_bins IGN_RS1_HAZARD_OFF = {[0:$]} `WITH (!reg_hazards_enabled);
    bins RD[] = {[0:31]} iff (instr.rd == instr.rs1);
  }

  cross_rd_rs1: cross cp_rd, cp_rs1 {
    ignore_bins IGN_OFF = cross_rd_rs1 `WITH (!reg_crosses_enabled);
  }

  cp_rs1_value: coverpoint instr.rs1_value_type {
    ignore_bins POS_OFF = {POSITIVE} `WITH (!rs1_is_signed);
    ignore_bins NEG_OFF = {NEGATIVE} `WITH (!rs1_is_signed);
    ignore_bins NON_ZERO_OFF = {NON_ZERO} `WITH (rs1_is_signed);
  }

  cp_immi_value: coverpoint (instr.immi[4:0]) {
    bins SHAMT[] = {[0:31]};
  }

  cross_rs1_immi_value: cross cp_rs1_value, cp_immi_value;

  cp_rd_value: coverpoint instr.rd_value_type {
    ignore_bins POS_OFF = {POSITIVE} `WITH (!rd_is_signed);
    ignore_bins NEG_OFF = {NEGATIVE} `WITH (!rd_is_signed);
    ignore_bins NON_ZERO_OFF = {NON_ZERO} `WITH (rd_is_signed);
  }

  `ISACOV_CP_BITWISE(cp_rs1_toggle,  instr.rs1_value, 1)
  `ISACOV_CP_BITWISE(cp_rd_toggle,   instr.rd_value,  1)

endgroup : cg_itype_shift

covergroup cg_stype(
    string name,
    bit reg_crosses_enabled,
    bit align_halfword,
    bit align_word
) with function sample (
    uvma_isacov_instr_c instr
);
  option.per_instance = 1;
  option.name = name;

  cp_rs1: coverpoint instr.rs1;
  cp_rs2: coverpoint instr.rs2;

  cross_rs1_rs2: cross cp_rs1, cp_rs2 {
    ignore_bins IGN_OFF = cross_rs1_rs2 `WITH (!reg_crosses_enabled);
  }

  cp_imms_value: coverpoint instr.imms_value_type {
    ignore_bins NON_ZERO_OFF = {NON_ZERO};
  }

  `ISACOV_CP_BITWISE(cp_rs1_toggle, instr.rs1_value, 1)
  `ISACOV_CP_BITWISE(cp_rs2_toggle, instr.rs2_value, 1)
  `ISACOV_CP_BITWISE_11_0(cp_imms_toggle, instr.imms, 1)

  cp_align_halfword: coverpoint (instr.rvfi.mem_addr[0]) {
    ignore_bins IGN_OFF = {[0:$]} `WITH (!align_halfword);
    bins ALIGNED  = {0};
    bins UNALIGNED = {1};
  }

  cp_align_word: coverpoint (instr.rvfi.mem_addr[1:0]) {
    ignore_bins IGN_OFF = {[0:$]} `WITH (!align_word);
    bins ALIGNED     = {0};
    bins UNALIGNED[] = {[1:3]};
  }

endgroup : cg_stype


covergroup cg_btype(
    string name,
    bit reg_crosses_enabled
) with function sample (
    uvma_isacov_instr_c instr
);
  option.per_instance = 1;
  option.name = name;

  cp_rs1: coverpoint instr.rs1;
  cp_rs2: coverpoint instr.rs2;

  cross_rs1_rs2: cross cp_rs1, cp_rs2 {
    ignore_bins IGN_OFF = cross_rs1_rs2 `WITH (!reg_crosses_enabled);
  }

  cp_immb_value: coverpoint instr.immb_value_type {
    ignore_bins NON_ZERO_OFF = {NON_ZERO};
  }

  cp_branch_taken: coverpoint (instr.is_branch_taken()) {
    bins NOT_TAKEN = {0};
    bins TAKEN     = {1};
  }

  `ISACOV_CP_BITWISE(cp_rs1_toggle, instr.rs1_value, 1)
  `ISACOV_CP_BITWISE(cp_rs2_toggle, instr.rs2_value, 1)
  `ISACOV_CP_BITWISE_11_0(cp_immb_toggle, instr.immb, 1)

endgroup : cg_btype


covergroup cg_utype(string name) with function sample (uvma_isacov_instr_c instr);
  option.per_instance = 1;
  option.name = name;

  cp_rd: coverpoint instr.rd;

  cp_immu_value: coverpoint instr.immu_value_type {
    ignore_bins POS_OFF = {POSITIVE};
    ignore_bins NEG_OFF = {NEGATIVE};
  }

  `ISACOV_CP_BITWISE_31_12(cp_rd_toggle, instr.rd_value, 1)
  `ISACOV_CP_BITWISE_19_0(cp_immu_toggle, instr.immu, 1)

endgroup : cg_utype


covergroup cg_jtype(
    string name
) with function sample (
  uvma_isacov_instr_c instr
);
  option.per_instance = 1;
  option.name = name;

  cp_rd: coverpoint instr.rd;

  cp_immj_value: coverpoint instr.immj_value_type {
    ignore_bins NON_ZERO_OFF = {NON_ZERO};
  }

  `ISACOV_CP_BITWISE(cp_rd_toggle, instr.rd_value, 1)
  `ISACOV_CP_BITWISE_19_0(cp_immj_toggle, instr.immj, 1)

endgroup : cg_jtype

covergroup cg_csrtype(
    string name,
    bit[CSR_MASK_WL-1:0] cfg_illegal_csr,
    bit reg_crosses_enabled,
    bit reg_hazards_enabled
) with function sample (
    uvma_isacov_instr_c instr
);
  option.per_instance = 1;
  option.name = name;

  cp_rs1: coverpoint instr.rs1;
  cp_rd: coverpoint instr.rd;
  cp_csr: coverpoint instr.csr {
    bins CSR[] = {[USTATUS:VLENB]} with (cfg_illegal_csr[item] == 0);
  }

  cp_rd_rs1_hazard: coverpoint instr.rd {
    ignore_bins IGN_RS1_HAZARD_OFF = {[0:$]} `WITH (!reg_hazards_enabled);
    bins RD[] = {[0:31]} iff (instr.rd == instr.rs1);
  }

  cross_rd_rs1: cross cp_rd, cp_rs1 {
    ignore_bins IGN_OFF = cross_rd_rs1 `WITH (!reg_crosses_enabled);
  }
endgroup : cg_csrtype

covergroup cg_csritype(
    string name,
    bit[CSR_MASK_WL-1:0] cfg_illegal_csr,
    bit reg_crosses_enabled
) with function sample (
    uvma_isacov_instr_c instr
);
  option.per_instance = 1;
  option.name = name;

  cp_rd: coverpoint instr.rd;
  cp_csr: coverpoint instr.csr {
    bins CSR[] = {[USTATUS:VLENB]} with (cfg_illegal_csr[item] == 0);
  }
  `ISACOV_CP_BITWISE_4_0(cp_uimm_toggle, instr.rs1, 1)
endgroup : cg_csritype

covergroup cg_cr(
    string name,
    bit reg_crosses_enabled,
    bit reg_hazards_enabled,
    bit rdrs1_is_signed,
    bit has_rs1,
    bit rs2_is_signed
) with function sample (
    uvma_isacov_instr_c instr
);
  option.per_instance = 1;
  option.name = name;

  cp_c_rdrs1: coverpoint instr.c_rdrs1 {
    ignore_bins RDRS1_NOT_ZERO = {0};
  }
  cp_rs2: coverpoint instr.rs2 {
    ignore_bins RS2_NOT_ZERO = {0};
  }

  cp_rs1_value: coverpoint instr.rs1_value_type {
    ignore_bins  OFF     = cp_rs1_value    `WITH (!has_rs1);
    ignore_bins POS_OFF = {POSITIVE} `WITH (!rdrs1_is_signed);
    ignore_bins NEG_OFF = {NEGATIVE} `WITH (!rdrs1_is_signed);
    ignore_bins NON_ZERO_OFF = {NON_ZERO} `WITH (rdrs1_is_signed);
  }

  cp_rs2_value: coverpoint instr.rs2_value_type {
    ignore_bins POS_OFF = {POSITIVE} `WITH (!rs2_is_signed);
    ignore_bins NEG_OFF = {NEGATIVE} `WITH (!rs2_is_signed);
    ignore_bins NON_ZERO_OFF = {NON_ZERO} `WITH (rs2_is_signed);
  }

  cp_rd_value: coverpoint instr.rd_value_type {
    ignore_bins POS_OFF = {POSITIVE} `WITH (!rdrs1_is_signed);
    ignore_bins NEG_OFF = {NEGATIVE} `WITH (!rdrs1_is_signed);
    ignore_bins NON_ZERO_OFF = {NON_ZERO} `WITH (rdrs1_is_signed);
  }


  cp_rd_rs2_hazard: coverpoint instr.rd {
    ignore_bins IGN_RS2_HAZARD_OFF = {[0:$]} `WITH (!reg_hazards_enabled);
    bins RD[] = {[1:31]} iff (instr.rd == instr.rs2);
  }

  cross_rdrs1_rs2: cross cp_c_rdrs1, cp_rs2 {
    ignore_bins IGN_OFF = cross_rdrs1_rs2 `WITH (!reg_crosses_enabled);
  }

  `ISACOV_CP_BITWISE(cp_rs1_toggle, instr.rs1_value, has_rs1)
  `ISACOV_CP_BITWISE(cp_rs2_toggle, instr.rs2_value, 1)
  `ISACOV_CP_BITWISE(cp_rd_toggle, instr.rd_value, 1)

endgroup : cg_cr

covergroup cg_cr_j(
    string name,
    bit reg_crosses_enabled,
    bit reg_hazards_enabled,
    bit rs1_is_signed
) with function sample (
    uvma_isacov_instr_c instr
);
  option.per_instance = 1;
  option.name = name;

  cp_c_rdrs1: coverpoint instr.c_rdrs1 {
    ignore_bins RDRS1_NOT_ZERO = {0};
  }

  cp_rs1_value: coverpoint instr.rs1_value_type {
    ignore_bins POS_OFF = {POSITIVE} `WITH (!rs1_is_signed);
    ignore_bins NEG_OFF = {NEGATIVE} `WITH (!rs1_is_signed);
    ignore_bins NON_ZERO_OFF = {NON_ZERO} `WITH (rs1_is_signed);
  }

  `ISACOV_CP_BITWISE(cp_rs1_toggle, instr.rs1_value, 1)

endgroup : cg_cr_j

covergroup cg_ci(
    string name,
    bit rs1_is_signed,
    bit imm_is_signed,
    bit rd_is_signed,
    bit imm_is_nonzero,
    bit has_rs1,
    bit tie_rdrs1_x2
) with function sample (
    uvma_isacov_instr_c instr
);
  option.per_instance = 1;
  option.name = name;

  cp_rs1_value: coverpoint instr.rs1_value_type {
    ignore_bins  OFF     = cp_rs1_value    `WITH (!has_rs1);
    illegal_bins POS_OFF = {POSITIVE}      `WITH (!rs1_is_signed);
    illegal_bins NEG_OFF = {NEGATIVE}      `WITH (!rs1_is_signed);
    illegal_bins NON_ZERO_OFF = {NON_ZERO} `WITH ( rs1_is_signed);
  }

  cp_imm_value: coverpoint instr.c_imm_value_type {
    illegal_bins POS_OFF      = {POSITIVE} `WITH (!imm_is_signed);
    illegal_bins NEG_OFF      = {NEGATIVE} `WITH (!imm_is_signed);
    illegal_bins NON_ZERO_OFF = {NON_ZERO} `WITH (imm_is_signed);
    ignore_bins  ZERO_OFF     = {ZERO}     `WITH (imm_is_nonzero);  // Not illegal, because of HINT instrs
  }

  cp_rd_value: coverpoint instr.rd_value_type {
    illegal_bins POS_OFF = {POSITIVE} `WITH (!rd_is_signed);
    illegal_bins NEG_OFF = {NEGATIVE} `WITH (!rd_is_signed);
    illegal_bins NON_ZERO_OFF = {NON_ZERO} `WITH (rd_is_signed);
  }

  cp_rdrs1: coverpoint instr.c_rdrs1 {
    illegal_bins RD_NOT_ZERO = {0};
    illegal_bins NON_X2      = cp_rdrs1 with ((item != 2) && tie_rdrs1_x2);
  }

  `ISACOV_CP_BITWISE(cp_rd_toggle, instr.rd_value, 1)
  `ISACOV_CP_BITWISE_5_0(cp_imm_toggle, instr.get_field_imm(), 1)

endgroup : cg_ci

covergroup cg_ci_shift(
    string name,
    bit rs1_is_signed,
    bit rd_is_signed
) with function sample (
    uvma_isacov_instr_c instr
);
  option.per_instance = 1;
  option.name = name;

  cp_rs1_value: coverpoint instr.rs1_value_type {
    ignore_bins POS_OFF = {POSITIVE} `WITH (!rs1_is_signed);
    ignore_bins NEG_OFF = {NEGATIVE} `WITH (!rs1_is_signed);
    ignore_bins NON_ZERO_OFF = {NON_ZERO} `WITH (rs1_is_signed);
  }

  cp_rd_value: coverpoint instr.rd_value_type {
    ignore_bins POS_OFF = {POSITIVE} `WITH (!rd_is_signed);
    ignore_bins NEG_OFF = {NEGATIVE} `WITH (!rd_is_signed);
    ignore_bins NON_ZERO_OFF = {NON_ZERO} `WITH (rd_is_signed);
  }

  cp_shamt: coverpoint instr.get_field_imm() {
    bins SHAMT[] = {[0:63]};
    illegal_bins ILLEGAL_SHAMT[] = {[32:63]};                                  // MSB of the immediate value should be always zero
  }

  cp_rd: coverpoint instr.rd {
    ignore_bins RD_NOT_ZERO = {0};
  }

  `ISACOV_CP_BITWISE(cp_rd_toggle, instr.rd_value, 1)							// No need to toggle imm again because cp_shamt did the job

endgroup : cg_ci_shift

covergroup cg_ci_li(
    string name
) with function sample (
    uvma_isacov_instr_c instr
);
  option.per_instance = 1;
  option.name = name;

  cp_rd: coverpoint instr.rd {
    ignore_bins RD_NOT_ZERO = {0};
  }

  `ISACOV_CP_BITWISE(cp_rd_toggle, instr.rd_value, 1)
  `ISACOV_CP_BITWISE_5_0(cp_imm_toggle, instr.get_field_imm(), 1)

endgroup : cg_ci_li

covergroup cg_ci_lui(
    string name
) with function sample (
    uvma_isacov_instr_c instr
);
  option.per_instance = 1;
  option.name = name;

  cp_rd: coverpoint instr.rd {
    ignore_bins RD_NOT_ZERO = {0};
    ignore_bins RD_NOT_TWO  = {2};
  }

  `ISACOV_CP_BITWISE_31_12(cp_rd_toggle, instr.rd_value, 1)
  `ISACOV_CP_BITWISE_5_0(cp_imm_toggle, instr.get_field_imm(), 1)

endgroup : cg_ci_lui

covergroup cg_css(
    string name,
    bit rs2_is_signed,
    bit imm_is_signed
) with function sample (
    uvma_isacov_instr_c instr
);
  option.per_instance = 1;
  option.name = name;

  cp_rs2: coverpoint instr.rs2;

  cp_rs2_value: coverpoint instr.rs2_value_type {
    ignore_bins POS_OFF = {POSITIVE} `WITH (!rs2_is_signed);
    ignore_bins NEG_OFF = {NEGATIVE} `WITH (!rs2_is_signed);
    ignore_bins NON_ZERO_OFF = {NON_ZERO} `WITH (rs2_is_signed);
  }

  cp_imm_value: coverpoint instr.c_imm_value_type {
    ignore_bins POS_OFF = {POSITIVE} `WITH (!imm_is_signed);
    ignore_bins NEG_OFF = {NEGATIVE} `WITH (!imm_is_signed);
    ignore_bins NON_ZERO_OFF = {NON_ZERO} `WITH (imm_is_signed);
  }

  `ISACOV_CP_BITWISE    (cp_rs2_toggle, instr.rs2_value,         1)
  `ISACOV_CP_BITWISE_5_0(cp_imm_toggle, instr.get_field_imm(),   1)

endgroup : cg_css

covergroup cg_ciw(
    string name
) with function sample (
    uvma_isacov_instr_c instr
);
  option.per_instance = 1;
  option.name = name;

  cp_c_rd: coverpoint instr.c_rd;

  `ISACOV_CP_BITWISE(cp_rd_toggle, instr.rd_value, 1)
  `ISACOV_CP_BITWISE_7_0(cp_imm_toggle, instr.get_field_imm(), 1)

endgroup : cg_ciw

covergroup cg_cl(
    string name,
    bit reg_crosses_enabled,
    bit reg_hazards_enabled,
    bit rs1_is_signed,
    bit imm_is_signed
) with function sample (
    uvma_isacov_instr_c instr
);
  option.per_instance = 1;
  option.name = name;

  cp_rs1_value: coverpoint instr.rs1_value_type {
    ignore_bins POS_OFF = {POSITIVE} `WITH (!rs1_is_signed);
    ignore_bins NEG_OFF = {NEGATIVE} `WITH (!rs1_is_signed);
    ignore_bins NON_ZERO_OFF = {NON_ZERO} `WITH (rs1_is_signed);
  }

  cp_imm_value: coverpoint instr.c_imm_value_type {
    ignore_bins POS_OFF = {POSITIVE} `WITH (!imm_is_signed);
    ignore_bins NEG_OFF = {NEGATIVE} `WITH (!imm_is_signed);
    ignore_bins NON_ZERO_OFF = {NON_ZERO} `WITH (imm_is_signed);
  }

  cp_c_rs1: coverpoint instr.c_rs1;
  cp_c_rd:  coverpoint instr.c_rd;

  cp_c_rd_rs1_hazard: coverpoint instr.c_rd {
    ignore_bins IGN_RS1_HAZARD_OFF = {[0:$]} `WITH (!reg_hazards_enabled);
    bins RD[] = {[0:7]} iff (instr.c_rd == instr.c_rs1);
  }

  `ISACOV_CP_BITWISE(cp_rs1_toggle, instr.rs1_value, 1)
  `ISACOV_CP_BITWISE_4_0(cp_imm_toggle, instr.get_field_imm(), 1)

endgroup : cg_cl

covergroup cg_cs(
    string name,
    bit reg_crosses_enabled,
    bit rs1_is_signed,
    bit rs2_is_signed,
    bit imm_is_signed
) with function sample (
    uvma_isacov_instr_c instr
);
  option.per_instance = 1;
  option.name = name;

  cp_rs1_value: coverpoint instr.rs1_value_type {
    ignore_bins POS_OFF = {POSITIVE} `WITH (!rs1_is_signed);
    ignore_bins NEG_OFF = {NEGATIVE} `WITH (!rs1_is_signed);
    ignore_bins NON_ZERO_OFF = {NON_ZERO} `WITH (rs1_is_signed);
  }

  cp_rs2_value: coverpoint instr.rs2_value_type {
    ignore_bins POS_OFF = {POSITIVE} `WITH (!rs2_is_signed);
    ignore_bins NEG_OFF = {NEGATIVE} `WITH (!rs2_is_signed);
    ignore_bins NON_ZERO_OFF = {NON_ZERO} `WITH (rs2_is_signed);
  }

  cp_c_rs1: coverpoint instr.c_rs1;
  cp_c_rs2: coverpoint instr.c_rs2;

  `ISACOV_CP_BITWISE(cp_rs2_toggle, instr.rs2_value, 1)
  `ISACOV_CP_BITWISE(cp_rs1_toggle, instr.rs1_value, 1)
  `ISACOV_CP_BITWISE_4_0(cp_imm_toggle, instr.get_field_imm(), 1)

endgroup : cg_cs

covergroup cg_ca(
    string name,
    bit reg_crosses_enabled,
    bit reg_hazards_enabled,
    bit rs1_is_signed,
    bit rs2_is_signed,
    bit rd_is_signed
) with function sample (
    uvma_isacov_instr_c instr
);
  option.per_instance = 1;
  option.name = name;

  cp_rs1_value: coverpoint instr.rs1_value_type {
    ignore_bins POS_OFF = {POSITIVE} `WITH (!rs1_is_signed);
    ignore_bins NEG_OFF = {NEGATIVE} `WITH (!rs1_is_signed);
    ignore_bins NON_ZERO_OFF = {NON_ZERO} `WITH (rs1_is_signed);
  }

  cp_rs2_value: coverpoint instr.rs2_value_type {
    ignore_bins POS_OFF = {POSITIVE} `WITH (!rs2_is_signed);
    ignore_bins NEG_OFF = {NEGATIVE} `WITH (!rs2_is_signed);
    ignore_bins NON_ZERO_OFF = {NON_ZERO} `WITH (rs2_is_signed);
  }

  cp_rd_value: coverpoint instr.rd_value_type {
    ignore_bins POS_OFF = {POSITIVE} `WITH (!rd_is_signed);
    ignore_bins NEG_OFF = {NEGATIVE} `WITH (!rd_is_signed);
    ignore_bins NON_ZERO_OFF = {NON_ZERO} `WITH (rd_is_signed);
  }

  cp_c_rs2: coverpoint instr.c_rs2;
  cp_c_rdrs1: coverpoint instr.c_rs1;

  cross_rs1_rs2: cross cp_c_rs2, cp_c_rdrs1 {
    ignore_bins IGN_OFF = cross_rs1_rs2 `WITH (!reg_crosses_enabled);
  }

  `ISACOV_CP_BITWISE(cp_rd_toggle, instr.rd_value, 1)
  `ISACOV_CP_BITWISE(cp_rs2_toggle, instr.rs2_value, 1)
  `ISACOV_CP_BITWISE(cp_rs1_toggle, instr.rs1_value, 1)

endgroup : cg_ca

covergroup cg_cb(
    string name,
    bit rs1_is_signed,
    bit imm_is_signed
) with function sample (
    uvma_isacov_instr_c instr
);
  option.per_instance = 1;
  option.name = name;

  cp_rs1_value: coverpoint instr.rs1_value_type {
    ignore_bins POS_OFF = {POSITIVE} `WITH (!rs1_is_signed);
    ignore_bins NEG_OFF = {NEGATIVE} `WITH (!rs1_is_signed);
    ignore_bins NON_ZERO_OFF = {NON_ZERO} `WITH (rs1_is_signed);
  }

  cp_imm_value: coverpoint instr.c_imm_value_type {
    ignore_bins POS_OFF = {POSITIVE} `WITH (!imm_is_signed);
    ignore_bins NEG_OFF = {NEGATIVE} `WITH (!imm_is_signed);
    ignore_bins NON_ZERO_OFF = {NON_ZERO} `WITH (imm_is_signed);
  }

  cp_c_rs1: coverpoint instr.c_rs1;

  `ISACOV_CP_BITWISE(cp_rs1_toggle, instr.rs1_value, 1)
  `ISACOV_CP_BITWISE_7_0(cp_imm_toggle, instr.get_field_imm(), 1)

endgroup : cg_cb

covergroup cg_cb_andi(
    string name,
    bit rs1_is_signed,
    bit imm_is_signed
) with function sample (
    uvma_isacov_instr_c instr
);
  option.per_instance = 1;
  option.name = name;

  cp_rs1_value: coverpoint instr.rs1_value_type {
    ignore_bins POS_OFF = {POSITIVE} `WITH (!rs1_is_signed);
    ignore_bins NEG_OFF = {NEGATIVE} `WITH (!rs1_is_signed);
    ignore_bins NON_ZERO_OFF = {NON_ZERO} `WITH (rs1_is_signed);
  }

  cp_imm_value: coverpoint instr.c_imm_value_type {
    ignore_bins POS_OFF = {POSITIVE} `WITH (!imm_is_signed);
    ignore_bins NEG_OFF = {NEGATIVE} `WITH (!imm_is_signed);
    ignore_bins NON_ZERO_OFF = {NON_ZERO} `WITH (imm_is_signed);
  }

  cp_c_rdrs1: coverpoint instr.c_rs1;

  `ISACOV_CP_BITWISE(cp_rs1_toggle, instr.rs1_value, 1)
  `ISACOV_CP_BITWISE_5_0(cp_imm_toggle, instr.get_field_imm(), 1)

endgroup : cg_cb_andi

covergroup cg_cb_shift(
    string name,
    bit rs1_is_signed
) with function sample (
    uvma_isacov_instr_c instr
);
  option.per_instance = 1;
  option.name = name;

  cp_rs1_value: coverpoint instr.rs1_value_type {
    ignore_bins POS_OFF = {POSITIVE} `WITH (!rs1_is_signed);
    ignore_bins NEG_OFF = {NEGATIVE} `WITH (!rs1_is_signed);
    ignore_bins NON_ZERO_OFF = {NON_ZERO} `WITH (rs1_is_signed);
  }

  cp_shamt: coverpoint instr.get_field_imm() {
    bins SHAMT[] = {[0:63]};
    illegal_bins ILLEGAL_SHAMT[] = {[32:63]};                                  // MSB of the immediate value should be always zero
  }

  cp_c_rdrs1: coverpoint instr.c_rs1;

  `ISACOV_CP_BITWISE(cp_rs1_toggle, instr.rs1_value, 1)							// No need to toggle imm again because cp_shamt did the job

endgroup : cg_cb_shift

covergroup cg_cj(
    string name,
    bit imm_is_signed
) with function sample (
    uvma_isacov_instr_c instr
);
  option.per_instance = 1;
  option.name = name;

  cp_imm_value: coverpoint instr.c_imm_value_type {
    ignore_bins POS_OFF = {POSITIVE} `WITH (!imm_is_signed);
    ignore_bins NEG_OFF = {NEGATIVE} `WITH (!imm_is_signed);
    ignore_bins NON_ZERO_OFF = {NON_ZERO} `WITH (imm_is_signed);
  }

  `ISACOV_CP_BITWISE_10_0(cp_imm_toggle, instr.get_field_imm(), 1)

endgroup : cg_cj

covergroup cg_sequential(string name,
                         bit seq_instr_group_x2_enabled,
                         bit seq_instr_group_x3_enabled,
                         bit seq_instr_group_x4_enabled,
                         bit seq_instr_x2_enabled,
                         bit [CSR_MASK_WL-1:0] cfg_illegal_csr,
                         bit unaligned_access_supported,
                         bit ext_m_supported,
                         bit ext_c_supported,
                         bit ext_zba_supported,
                         bit ext_zbb_supported,
                         bit ext_zbc_supported,
                         bit ext_zbs_supported,
                         bit ext_a_supported) with function sample (uvma_isacov_instr_c instr,
                                                                 uvma_isacov_instr_c instr_prev,
                                                                 uvma_isacov_instr_c instr_prev2,
                                                                 uvma_isacov_instr_c instr_prev3,
                                                                 bit raw_hazard,
                                                                 bit csr_hazard);
  option.per_instance = 1;
  option.name = name;

  cp_instr: coverpoint(instr.name) {
    `ISACOV_IGN_BINS
  }

  cp_instr_prev_x2: coverpoint(instr_prev.name) iff (instr_prev != null) {
    `ISACOV_IGN_BINS
    ignore_bins IGN_X2_OFF = {[0:$]} `WITH (!seq_instr_x2_enabled);
  }

  cross_seq_instr_x2: cross cp_instr, cp_instr_prev_x2;

  cp_group: coverpoint (instr.group) {
    illegal_bins ILL_EXT_M = {MUL_GROUP, MULTI_MUL_GROUP, DIV_GROUP} `WITH (!ext_m_supported);
    illegal_bins ILL_EXT_A = {ALOAD_GROUP, ASTORE_GROUP, AMEM_GROUP} `WITH (!ext_a_supported);
    illegal_bins ILL_MISALIGN = {MISALIGN_LOAD_GROUP, MISALIGN_STORE_GROUP} `WITH (!unaligned_access_supported);
  }

  cp_group_pipe_x2:  coverpoint (instr_prev.group) iff (instr_prev != null) {
    ignore_bins IGN_X2_OFF = {[0:$]} `WITH (!seq_instr_group_x2_enabled);
    illegal_bins ILL_EXT_M = {MUL_GROUP, MULTI_MUL_GROUP, DIV_GROUP} `WITH (!ext_m_supported);
    illegal_bins ILL_EXT_A = {ALOAD_GROUP, ASTORE_GROUP, AMEM_GROUP} `WITH (!ext_a_supported);
    illegal_bins ILL_MISALIGN = {MISALIGN_LOAD_GROUP, MISALIGN_STORE_GROUP} `WITH (!unaligned_access_supported);
  }

  cp_group_pipe_x3: coverpoint (instr_prev2.group) iff (instr_prev2 != null) {
    ignore_bins IGN_X3_OFF = {[0:$]} `WITH (!seq_instr_group_x3_enabled);
    illegal_bins ILL_EXT_M = {MUL_GROUP, MULTI_MUL_GROUP, DIV_GROUP} `WITH (!ext_m_supported);
    illegal_bins ILL_EXT_A = {ALOAD_GROUP, ASTORE_GROUP, AMEM_GROUP} `WITH (!ext_a_supported);
    illegal_bins ILL_MISALIGN = {MISALIGN_LOAD_GROUP, MISALIGN_STORE_GROUP} `WITH (!unaligned_access_supported);
  }

  cp_group_pipe_x4: coverpoint (instr_prev3.group) iff (instr_prev3 != null) {
    ignore_bins IGN_X4_OFF = {[0:$]} `WITH (!seq_instr_group_x4_enabled);
    illegal_bins ILL_EXT_M = {MUL_GROUP, MULTI_MUL_GROUP, DIV_GROUP} `WITH (!ext_m_supported);
    illegal_bins ILL_EXT_A = {ALOAD_GROUP, ASTORE_GROUP, AMEM_GROUP} `WITH (!ext_a_supported);
    illegal_bins ILL_MISALIGN = {MISALIGN_LOAD_GROUP, MISALIGN_STORE_GROUP} `WITH (!unaligned_access_supported);
  }

  cp_gpr_raw_hazard: coverpoint(raw_hazard) {
    bins NO_RAW_HAZARD  = {0};
    bins RAW_HAZARD     = {1};
  }

  cp_csr_hazard: coverpoint(csr_hazard) {
    bins NO_CSR_HAZARD  = {0};
    bins CSR_HAZARD     = {1};
  }

  cp_csr: coverpoint(instr_prev.csr) iff (instr_prev != null) {
    bins CSR[] = {[USTATUS:VLENB]} with (cfg_illegal_csr[item] == 0);
  }

  cross_seq_group_x2: cross cp_group, cp_group_pipe_x2;
  cross_seq_group_x3: cross cp_group, cp_group_pipe_x2, cp_group_pipe_x3;
  cross_seq_group_x4: cross cp_group, cp_group_pipe_x2, cp_group_pipe_x3, cp_group_pipe_x4;

  cross_seq_gpr_raw_hazard: cross cp_group, cp_group_pipe_x2, cp_gpr_raw_hazard {
    // Ignore non-hazard bins
    ignore_bins IGN_HAZ = binsof(cp_gpr_raw_hazard) intersect {0};
    ignore_bins IGN_GROUP = binsof(cp_group) intersect {UNKNOWN_GROUP,
                                                        FENCE_GROUP,
                                                        FENCE_I_GROUP,
                                                        RET_GROUP,
                                                        WFI_GROUP,
                                                        ENV_GROUP};
    ignore_bins IGN_PREV_GROUP = binsof(cp_group_pipe_x2) intersect {UNKNOWN_GROUP,
                                                                     FENCE_GROUP,
                                                                     FENCE_I_GROUP,
                                                                     RET_GROUP,
                                                                     WFI_GROUP,
                                                                     ENV_GROUP,
                                                                     STORE_GROUP,
                                                                     BRANCH_GROUP};
  }

  cross_seq_csr_hazard_x2: cross cp_csr, cp_instr, cp_csr_hazard {
    // Ignore non-hazard bins
    ignore_bins IGN_HAZ = binsof(cp_csr_hazard) intersect {0};
  }
endgroup : cg_sequential


class uvma_isacov_cov_model_c extends uvm_component;

  `uvm_component_utils(uvma_isacov_cov_model_c)

  // Objects
  uvma_isacov_cfg_c cfg;

  // Store previous instruction
  uvma_isacov_instr_c instr_prev;
  uvma_isacov_instr_c instr_prev2;
  uvma_isacov_instr_c instr_prev3;

  // Covergroups
  //32I:
  cg_rtype rv32i_add_cg;
  cg_rtype rv32i_sub_cg;
  cg_rtype_slt rv32i_slt_cg;
  cg_rtype_slt rv32i_sltu_cg;
  cg_rtype_shift rv32i_sll_cg;
  cg_rtype_shift rv32i_srl_cg;
  cg_rtype_shift rv32i_sra_cg;
  cg_rtype rv32i_or_cg;
  cg_rtype rv32i_and_cg;
  cg_rtype rv32i_xor_cg;

  cg_itype rv32i_jalr_cg;
  cg_itype_load rv32i_lb_cg;
  cg_itype_load rv32i_lh_cg;
  cg_itype_load rv32i_lw_cg;
  cg_itype_load rv32i_lbu_cg;
  cg_itype_load rv32i_lhu_cg;
  cg_itype      rv32i_addi_cg;
  cg_itype_slt rv32i_slti_cg;
  cg_itype_slt rv32i_sltiu_cg;
  cg_itype rv32i_xori_cg;
  cg_itype rv32i_ori_cg;
  cg_itype rv32i_andi_cg;
  cg_itype_shift rv32i_slli_cg;
  cg_itype_shift rv32i_srli_cg;
  cg_itype_shift rv32i_srai_cg;

  cg_executed_type rv32i_fence_cg;
  cg_executed_type rv32i_wfi_cg;
  cg_executed_type rv32i_mret_cg;
  cg_executed_type rv32i_dret_cg;

  cg_stype rv32i_sb_cg;
  cg_stype rv32i_sh_cg;
  cg_stype rv32i_sw_cg;

  cg_btype rv32i_beq_cg;
  cg_btype rv32i_bne_cg;
  cg_btype rv32i_blt_cg;
  cg_btype rv32i_bge_cg;
  cg_btype rv32i_bltu_cg;
  cg_btype rv32i_bgeu_cg;

  cg_utype rv32i_lui_cg;
  cg_utype rv32i_auipc_cg;

  cg_jtype rv32i_jal_cg;

  cg_executed_type rv32i_ecall_cg;
  cg_executed_type rv32i_ebreak_cg;

  //32M:
  cg_rtype rv32m_mul_cg;
  cg_rtype rv32m_mulh_cg;
  cg_rtype rv32m_mulhsu_cg;
  cg_rtype rv32m_mulhu_cg;
  cg_rtype rv32m_div_cg;
  cg_div_special_results rv32m_div_results_cg;
  cg_rtype rv32m_divu_cg;
  cg_div_special_results rv32m_divu_results_cg;
  cg_rtype rv32m_rem_cg;
  cg_div_special_results rv32m_rem_results_cg;
  cg_rtype rv32m_remu_cg;
  cg_div_special_results rv32m_remu_results_cg;

  //32C:
  cg_ci       rv32c_addi_cg;
  cg_ci       rv32c_addi16sp_cg;
  cg_ci       rv32c_lwsp_cg;
  cg_ci_shift rv32c_slli_cg;
  cg_ci_li    rv32c_li_cg;
  cg_ci_lui   rv32c_lui_cg;

  cg_cr       rv32c_mv_cg;
  cg_cr       rv32c_add_cg;
  cg_cr_j     rv32c_jr_cg;
  cg_cr_j     rv32c_jalr_cg;

  cg_css      rv32c_swsp_cg;

  cg_ciw      rv32c_addi4spn_cg;

  cg_cl       rv32c_lw_cg;

  cg_cs       rv32c_sw_cg;

  cg_ca       rv32c_sub_cg;
  cg_ca       rv32c_xor_cg;
  cg_ca       rv32c_or_cg;
  cg_ca       rv32c_and_cg;

  cg_cb_shift rv32c_srli_cg;
  cg_cb_shift rv32c_srai_cg;
  cg_cb_andi  rv32c_andi_cg;
  cg_cb       rv32c_beqz_cg;
  cg_cb       rv32c_bnez_cg;

  cg_cj       rv32c_jal_cg;
  cg_cj       rv32c_j_cg;

  cg_executed_type  rv32c_nop_cg;
  cg_executed_type  rv32c_ebreak_cg;

  //Zicsr:
  cg_csrtype  rv32zicsr_csrrw_cg;
  cg_csrtype  rv32zicsr_csrrs_cg;
  cg_csrtype  rv32zicsr_csrrc_cg;
  cg_csritype rv32zicsr_csrrwi_cg;
  cg_csritype rv32zicsr_csrrsi_cg;
  cg_csritype rv32zicsr_csrrci_cg;

  //Zifencei:
  cg_executed_type  rv32zifencei_fence_i_cg;

  //32A:
  cg_rtype_lr_w rv32a_lr_w_cg;
  cg_rtype_sc_w rv32a_sc_w_cg;
  cg_rtype_amo  rv32a_amoswap_w_cg;
  cg_rtype_amo  rv32a_amoadd_w_cg;
  cg_rtype_amo  rv32a_amoxor_w_cg;
  cg_rtype_amo  rv32a_amoand_w_cg;
  cg_rtype_amo  rv32a_amoor_w_cg;
  cg_rtype_amo  rv32a_amomin_w_cg;
  cg_rtype_amo  rv32a_amomax_w_cg;
  cg_rtype_amo  rv32a_amominu_w_cg;
  cg_rtype_amo  rv32a_amomaxu_w_cg;

  //32B:
  cg_rtype       rv32zba_sh1add_cg;
  cg_rtype       rv32zba_sh2add_cg;
  cg_rtype       rv32zba_sh3add_cg;

  cg_zb_rstype  rv32zbb_clz_cg;
  cg_zb_rstype  rv32zbb_ctz_cg;
  cg_zb_rstype  rv32zbb_cpop_cg;
  cg_rtype      rv32zbb_min_cg;
  cg_rtype      rv32zbb_minu_cg;
  cg_rtype      rv32zbb_max_cg;
  cg_rtype      rv32zbb_maxu_cg;
  cg_zb_rstype  rv32zbb_sext_b_cg;
  cg_zb_rstype  rv32zbb_sext_h_cg;
  cg_zb_rstype  rv32zbb_zext_h_cg;
  cg_rtype      rv32zbb_andn_cg;
  cg_rtype      rv32zbb_orn_cg;
  cg_rtype      rv32zbb_xnor_cg;
  cg_rtype      rv32zbb_rol_cg;
  cg_rtype      rv32zbb_ror_cg;
  cg_zb_itype_shift rv32zbb_rori_cg;
  cg_zb_rstype  rv32zbb_rev8_cg;
  cg_zb_rstype  rv32zbb_orc_b_cg;

  cg_rtype      rv32zbc_clmul_cg;
  cg_rtype      rv32zbc_clmulh_cg;
  cg_rtype      rv32zbc_clmulr_cg;

  cg_rtype          rv32zbs_bset_cg;
  cg_zb_itype_shift rv32zbs_bseti_cg;
  cg_rtype          rv32zbs_bclr_cg;
  cg_zb_itype_shift rv32zbs_bclri_cg;
  cg_rtype          rv32zbs_binv_cg;
  cg_zb_itype_shift rv32zbs_binvi_cg;
  cg_zb_rstype_ext  rv32zbs_bext_cg;
  cg_zb_itype_ext   rv32zbs_bexti_cg;

  // Sequential instruction coverage
  cg_sequential     rv32_seq_cg;

  // TLM
  uvm_tlm_analysis_fifo #(uvma_isacov_mon_trn_c) mon_trn_fifo;

  extern function new(string name = "uvma_isacov_cov_model", uvm_component parent = null);
  extern virtual function void build_phase(uvm_phase phase);
  extern virtual task run_phase(uvm_phase phase);
  extern function void sample (uvma_isacov_instr_c instr);

  extern function bit is_raw_hazard(uvma_isacov_instr_c instr,
                                    uvma_isacov_instr_c instr_prev);
  extern function bit is_csr_hazard(uvma_isacov_instr_c instr,
                                    uvma_isacov_instr_c instr_prev);
endclass : uvma_isacov_cov_model_c


function uvma_isacov_cov_model_c::new(string name = "uvma_isacov_cov_model", uvm_component parent = null);

  super.new(name, parent);

endfunction : new


function void uvma_isacov_cov_model_c::build_phase(uvm_phase phase);

  super.build_phase(phase);

  void'(uvm_config_db#(uvma_isacov_cfg_c)::get(this, "", "cfg", cfg));
  if (!cfg) begin
    `uvm_fatal("CFG", "Configuration handle is null")
  end

  if (cfg.enabled && cfg.cov_model_enabled) begin

    // ----------------------------------------------------------------------------------------
    // I Extension
    // ----------------------------------------------------------------------------------------

    if (cfg.core_cfg.ext_i_supported) begin
      rv32i_lui_cg    = new("rv32i_lui_cg");
      rv32i_auipc_cg  = new("rv32i_auipc_cg");
      rv32i_jal_cg    = new("rv32i_jal_cg");
      rv32i_jalr_cg   = new("rv32i_jalr_cg",
                            .reg_crosses_enabled(cfg.reg_crosses_enabled),
                            .reg_hazards_enabled(cfg.reg_hazards_enabled),
                            .rs1_is_signed(rs1_is_signed[JALR]),
                            .immi_is_signed(immi_is_signed[JALR]),
                            .rd_is_signed(rd_is_signed[JALR]));

      rv32i_beq_cg    = new("rv32i_beq_cg", .reg_crosses_enabled(cfg.reg_crosses_enabled));
      rv32i_bne_cg    = new("rv32i_bne_cg", .reg_crosses_enabled(cfg.reg_crosses_enabled));
      rv32i_blt_cg    = new("rv32i_blt_cg", .reg_crosses_enabled(cfg.reg_crosses_enabled));
      rv32i_bge_cg    = new("rv32i_bge_cg", .reg_crosses_enabled(cfg.reg_crosses_enabled));
      rv32i_bltu_cg   = new("rv32i_bltu_cg", .reg_crosses_enabled(cfg.reg_crosses_enabled));
      rv32i_bgeu_cg   = new("rv32i_bgeu_cg", .reg_crosses_enabled(cfg.reg_crosses_enabled));

      rv32i_lb_cg     = new("rv32i_lb_cg",
                            .reg_crosses_enabled(cfg.reg_crosses_enabled),
                            .reg_hazards_enabled(cfg.reg_hazards_enabled),
                            .rs1_is_signed(rs1_is_signed[LB]),
                            .immi_is_signed(immi_is_signed[LB]),
                            .rd_is_signed(rd_is_signed[LB]),
                            .align_halfword(0),
                            .align_word(0)
                            );
      rv32i_lh_cg     = new("rv32i_lh_cg",
                            .reg_crosses_enabled(cfg.reg_crosses_enabled),
                            .reg_hazards_enabled(cfg.reg_hazards_enabled),
                            .rs1_is_signed(rs1_is_signed[LH]),
                            .immi_is_signed(immi_is_signed[LH]),
                            .rd_is_signed(rd_is_signed[LH]),
                            .align_halfword(cfg.core_cfg.unaligned_access_supported),
                            .align_word(0));
      rv32i_lw_cg     = new("rv32i_lw_cg",
                            .reg_crosses_enabled(cfg.reg_crosses_enabled),
                            .reg_hazards_enabled(cfg.reg_hazards_enabled),
                            .rs1_is_signed(rs1_is_signed[LW]),
                            .immi_is_signed(immi_is_signed[LW]),
                            .rd_is_signed(rd_is_signed[LW]),
                            .align_halfword(0),
                            .align_word(cfg.core_cfg.unaligned_access_supported));
      rv32i_lbu_cg    = new("rv32i_lbu_cg",
                            .reg_crosses_enabled(cfg.reg_crosses_enabled),
                            .reg_hazards_enabled(cfg.reg_hazards_enabled),
                            .rs1_is_signed(rs1_is_signed[LBU]),
                            .immi_is_signed(immi_is_signed[LBU]),
                            .rd_is_signed(rd_is_signed[LBU]),
                            .align_halfword(0),
                            .align_word(0));
      rv32i_lhu_cg    = new("rv32i_lhu_cg",
                            .reg_crosses_enabled(cfg.reg_crosses_enabled),
                            .reg_hazards_enabled(cfg.reg_hazards_enabled),
                            .rs1_is_signed(rs1_is_signed[LHU]),
                            .immi_is_signed(immi_is_signed[LHU]),
                            .rd_is_signed(rd_is_signed[LHU]),
                            .align_halfword(cfg.core_cfg.unaligned_access_supported),
                            .align_word(0));

      rv32i_sb_cg     = new("rv32i_sb_cg",
                            .reg_crosses_enabled(cfg.reg_crosses_enabled),
                            .align_halfword(0),
                            .align_word(0));
      rv32i_sh_cg     = new("rv32i_sh_cg",
                            .reg_crosses_enabled(cfg.reg_crosses_enabled),
                            .align_halfword(cfg.core_cfg.unaligned_access_supported),
                            .align_word(0));
      rv32i_sw_cg     = new("rv32i_sw_cg",
                            .reg_crosses_enabled(cfg.reg_crosses_enabled),
                            .align_halfword(0),
                            .align_word(cfg.core_cfg.unaligned_access_supported));

      rv32i_addi_cg   = new("rv32i_addi_cg",
                            .reg_crosses_enabled(cfg.reg_crosses_enabled),
                            .reg_hazards_enabled(cfg.reg_hazards_enabled),
                            .rs1_is_signed(rs1_is_signed[ADDI]),
                            .immi_is_signed(immi_is_signed[ADDI]),
                            .rd_is_signed(rd_is_signed[ADDI]));
      rv32i_slti_cg   = new("rv32i_slti_cg",
                            .reg_crosses_enabled(cfg.reg_crosses_enabled),
                            .reg_hazards_enabled(cfg.reg_hazards_enabled),
                            .rs1_is_signed(rs1_is_signed[SLTI]),
                            .immi_is_signed(immi_is_signed[SLTI]),
                            .rd_is_signed(rs1_is_signed[SLTI]));
      rv32i_sltiu_cg  = new("rv32i_sltiu_cg",
                            .reg_crosses_enabled(cfg.reg_crosses_enabled),
                            .reg_hazards_enabled(cfg.reg_hazards_enabled),
                            .rs1_is_signed(rs1_is_signed[SLTIU]),
                            .immi_is_signed(immi_is_signed[SLTIU]),
                            .rd_is_signed(rd_is_signed[SLTIU]));
      rv32i_xori_cg   = new("rv32i_xori_cg",
                            .reg_crosses_enabled(cfg.reg_crosses_enabled),
                            .reg_hazards_enabled(cfg.reg_hazards_enabled),
                            .rs1_is_signed(rs1_is_signed[XORI]),
                            .immi_is_signed(immi_is_signed[XORI]),
                            .rd_is_signed(rd_is_signed[XORI]));
      rv32i_ori_cg    = new("rv32i_ori_cg",
                            .reg_crosses_enabled(cfg.reg_crosses_enabled),
                            .reg_hazards_enabled(cfg.reg_hazards_enabled),
                            .rs1_is_signed(rs1_is_signed[ORI]),
                            .immi_is_signed(immi_is_signed[ORI]),
                            .rd_is_signed(rd_is_signed[ORI]));
      rv32i_andi_cg   = new("rv32i_andi_cg",
                            .reg_crosses_enabled(cfg.reg_crosses_enabled),
                            .reg_hazards_enabled(cfg.reg_hazards_enabled),
                            .rs1_is_signed(rs1_is_signed[ANDI]),
                            .immi_is_signed(immi_is_signed[ANDI]),
                            .rd_is_signed(rd_is_signed[ANDI]));
      rv32i_slli_cg   = new("rv32i_slli_cg",
                            .reg_crosses_enabled(cfg.reg_crosses_enabled),
                            .reg_hazards_enabled(cfg.reg_hazards_enabled),
                            .rs1_is_signed(rs1_is_signed[SLLI]),
                            .immi_is_signed(immi_is_signed[SLLI]),
                            .rd_is_signed(rd_is_signed[SLLI]));
      rv32i_srli_cg   = new("rv32i_srli_cg",
                            .reg_crosses_enabled(cfg.reg_crosses_enabled),
                            .reg_hazards_enabled(cfg.reg_hazards_enabled),
                            .rs1_is_signed(rs1_is_signed[SRLI]),
                            .immi_is_signed(immi_is_signed[SRLI]),
                            .rd_is_signed(rd_is_signed[SRLI]));
      rv32i_srai_cg   = new("rv32i_srai_cg",
                            .reg_crosses_enabled(cfg.reg_crosses_enabled),
                            .reg_hazards_enabled(cfg.reg_hazards_enabled),
                            .rs1_is_signed(rs1_is_signed[SRAI]),
                            .immi_is_signed(immi_is_signed[SRAI]),
                            .rd_is_signed(rd_is_signed[SRAI]));

      rv32i_add_cg    = new("rv32i_add_cg",
                            .reg_crosses_enabled(cfg.reg_crosses_enabled),
                            .reg_hazards_enabled(cfg.reg_hazards_enabled),
                            .rs1_is_signed(rs1_is_signed[ADD]),
                            .rs2_is_signed(rs2_is_signed[ADD]),
                            .rd_is_signed(rd_is_signed[ADD]));
      rv32i_sub_cg    = new("rv32i_sub_cg",
                            .reg_crosses_enabled(cfg.reg_crosses_enabled),
                            .reg_hazards_enabled(cfg.reg_hazards_enabled),
                            .rs1_is_signed(rs1_is_signed[SUB]),
                            .rs2_is_signed(rs2_is_signed[SUB]),
                            .rd_is_signed(rd_is_signed[SUB]));
      rv32i_sll_cg    = new("rv32i_sll_cg",
                            .reg_crosses_enabled(cfg.reg_crosses_enabled),
                            .reg_hazards_enabled(cfg.reg_hazards_enabled),
                            .rs1_is_signed(rs1_is_signed[SLL]),
                            .rs2_is_signed(rs2_is_signed[SLL]),
                            .rd_is_signed(rd_is_signed[SLL]));
      rv32i_slt_cg    = new("rv32i_slt_cg",
                            .reg_crosses_enabled(cfg.reg_crosses_enabled),
                            .reg_hazards_enabled(cfg.reg_hazards_enabled),
                            .rs1_is_signed(rs1_is_signed[SLT]),
                            .rs2_is_signed(rs2_is_signed[SLT]),
                            .rd_is_signed(rd_is_signed[SLT]));
      rv32i_sltu_cg   = new("rv32i_sltu_cg",
                            .reg_crosses_enabled(cfg.reg_crosses_enabled),
                            .reg_hazards_enabled(cfg.reg_hazards_enabled),
                            .rs1_is_signed(rs1_is_signed[SLTU]),
                            .rs2_is_signed(rs2_is_signed[SLTU]),
                            .rd_is_signed(rd_is_signed[SLTU]));
      rv32i_xor_cg    = new("rv32i_xor_cg",
                            .reg_crosses_enabled(cfg.reg_crosses_enabled),
                            .reg_hazards_enabled(cfg.reg_hazards_enabled),
                            .rs1_is_signed(rs1_is_signed[XOR]),
                            .rs2_is_signed(rs2_is_signed[XOR]),
                            .rd_is_signed(rd_is_signed[XOR]));
      rv32i_srl_cg    = new("rv32i_srl_cg",
                            .reg_crosses_enabled(cfg.reg_crosses_enabled),
                            .reg_hazards_enabled(cfg.reg_hazards_enabled),
                            .rs1_is_signed(rs1_is_signed[SRL]),
                            .rs2_is_signed(rs2_is_signed[SRL]),
                            .rd_is_signed(rd_is_signed[SRL]));
      rv32i_sra_cg    = new("rv32i_sra_cg",
                            .reg_crosses_enabled(cfg.reg_crosses_enabled),
                            .reg_hazards_enabled(cfg.reg_hazards_enabled),
                            .rs1_is_signed(rs1_is_signed[SRA]),
                            .rs2_is_signed(rs2_is_signed[SRA]),
                            .rd_is_signed(rd_is_signed[SRA]));
      rv32i_or_cg     = new("rv32i_or_cg",
                            .reg_crosses_enabled(cfg.reg_crosses_enabled),
                            .reg_hazards_enabled(cfg.reg_hazards_enabled),
                            .rs1_is_signed(rs1_is_signed[OR]),
                            .rs2_is_signed(rs2_is_signed[OR]),
                            .rd_is_signed(rd_is_signed[OR]));
      rv32i_and_cg    = new("rv32i_and_cg",
                            .reg_crosses_enabled(cfg.reg_crosses_enabled),
                            .reg_hazards_enabled(cfg.reg_hazards_enabled),
                            .rs1_is_signed(rs1_is_signed[AND]),
                            .rs2_is_signed(rs2_is_signed[AND]),
                            .rd_is_signed(rd_is_signed[AND]));
      rv32i_fence_cg  = new("rv32i_fence_cg",  FENCE);
      rv32i_wfi_cg    = new("rv32i_wfi_cg",    WFI);
      rv32i_mret_cg   = new("rv32i_mret_cg",   MRET);
      rv32i_dret_cg   = new("rv32i_dret_cg",   DRET);
      rv32i_ecall_cg  = new("rv32i_ecall_cg",  ECALL);
      rv32i_ebreak_cg = new("rv32i_ebreak_cg", EBREAK);
    end

    // ----------------------------------------------------------------------------------------
    // M Extension
    // ----------------------------------------------------------------------------------------
    if (cfg.core_cfg.ext_m_supported) begin
      rv32m_mul_cg    = new("rv32m_mul_cg",
                            .reg_crosses_enabled(cfg.reg_crosses_enabled),
                            .reg_hazards_enabled(cfg.reg_hazards_enabled),
                            .rs1_is_signed(rs1_is_signed[MUL]),
                            .rs2_is_signed(rs2_is_signed[MUL]),
                            .rd_is_signed(rd_is_signed[MUL]));
      rv32m_mulh_cg   = new("rv32m_mulh_cg",
                            .reg_crosses_enabled(cfg.reg_crosses_enabled),
                            .reg_hazards_enabled(cfg.reg_hazards_enabled),
                            .rs1_is_signed(rs1_is_signed[MULH]),
                            .rs2_is_signed(rs2_is_signed[MULH]),
                            .rd_is_signed(rd_is_signed[MULH]));
      rv32m_mulhsu_cg = new("rv32m_mulhsu_cg",
                            .reg_crosses_enabled(cfg.reg_crosses_enabled),
                            .reg_hazards_enabled(cfg.reg_hazards_enabled),
                            .rs1_is_signed(rs1_is_signed[MULHSU]),
                            .rs2_is_signed(rs2_is_signed[MULHSU]),
                            .rd_is_signed(rd_is_signed[MULHSU]));
      rv32m_mulhu_cg  = new("rv32m_mulhu_cg",
                            .reg_crosses_enabled(cfg.reg_crosses_enabled),
                            .reg_hazards_enabled(cfg.reg_hazards_enabled),
                            .rs1_is_signed(rs1_is_signed[MULHU]),
                            .rs2_is_signed(rs2_is_signed[MULHU]),
                            .rd_is_signed(rd_is_signed[MULHU]));
      rv32m_div_cg    = new("rv32m_div_cg",
                            .reg_crosses_enabled(cfg.reg_crosses_enabled),
                            .reg_hazards_enabled(cfg.reg_hazards_enabled),
                            .rs1_is_signed(rs1_is_signed[DIV]),
                            .rs2_is_signed(rs2_is_signed[DIV]),
                            .rd_is_signed(rd_is_signed[DIV]));
      rv32m_div_results_cg = new("rv32m_div_results_cg",
                                 .check_overflow(1));
      rv32m_divu_cg   = new("rv32m_divu_cg",
                            .reg_crosses_enabled(cfg.reg_crosses_enabled),
                            .reg_hazards_enabled(cfg.reg_hazards_enabled),
                            .rs1_is_signed(rs1_is_signed[DIVU]),
                            .rs2_is_signed(rs2_is_signed[DIVU]),
                            .rd_is_signed(rd_is_signed[DIVU]));
      rv32m_divu_results_cg = new("rv32m_divu_results_cg",
                                  .check_overflow(0));
      rv32m_rem_cg    = new("rv32m_rem_cg",
                            .reg_crosses_enabled(cfg.reg_crosses_enabled),
                            .reg_hazards_enabled(cfg.reg_hazards_enabled),
                            .rs1_is_signed(rs1_is_signed[REM]),
                            .rs2_is_signed(rs2_is_signed[REM]),
                            .rd_is_signed(rd_is_signed[REM]));
      rv32m_rem_results_cg = new("rv32m_rem_results_cg",
                                 .check_overflow(1));
      rv32m_remu_cg   = new("rv32m_remu_cg",
                            .reg_crosses_enabled(cfg.reg_crosses_enabled),
                            .reg_hazards_enabled(cfg.reg_hazards_enabled),
                            .rs1_is_signed(rs1_is_signed[REMU]),
                            .rs2_is_signed(rs2_is_signed[REMU]),
                            .rd_is_signed(rd_is_signed[REMU]));
      rv32m_remu_results_cg = new("rv32m_remu_results_cg",
                                  .check_overflow(0));
    end

    // ----------------------------------------------------------------------------------------
    // C Extension
    // ----------------------------------------------------------------------------------------

    if (cfg.core_cfg.ext_c_supported) begin
      rv32c_addi_cg     = new("rv32c_addi_cg",
                              .rs1_is_signed(rs1_is_signed[C_ADDI]),
                              .imm_is_signed(c_imm_is_signed[C_ADDI]),
                              .rd_is_signed(rd_is_signed[C_ADDI]),
                              .imm_is_nonzero(c_imm_is_nonzero[C_ADDI]),
                              .has_rs1(c_has_rs1[C_ADDI]),
                              .tie_rdrs1_x2(0));
      rv32c_addi16sp_cg = new("rv32c_addi16sp_cg",
                              .rs1_is_signed(rs1_is_signed[C_ADDI16SP]),
                              .imm_is_signed(c_imm_is_signed[C_ADDI16SP]),
                              .rd_is_signed(rd_is_signed[C_ADDI16SP]),
                              .imm_is_nonzero(c_imm_is_nonzero[C_ADDI16SP]),
                              .has_rs1(c_has_rs1[C_ADDI16SP]),
                              .tie_rdrs1_x2(1));
      rv32c_slli_cg     = new("rv32c_slli_cg",
                              .rs1_is_signed(rs1_is_signed[C_SLLI]),
                              .rd_is_signed(rd_is_signed[C_SLLI]));
      rv32c_lwsp_cg     = new("rv32c_lwsp_cg",
                              .rs1_is_signed (rs1_is_signed   [C_LWSP]),
                              .imm_is_signed (c_imm_is_signed [C_LWSP]),
                              .rd_is_signed  (rd_is_signed    [C_LWSP]),
                              .imm_is_nonzero(c_imm_is_nonzero[C_LWSP]),
                              .has_rs1       (c_has_rs1       [C_LWSP]),
                              .tie_rdrs1_x2(0));
      rv32c_li_cg       = new("rv32c_li_cg");
      rv32c_lui_cg      = new("rv32c_lui_cg");

      rv32c_mv_cg       = new("rv32c_mv_cg",
                              .reg_crosses_enabled(cfg.reg_crosses_enabled),
                              .reg_hazards_enabled(cfg.reg_hazards_enabled),
                              .rdrs1_is_signed(0),
                              .has_rs1(c_has_rs1[C_MV]),
                              .rs2_is_signed(0));
      rv32c_add_cg      = new("rv32c_add_cg",
                              .reg_crosses_enabled(cfg.reg_crosses_enabled),
                              .reg_hazards_enabled(cfg.reg_hazards_enabled),
                              .rdrs1_is_signed(1),
                              .has_rs1(c_has_rs1[C_ADD]),
                              .rs2_is_signed(1));
      rv32c_jr_cg       = new("rv32c_jr_cg",
                              .reg_crosses_enabled(cfg.reg_crosses_enabled),
                              .reg_hazards_enabled(cfg.reg_hazards_enabled),
                              .rs1_is_signed(0));
      rv32c_jalr_cg     = new("rv32c_jalr_cg",
                              .reg_crosses_enabled(cfg.reg_crosses_enabled),
                              .reg_hazards_enabled(cfg.reg_hazards_enabled),
                              .rs1_is_signed(0));

      rv32c_swsp_cg     = new("rv32c_swsp_cg",
                              .rs2_is_signed(0),
                              .imm_is_signed(0));

      rv32c_addi4spn_cg = new("rv32c_addi4spn_cg");

      rv32c_lw_cg       = new("rv32c_lw_cg",
                              .reg_crosses_enabled(cfg.reg_crosses_enabled),
                              .reg_hazards_enabled(cfg.reg_hazards_enabled),
                              .rs1_is_signed(rs1_is_signed[C_LW]),
                              .imm_is_signed(c_imm_is_signed[C_LW]));

      rv32c_sw_cg       = new("rv32c_sw_cg",
                              .reg_crosses_enabled(cfg.reg_crosses_enabled),
                              .rs1_is_signed(rs1_is_signed[C_SW]),
                              .rs2_is_signed(rs2_is_signed[C_SW]),
                              .imm_is_signed(c_imm_is_signed[C_SW]));

      rv32c_and_cg      = new("rv32c_and_cg",
                              .reg_crosses_enabled(cfg.reg_crosses_enabled),
                              .reg_hazards_enabled(cfg.reg_hazards_enabled),
                              .rs1_is_signed(rs1_is_signed[C_AND]),
                              .rs2_is_signed(rs2_is_signed[C_AND]),
                              .rd_is_signed(rd_is_signed[C_AND]));
      rv32c_or_cg       = new("rv32c_or_cg",
                              .reg_crosses_enabled(cfg.reg_crosses_enabled),
                              .reg_hazards_enabled(cfg.reg_hazards_enabled),
                              .rs1_is_signed(rs1_is_signed[C_OR]),
                              .rs2_is_signed(rs2_is_signed[C_OR]),
                              .rd_is_signed(rd_is_signed[C_OR]));
      rv32c_xor_cg      = new("rv32c_xor_cg",
                              .reg_crosses_enabled(cfg.reg_crosses_enabled),
                              .reg_hazards_enabled(cfg.reg_hazards_enabled),
                              .rs1_is_signed(rs1_is_signed[C_XOR]),
                              .rs2_is_signed(rs2_is_signed[C_XOR]),
                              .rd_is_signed(rd_is_signed[C_XOR]));
      rv32c_sub_cg      = new("rv32c_sub_cg",
                              .reg_crosses_enabled(cfg.reg_crosses_enabled),
                              .reg_hazards_enabled(cfg.reg_hazards_enabled),
                              .rs1_is_signed(rs1_is_signed[C_SUB]),
                              .rs2_is_signed(rs2_is_signed[C_SUB]),
                              .rd_is_signed(rd_is_signed[C_SUB]));

      rv32c_beqz_cg     = new("rv32c_beqz_cg",
                              .rs1_is_signed(rs1_is_signed[C_BEQZ]),
                              .imm_is_signed(c_imm_is_signed[C_BEQZ]));
      rv32c_bnez_cg     = new("rv32c_bnez_cg",
                              .rs1_is_signed(rs1_is_signed[C_BNEZ]),
                              .imm_is_signed(c_imm_is_signed[C_BNEZ]));
      rv32c_andi_cg     = new("rv32c_andi_cg",
                              .rs1_is_signed(rs1_is_signed[C_ANDI]),
                              .imm_is_signed(c_imm_is_signed[C_ANDI]));
      rv32c_srli_cg     = new("rv32c_srli_cg",
                              .rs1_is_signed(rs1_is_signed[C_SRLI]));
      rv32c_srai_cg     = new("rv32c_srai_cg",
                              .rs1_is_signed(rs1_is_signed[C_SRAI]));

      rv32c_j_cg        = new("rv32c_j_cg",
                              .imm_is_signed(c_imm_is_signed[C_J]));
      rv32c_jal_cg      = new("rv32c_jal_cg",
                              .imm_is_signed(c_imm_is_signed[C_JAL]));

      rv32c_ebreak_cg   = new("rv32c_ebreak_cg", C_EBREAK);
      rv32c_nop_cg      = new("rv32c_nop_cg", C_NOP);
    end

    // ----------------------------------------------------------------------------------------
    // Zicsr Extension
    // ----------------------------------------------------------------------------------------
    if (cfg.core_cfg.ext_zicsr_supported) begin
      rv32zicsr_csrrw_cg  = new("rv32zicsr_csrrw_cg", cfg.core_cfg.unsupported_csr_mask,
                                .reg_crosses_enabled(cfg.reg_crosses_enabled),
                                .reg_hazards_enabled(cfg.reg_hazards_enabled));
      rv32zicsr_csrrs_cg  = new("rv32zicsr_csrrs_cg", cfg.core_cfg.unsupported_csr_mask,
                                .reg_crosses_enabled(cfg.reg_crosses_enabled),
                                .reg_hazards_enabled(cfg.reg_hazards_enabled));
      rv32zicsr_csrrc_cg  = new("rv32zicsr_csrrc_cg", cfg.core_cfg.unsupported_csr_mask,
                                .reg_crosses_enabled(cfg.reg_crosses_enabled),
                                .reg_hazards_enabled(cfg.reg_hazards_enabled));
      rv32zicsr_csrrwi_cg = new("rv32zicsr_csrrwi_cg", cfg.core_cfg.unsupported_csr_mask,
                                .reg_crosses_enabled(cfg.reg_crosses_enabled));
      rv32zicsr_csrrsi_cg = new("rv32zicsr_csrrsi_cg", cfg.core_cfg.unsupported_csr_mask,
                                .reg_crosses_enabled(cfg.reg_crosses_enabled));
      rv32zicsr_csrrci_cg = new("rv32zicsr_csrrci_cg", cfg.core_cfg.unsupported_csr_mask,
                                .reg_crosses_enabled(cfg.reg_crosses_enabled));
    end

    // ----------------------------------------------------------------------------------------
    // Zifence Extension
    // ----------------------------------------------------------------------------------------
    if (cfg.core_cfg.ext_zifencei_supported) begin
      rv32zifencei_fence_i_cg = new("rv32zifencei_fence_i_cg", FENCE_I);
    end

    // ----------------------------------------------------------------------------------------
    // A Extension
    // ----------------------------------------------------------------------------------------
    if (cfg.core_cfg.ext_a_supported) begin
      rv32a_lr_w_cg = new("rv32a_lr_w_cg",
                          .reg_hazards_enabled(cfg.reg_hazards_enabled),
                          .rs1_is_signed(rs1_is_signed[LR_W]),
                          .rd_is_signed(rd_is_signed[LR_W]),
                          .unaligned_access_amo_supported(cfg.core_cfg.unaligned_access_amo_supported));
      rv32a_sc_w_cg = new("rv32a_sc_w_cg",
                          .reg_crosses_enabled(cfg.reg_crosses_enabled),
                          .reg_hazards_enabled(cfg.reg_hazards_enabled),
                          .rs1_is_signed(rs1_is_signed[SC_W]),
                          .rs2_is_signed(rs2_is_signed[SC_W]),
                          .unaligned_access_amo_supported(cfg.core_cfg.unaligned_access_amo_supported));
      rv32a_amoswap_w_cg = new("rv32a_amoswap_w_cg",
                               .reg_crosses_enabled(cfg.reg_crosses_enabled),
                               .reg_hazards_enabled(cfg.reg_hazards_enabled),
                               .rs1_is_signed(rs1_is_signed[AMOSWAP_W]),
                               .rd_is_signed(rd_is_signed[AMOSWAP_W]),
                               .unaligned_access_amo_supported(cfg.core_cfg.unaligned_access_amo_supported));
      rv32a_amoadd_w_cg = new("rv32a_amoadd_w_cg",
                              .reg_crosses_enabled(cfg.reg_crosses_enabled),
                              .reg_hazards_enabled(cfg.reg_hazards_enabled),
                              .rs1_is_signed(rs1_is_signed[AMOADD_W]),
                              .rd_is_signed(rd_is_signed[AMOADD_W]),
                              .unaligned_access_amo_supported(cfg.core_cfg.unaligned_access_amo_supported));
      rv32a_amoxor_w_cg = new("rv32a_amoxor_w_cg",
                              .reg_crosses_enabled(cfg.reg_crosses_enabled),
                              .reg_hazards_enabled(cfg.reg_hazards_enabled),
                              .rs1_is_signed(rs1_is_signed[AMOXOR_W]),
                              .rd_is_signed(rd_is_signed[AMOXOR_W]),
                              .unaligned_access_amo_supported(cfg.core_cfg.unaligned_access_amo_supported));
      rv32a_amoand_w_cg = new("rv32a_amoand_w_cg",
                              .reg_crosses_enabled(cfg.reg_crosses_enabled),
                              .reg_hazards_enabled(cfg.reg_hazards_enabled),
                              .rs1_is_signed(rs1_is_signed[AMOAND_W]),
                              .rd_is_signed(rd_is_signed[AMOAND_W]),
                              .unaligned_access_amo_supported(cfg.core_cfg.unaligned_access_amo_supported));
      rv32a_amoor_w_cg = new("rv32a_amoor_w_cg",
                             .reg_crosses_enabled(cfg.reg_crosses_enabled),
                             .reg_hazards_enabled(cfg.reg_hazards_enabled),
                             .rs1_is_signed(rs1_is_signed[AMOOR_W]),
                             .rd_is_signed(rd_is_signed[AMOOR_W]),
                             .unaligned_access_amo_supported(cfg.core_cfg.unaligned_access_amo_supported));
      rv32a_amomax_w_cg = new("rv32a_max_w_cg",
                              .reg_crosses_enabled(cfg.reg_crosses_enabled),
                              .reg_hazards_enabled(cfg.reg_hazards_enabled),
                              .rs1_is_signed(rs1_is_signed[AMOMAX_W]),
                              .rd_is_signed(rd_is_signed[AMOSWAP_W]),
                              .unaligned_access_amo_supported(cfg.core_cfg.unaligned_access_amo_supported));
      rv32a_amomin_w_cg = new("rv32a_amomin_w_cg",
                               .reg_crosses_enabled(cfg.reg_crosses_enabled),
                               .reg_hazards_enabled(cfg.reg_hazards_enabled),
                               .rs1_is_signed(rs1_is_signed[AMOMIN_W]),
                               .rd_is_signed(rd_is_signed[AMOMIN_W]),
                               .unaligned_access_amo_supported(cfg.core_cfg.unaligned_access_amo_supported));
      rv32a_amomaxu_w_cg = new("rv32a_amomaxu_w_cg",
                               .reg_crosses_enabled(cfg.reg_crosses_enabled),
                               .reg_hazards_enabled(cfg.reg_hazards_enabled),
                               .rs1_is_signed(rs1_is_signed[AMOMAXU_W]),
                               .rd_is_signed(rd_is_signed[AMOMAXU_W]),
                               .unaligned_access_amo_supported(cfg.core_cfg.unaligned_access_amo_supported));
      rv32a_amominu_w_cg = new("rv32a_amominu_w_cg",
                               .reg_crosses_enabled(cfg.reg_crosses_enabled),
                               .reg_hazards_enabled(cfg.reg_hazards_enabled),
                               .rs1_is_signed(rs1_is_signed[AMOMINU_W]),
                               .rd_is_signed(rd_is_signed[AMOMINU_W]),
                               .unaligned_access_amo_supported(cfg.core_cfg.unaligned_access_amo_supported));
    end

    // ----------------------------------------------------------------------------------------
    // Zba Extension
    // ----------------------------------------------------------------------------------------
    if (cfg.core_cfg.ext_zba_supported) begin
      rv32zba_sh1add_cg = new("rv32zba_sh1add_cg",
                               .reg_crosses_enabled(cfg.reg_crosses_enabled),
                               .reg_hazards_enabled(cfg.reg_hazards_enabled),
                               .rs1_is_signed(rs1_is_signed[SH1ADD]),
                               .rs2_is_signed(rs2_is_signed[SH1ADD]),
                               .rd_is_signed(rd_is_signed[SH1ADD]));
      rv32zba_sh2add_cg = new("rv32zba_sh2add_cg",
                               .reg_crosses_enabled(cfg.reg_crosses_enabled),
                               .reg_hazards_enabled(cfg.reg_hazards_enabled),
                               .rs1_is_signed(rs1_is_signed[SH2ADD]),
                               .rs2_is_signed(rs2_is_signed[SH2ADD]),
                               .rd_is_signed(rd_is_signed[SH2ADD]));
      rv32zba_sh3add_cg = new("rv32zba_sh3add_cg",
                               .reg_crosses_enabled(cfg.reg_crosses_enabled),
                               .reg_hazards_enabled(cfg.reg_hazards_enabled),
                               .rs1_is_signed(rs1_is_signed[SH3ADD]),
                               .rs2_is_signed(rs2_is_signed[SH3ADD]),
                               .rd_is_signed(rd_is_signed[SH3ADD]));
    end

    // ----------------------------------------------------------------------------------------
    // Zbb Extension
    // ----------------------------------------------------------------------------------------
    if (cfg.core_cfg.ext_zbb_supported) begin
      rv32zbb_clz_cg = new("rv32zbb_clz_cg",
                           .reg_crosses_enabled(cfg.reg_crosses_enabled),
                           .reg_hazards_enabled(cfg.reg_hazards_enabled),
                           .rs_is_signed(rs1_is_signed[CLZ]),
                           .rd_is_signed(rd_is_signed[CLZ]));
      rv32zbb_ctz_cg = new("rv32zbb_ctz_cg",
                           .reg_crosses_enabled(cfg.reg_crosses_enabled),
                           .reg_hazards_enabled(cfg.reg_hazards_enabled),
                           .rs_is_signed(rs1_is_signed[CTZ]),
                           .rd_is_signed(rd_is_signed[CTZ]));
      rv32zbb_cpop_cg = new("rv32zbb_cpop_cg",
                            .reg_crosses_enabled(cfg.reg_crosses_enabled),
                            .reg_hazards_enabled(cfg.reg_hazards_enabled),
                            .rs_is_signed(rs1_is_signed[CPOP]),
                            .rd_is_signed(rd_is_signed[CPOP]));
      rv32zbb_min_cg = new("rv32zbb_min_cg",
                           .reg_crosses_enabled(cfg.reg_crosses_enabled),
                           .reg_hazards_enabled(cfg.reg_hazards_enabled),
                           .rs1_is_signed(rs1_is_signed[MIN]),
                           .rs2_is_signed(rs2_is_signed[MIN]),
                           .rd_is_signed(rd_is_signed[MIN]));
      rv32zbb_minu_cg = new("rv32zbb_minu_cg",
                            .reg_crosses_enabled(cfg.reg_crosses_enabled),
                            .reg_hazards_enabled(cfg.reg_hazards_enabled),
                            .rs1_is_signed(rs1_is_signed[MINU]),
                            .rs2_is_signed(rs2_is_signed[MINU]),
                            .rd_is_signed(rd_is_signed[MINU]));
      rv32zbb_max_cg = new("rv32zbb_max_cg",
                           .reg_crosses_enabled(cfg.reg_crosses_enabled),
                           .reg_hazards_enabled(cfg.reg_hazards_enabled),
                           .rs1_is_signed(rs1_is_signed[MAX]),
                           .rs2_is_signed(rs2_is_signed[MAX]),
                           .rd_is_signed(rd_is_signed[MAX]));
      rv32zbb_maxu_cg = new("rv32zbb_maxu_cg",
                            .reg_crosses_enabled(cfg.reg_crosses_enabled),
                            .reg_hazards_enabled(cfg.reg_hazards_enabled),
                            .rs1_is_signed(rs1_is_signed[MAXU]),
                            .rs2_is_signed(rs2_is_signed[MAXU]),
                            .rd_is_signed(rd_is_signed[MAXU]));
      rv32zbb_sext_b_cg = new("rv32zbb_sext_b_cg",
                              .reg_crosses_enabled(cfg.reg_crosses_enabled),
                              .reg_hazards_enabled(cfg.reg_hazards_enabled),
                              .rs_is_signed(rs1_is_signed[SEXT_B]),
                              .rd_is_signed(rd_is_signed[SEXT_B]));
      rv32zbb_sext_h_cg = new("rv32zbb_sext_h_cg",
                              .reg_crosses_enabled(cfg.reg_crosses_enabled),
                              .reg_hazards_enabled(cfg.reg_hazards_enabled),
                              .rs_is_signed(rs1_is_signed[SEXT_H]),
                              .rd_is_signed(rd_is_signed[SEXT_H]));
      rv32zbb_zext_h_cg = new("rv32zbb_zext_h_cg",
                              .reg_crosses_enabled(cfg.reg_crosses_enabled),
                              .reg_hazards_enabled(cfg.reg_hazards_enabled),
                              .rs_is_signed(rs1_is_signed[ZEXT_H]),
                              .rd_is_signed(rd_is_signed[ZEXT_H]));
      rv32zbb_andn_cg = new("rv32zbb_andn_cg",
                            .reg_crosses_enabled(cfg.reg_crosses_enabled),
                            .reg_hazards_enabled(cfg.reg_hazards_enabled),
                            .rs1_is_signed(rs1_is_signed[ANDN]),
                            .rs2_is_signed(rs2_is_signed[ANDN]),
                            .rd_is_signed(rd_is_signed[ANDN]));
      rv32zbb_orn_cg = new("rv32zbb_orn_cg",
                            .reg_crosses_enabled(cfg.reg_crosses_enabled),
                            .reg_hazards_enabled(cfg.reg_hazards_enabled),
                            .rs1_is_signed(rs1_is_signed[ORN]),
                            .rs2_is_signed(rs2_is_signed[ORN]),
                            .rd_is_signed(rd_is_signed[ORN]));
      rv32zbb_xnor_cg = new("rv32zbb_xnor_cg",
                            .reg_crosses_enabled(cfg.reg_crosses_enabled),
                            .reg_hazards_enabled(cfg.reg_hazards_enabled),
                            .rs1_is_signed(rs1_is_signed[XNOR]),
                            .rs2_is_signed(rs2_is_signed[XNOR]),
                            .rd_is_signed(rd_is_signed[XNOR]));
      rv32zbb_rol_cg = new("rv32zbb_rol_cg",
                           .reg_crosses_enabled(cfg.reg_crosses_enabled),
                           .reg_hazards_enabled(cfg.reg_hazards_enabled),
                           .rs1_is_signed(rs1_is_signed[ROL]),
                           .rs2_is_signed(rs2_is_signed[ROL]),
                           .rd_is_signed(rd_is_signed[ROL]));
      rv32zbb_ror_cg = new("rv32zbb_ror_cg",
                           .reg_crosses_enabled(cfg.reg_crosses_enabled),
                           .reg_hazards_enabled(cfg.reg_hazards_enabled),
                           .rs1_is_signed(rs1_is_signed[ROR]),
                           .rs2_is_signed(rs2_is_signed[ROR]),
                           .rd_is_signed(rd_is_signed[ROR]));
      rv32zbb_rori_cg = new("rv32zbb_rori_cg",
                            .reg_crosses_enabled(cfg.reg_crosses_enabled),
                            .reg_hazards_enabled(cfg.reg_hazards_enabled),
                            .rs_is_signed(rs1_is_signed[RORI]),
                            .rd_is_signed(rd_is_signed[RORI]));
      rv32zbb_rev8_cg = new("rv32zbb_rev8_cg",
                            .reg_crosses_enabled(cfg.reg_crosses_enabled),
                            .reg_hazards_enabled(cfg.reg_hazards_enabled),
                            .rs_is_signed(rs1_is_signed[REV8]),
                            .rd_is_signed(rd_is_signed[REV8]));
      rv32zbb_orc_b_cg = new("rv32zbb_orc_b_cg",
                             .reg_crosses_enabled(cfg.reg_crosses_enabled),
                             .reg_hazards_enabled(cfg.reg_hazards_enabled),
                             .rs_is_signed(rs1_is_signed[ORC_B]),
                             .rd_is_signed(rd_is_signed[ORC_B]));
    end

    // ----------------------------------------------------------------------------------------
    // Zbc Extension
    // ----------------------------------------------------------------------------------------
    if (cfg.core_cfg.ext_zbc_supported) begin
      rv32zbc_clmul_cg = new("rv32zbc_clmul_cg",
                             .reg_crosses_enabled(cfg.reg_crosses_enabled),
                             .reg_hazards_enabled(cfg.reg_hazards_enabled),
                             .rs1_is_signed(rs1_is_signed[CLMUL]),
                             .rs2_is_signed(rs2_is_signed[CLMUL]),
                             .rd_is_signed(rd_is_signed[CLMUL]));
      rv32zbc_clmulh_cg = new("rv32zbc_clmulh_cg",
                              .reg_crosses_enabled(cfg.reg_crosses_enabled),
                              .reg_hazards_enabled(cfg.reg_hazards_enabled),
                              .rs1_is_signed(rs1_is_signed[CLMULH]),
                              .rs2_is_signed(rs2_is_signed[CLMULH]),
                              .rd_is_signed(rd_is_signed[CLMULH]));
      rv32zbc_clmulr_cg = new("rv32zbc_clmulr_cg",
                              .reg_crosses_enabled(cfg.reg_crosses_enabled),
                              .reg_hazards_enabled(cfg.reg_hazards_enabled),
                              .rs1_is_signed(rs1_is_signed[CLMULR]),
                              .rs2_is_signed(rs2_is_signed[CLMULR]),
                              .rd_is_signed(rd_is_signed[CLMULR]));
    end

    // ----------------------------------------------------------------------------------------
    // Zbs Extension
    // ----------------------------------------------------------------------------------------
    if (cfg.core_cfg.ext_zbs_supported) begin
      rv32zbs_bset_cg = new("rv32zbs_bset_cg",
                            .reg_crosses_enabled(cfg.reg_crosses_enabled),
                            .reg_hazards_enabled(cfg.reg_hazards_enabled),
                            .rs1_is_signed(rs1_is_signed[BSET]),
                            .rs2_is_signed(rs2_is_signed[BSET]),
                            .rd_is_signed(rd_is_signed[BSET]));
      rv32zbs_bseti_cg = new("rv32zbs_bseti_cg",
                             .reg_crosses_enabled(cfg.reg_crosses_enabled),
                             .reg_hazards_enabled(cfg.reg_hazards_enabled),
                             .rs_is_signed(rs1_is_signed[BSETI]),
                             .rd_is_signed(rd_is_signed[BSETI]));
      rv32zbs_bclr_cg = new("rv32zbs_bclr_cg",
                            .reg_crosses_enabled(cfg.reg_crosses_enabled),
                            .reg_hazards_enabled(cfg.reg_hazards_enabled),
                            .rs1_is_signed(rs1_is_signed[BCLR]),
                            .rs2_is_signed(rs2_is_signed[BCLR]),
                            .rd_is_signed(rd_is_signed[BCLR]));
      rv32zbs_bclri_cg = new("rv32zbs_bclri_cg",
                             .reg_crosses_enabled(cfg.reg_crosses_enabled),
                             .reg_hazards_enabled(cfg.reg_hazards_enabled),
                             .rs_is_signed(rs1_is_signed[BCLRI]),
                             .rd_is_signed(rd_is_signed[BCLRI]));
      rv32zbs_binv_cg = new("rv32zbs_binv_cg",
                            .reg_crosses_enabled(cfg.reg_crosses_enabled),
                            .reg_hazards_enabled(cfg.reg_hazards_enabled),
                            .rs1_is_signed(rs1_is_signed[BINV]),
                            .rs2_is_signed(rs2_is_signed[BINV]),
                            .rd_is_signed(rd_is_signed[BINV]));
      rv32zbs_binvi_cg = new("rv32zbs_binvi_cg",
                             .reg_crosses_enabled(cfg.reg_crosses_enabled),
                             .reg_hazards_enabled(cfg.reg_hazards_enabled),
                             .rs_is_signed(rs1_is_signed[BINVI]),
                             .rd_is_signed(rd_is_signed[BINVI]));
      rv32zbs_bext_cg = new("rv32zbs_bext_cg",
                            .reg_crosses_enabled(cfg.reg_crosses_enabled),
                            .reg_hazards_enabled(cfg.reg_hazards_enabled),
                            .rs1_is_signed(rs1_is_signed[BEXT]),
                            .rs2_is_signed(rs2_is_signed[BEXT]),
                            .rd_is_signed(rd_is_signed[BEXT]));
      rv32zbs_bexti_cg = new("rv32zbs_bexti_cg",
                             .reg_crosses_enabled(cfg.reg_crosses_enabled),
                             .reg_hazards_enabled(cfg.reg_hazards_enabled),
                             .rs_is_signed(rs1_is_signed[BEXTI]),
                             .rd_is_signed(rd_is_signed[BEXTI]));
    end

    // ----------------------------------------------------------------------------------------
    // ISA "Sequential" coverage
    // ----------------------------------------------------------------------------------------
    rv32_seq_cg = new("rev32_seq_cg",
                      .seq_instr_group_x2_enabled(cfg.seq_instr_group_x2_enabled),
                      .seq_instr_group_x3_enabled(cfg.seq_instr_group_x3_enabled),
                      .seq_instr_group_x4_enabled(cfg.seq_instr_group_x4_enabled),
                      .seq_instr_x2_enabled(cfg.seq_instr_x2_enabled),
                      .cfg_illegal_csr(cfg.core_cfg.unsupported_csr_mask),
                      .unaligned_access_supported(cfg.core_cfg.unaligned_access_supported),
                      .ext_m_supported(cfg.core_cfg.ext_m_supported),
                      .ext_c_supported(cfg.core_cfg.ext_c_supported),
                      .ext_a_supported(cfg.core_cfg.ext_a_supported),
                      .ext_zba_supported(cfg.core_cfg.ext_zba_supported),
                      .ext_zbb_supported(cfg.core_cfg.ext_zbb_supported),
                      .ext_zbc_supported(cfg.core_cfg.ext_zbc_supported),
                      .ext_zbs_supported(cfg.core_cfg.ext_zbs_supported)
                      );
  end

  mon_trn_fifo = new("mon_trn_fifo", this);

endfunction : build_phase


task uvma_isacov_cov_model_c::run_phase(uvm_phase phase);

  super.run_phase(phase);

  forever begin
    uvma_isacov_mon_trn_c mon_trn;

    mon_trn_fifo.get(mon_trn);
    if (cfg.enabled && cfg.cov_model_enabled) begin
      sample (mon_trn.instr);
    end
  end

endtask : run_phase


function void uvma_isacov_cov_model_c::sample (uvma_isacov_instr_c instr);

  logic have_sampled = 0;
  logic is_ecall_or_ebreak =
    ( instr.trap[ 8:3] ==  8)                              ||  // Ecall U-mode
    ( instr.trap[ 8:3] == 11)                              ||  // Ecall M-mode
    ((instr.trap[ 8:3] ==  3) && (instr.trap[13:12] == 0)) ||  // Ebreak (ebreakm==0)
    ( instr.trap[11:9] ==  1);                                 // Ebreak to* or in D-mode (* ebreakm==1)
  logic is_normal_instr =
    (instr.trap[0] == 0) ||                              // No rvfi_trap
    ((instr.trap[11:9] == 4) && (instr.trap[1] == 0));   // Single-step, without any exception

  if (!have_sampled && is_normal_instr && cfg.core_cfg.ext_i_supported) begin
    have_sampled = 1;
    case (instr.name)
      LUI:   rv32i_lui_cg.sample(instr);
      AUIPC: rv32i_auipc_cg.sample(instr);
      JAL:   rv32i_jal_cg.sample(instr);
      JALR:  rv32i_jalr_cg.sample(instr);

      BEQ:  rv32i_beq_cg.sample(instr);
      BNE:  rv32i_bne_cg.sample(instr);
      BLT:  rv32i_blt_cg.sample(instr);
      BGE:  rv32i_bge_cg.sample(instr);
      BLTU: rv32i_bltu_cg.sample(instr);
      BGEU: rv32i_bgeu_cg.sample(instr);

      LB:  rv32i_lb_cg.sample(instr);
      LH:  rv32i_lh_cg.sample(instr);
      LW:  rv32i_lw_cg.sample(instr);
      LBU: rv32i_lbu_cg.sample(instr);
      LHU: rv32i_lhu_cg.sample(instr);
      SB:  rv32i_sb_cg.sample(instr);
      SH:  rv32i_sh_cg.sample(instr);
      SW:  rv32i_sw_cg.sample(instr);

      ADDI:  rv32i_addi_cg.sample(instr);
      SLTI:  rv32i_slti_cg.sample(instr);
      SLTIU: rv32i_sltiu_cg.sample(instr);
      XORI:  rv32i_xori_cg.sample(instr);
      ORI:   rv32i_ori_cg.sample(instr);
      ANDI:  rv32i_andi_cg.sample(instr);
      SLLI:  rv32i_slli_cg.sample(instr);
      SRLI:  rv32i_srli_cg.sample(instr);
      SRAI:  rv32i_srai_cg.sample(instr);

      ADD:  rv32i_add_cg.sample(instr);
      SUB:  rv32i_sub_cg.sample(instr);
      SLL:  rv32i_sll_cg.sample(instr);
      SLT:  rv32i_slt_cg.sample(instr);
      SLTU: rv32i_sltu_cg.sample(instr);
      XOR:  rv32i_xor_cg.sample(instr);
      SRL:  rv32i_srl_cg.sample(instr);
      SRA:  rv32i_sra_cg.sample(instr);
      OR:   rv32i_or_cg.sample(instr);
      AND:  rv32i_and_cg.sample(instr);

      FENCE:  rv32i_fence_cg.sample(instr);
      WFI:    rv32i_wfi_cg.sample(instr);
      MRET:   rv32i_mret_cg.sample(instr);
      DRET:   rv32i_dret_cg.sample(instr);

      default: have_sampled = 0;
    endcase
  end else if (!have_sampled && is_ecall_or_ebreak && cfg.core_cfg.ext_i_supported) begin
    have_sampled = 1;
    case (instr.name)
      // Ecall and ebreak will trap
      ECALL:  rv32i_ecall_cg.sample(instr);
      EBREAK: rv32i_ebreak_cg.sample(instr);

      default: have_sampled = 0;
    endcase
  end

  if (!have_sampled && is_normal_instr && cfg.core_cfg.ext_m_supported) begin
    have_sampled = 1;
    case (instr.name)
      MUL:     rv32m_mul_cg.sample(instr);
      MULH:    rv32m_mulh_cg.sample(instr);
      MULHSU:  rv32m_mulhsu_cg.sample(instr);
      MULHU:   rv32m_mulhu_cg.sample(instr);
      DIV: begin
               rv32m_div_results_cg.sample(instr);
               rv32m_div_cg.sample(instr);

      end
      DIVU: begin
               rv32m_divu_cg.sample(instr);
               rv32m_divu_results_cg.sample(instr);
      end
      REM: begin
               rv32m_rem_cg.sample(instr);
               rv32m_rem_results_cg.sample(instr);
      end
      REMU: begin
               rv32m_remu_cg.sample(instr);
               rv32m_remu_results_cg.sample(instr);
      end
      default: have_sampled = 0;
    endcase
  end

  if (!have_sampled && is_normal_instr && cfg.core_cfg.ext_c_supported) begin
    have_sampled = 1;
    case (instr.name)
      C_ADDI:     rv32c_addi_cg.sample(instr);
      C_ADDI16SP: rv32c_addi16sp_cg.sample(instr);
      C_LWSP:     rv32c_lwsp_cg.sample(instr);
      C_SLLI:     rv32c_slli_cg.sample(instr);
      C_LI:       rv32c_li_cg.sample(instr);
      C_LUI:      rv32c_lui_cg.sample(instr);

      C_JR:       rv32c_jr_cg.sample(instr);
      C_MV:       rv32c_mv_cg.sample(instr);
      C_JALR:     rv32c_jalr_cg.sample(instr);
      C_ADD:      rv32c_add_cg.sample(instr);

      C_SWSP:     rv32c_swsp_cg.sample(instr);

      C_ADDI4SPN: rv32c_addi4spn_cg.sample(instr);

      C_LW:       rv32c_lw_cg.sample(instr);

      C_SW:       rv32c_sw_cg.sample(instr);

      C_SUB:      rv32c_sub_cg.sample(instr);
      C_XOR:      rv32c_xor_cg.sample(instr);
      C_OR:       rv32c_or_cg.sample(instr);
      C_AND:      rv32c_and_cg.sample(instr);

      C_BEQZ:     rv32c_beqz_cg.sample(instr);
      C_BNEZ:     rv32c_bnez_cg.sample(instr);
      C_SRLI:     rv32c_srli_cg.sample(instr);
      C_SRAI:     rv32c_srai_cg.sample(instr);
      C_ANDI:     rv32c_andi_cg.sample(instr);

      C_J:        rv32c_j_cg.sample(instr);
      C_JAL:      rv32c_jal_cg.sample(instr);

      C_NOP:      rv32c_nop_cg.sample(instr);

      default: have_sampled = 0;
    endcase
  end else if (!have_sampled && is_ecall_or_ebreak && cfg.core_cfg.ext_c_supported) begin
    have_sampled = 1;
    case (instr.name)
      // Ebreak will trap
      C_EBREAK:   rv32c_ebreak_cg.sample(instr);

      default: have_sampled = 0;
    endcase
  end

  if (!have_sampled && is_normal_instr && cfg.core_cfg.ext_zicsr_supported) begin
    have_sampled = 1;
    case (instr.name)
      CSRRW:   rv32zicsr_csrrw_cg.sample(instr);
      CSRRS:   rv32zicsr_csrrs_cg.sample(instr);
      CSRRC:   rv32zicsr_csrrc_cg.sample(instr);
      CSRRWI:  rv32zicsr_csrrwi_cg.sample(instr);
      CSRRSI:  rv32zicsr_csrrsi_cg.sample(instr);
      CSRRCI:  rv32zicsr_csrrci_cg.sample(instr);
      default: have_sampled = 0;
    endcase
  end

  if (!have_sampled && is_normal_instr && cfg.core_cfg.ext_zifencei_supported) begin
    have_sampled = 1;
    case (instr.name)
      FENCE_I: rv32zifencei_fence_i_cg.sample(instr);
      default: have_sampled = 0;
    endcase
  end

  if (!have_sampled && is_normal_instr && cfg.core_cfg.ext_a_supported) begin
    have_sampled = 1;
    case (instr.name)
      LR_W:      rv32a_lr_w_cg.sample(instr);
      SC_W:      rv32a_sc_w_cg.sample(instr);
      AMOSWAP_W: rv32a_amoswap_w_cg.sample(instr);
      AMOADD_W:  rv32a_amoadd_w_cg.sample(instr);
      AMOAND_W:  rv32a_amoand_w_cg.sample(instr);
      AMOXOR_W:  rv32a_amoxor_w_cg.sample(instr);
      AMOOR_W:   rv32a_amoor_w_cg.sample(instr);
      AMOMAX_W:  rv32a_amomax_w_cg.sample(instr);
      AMOMIN_W:  rv32a_amomin_w_cg.sample(instr);
      AMOMAXU_W: rv32a_amomaxu_w_cg.sample(instr);
      AMOMINU_W: rv32a_amomaxu_w_cg.sample(instr);
      default: have_sampled = 0;
    endcase
  end

  if (!have_sampled && is_normal_instr && cfg.core_cfg.ext_zba_supported) begin
    have_sampled = 1;
    case (instr.name)
      SH1ADD:  rv32zba_sh1add_cg.sample(instr);
      SH2ADD:  rv32zba_sh2add_cg.sample(instr);
      SH3ADD:  rv32zba_sh3add_cg.sample(instr);
      default: have_sampled = 0;
    endcase
  end

  if (!have_sampled && is_normal_instr && cfg.core_cfg.ext_zbb_supported) begin
    have_sampled = 1;
    case (instr.name)
      CLZ:     rv32zbb_clz_cg.sample(instr);
      CTZ:     rv32zbb_ctz_cg.sample(instr);
      CPOP:    rv32zbb_cpop_cg.sample(instr);
      MIN:     rv32zbb_min_cg.sample(instr);
      MAX:     rv32zbb_max_cg.sample(instr);
      MINU:    rv32zbb_minu_cg.sample(instr);
      MAXU:    rv32zbb_maxu_cg.sample(instr);
      SEXT_B:  rv32zbb_sext_b_cg.sample(instr);
      SEXT_H:  rv32zbb_sext_h_cg.sample(instr);
      ZEXT_H:  rv32zbb_zext_h_cg.sample(instr);
      ANDN:    rv32zbb_andn_cg.sample(instr);
      ORN:     rv32zbb_orn_cg.sample(instr);
      XNOR:    rv32zbb_xnor_cg.sample(instr);
      ROR:     rv32zbb_ror_cg.sample(instr);
      RORI:    rv32zbb_rori_cg.sample(instr);
      ROL:     rv32zbb_rol_cg.sample(instr);
      REV8:    rv32zbb_rev8_cg.sample(instr);
      ORC_B:   rv32zbb_orc_b_cg.sample(instr);
      default: have_sampled = 0;
    endcase
  end

  if (!have_sampled && is_normal_instr && cfg.core_cfg.ext_zbc_supported) begin
    have_sampled = 1;
    case (instr.name)
      CLMUL:   rv32zbc_clmul_cg.sample(instr);
      CLMULH:  rv32zbc_clmulh_cg.sample(instr);
      CLMULR:  rv32zbc_clmulr_cg.sample(instr);
      default: have_sampled = 0;
    endcase
  end

  if (!have_sampled && is_normal_instr && cfg.core_cfg.ext_zbs_supported) begin
    have_sampled = 1;
    case (instr.name)
      BSET:    rv32zbs_bset_cg.sample(instr);
      BSETI:   rv32zbs_bseti_cg.sample(instr);
      BCLR:    rv32zbs_bclr_cg.sample(instr);
      BCLRI:   rv32zbs_bclri_cg.sample(instr);
      BINV:    rv32zbs_binv_cg.sample(instr);
      BINVI:   rv32zbs_binvi_cg.sample(instr);
      BEXT:    rv32zbs_bext_cg.sample(instr);
      BEXTI:   rv32zbs_bexti_cg.sample(instr);
      default: have_sampled = 0;
    endcase
  end

  if (!have_sampled && is_normal_instr && instr.name != UNKNOWN) begin
    `uvm_error("ISACOV", $sformatf("Could not sample instruction: %s", instr.name.name()));
  end

  if (have_sampled) begin
    rv32_seq_cg.sample(instr,
                       instr_prev,
                       instr_prev2,
                       instr_prev3,
                       .raw_hazard(is_raw_hazard(instr, instr_prev)),
                       .csr_hazard(is_csr_hazard(instr, instr_prev))
                       );

    // Move instructions down the pipeline
    instr_prev3 = instr_prev2;
    instr_prev2 = instr_prev;
    instr_prev  = instr;
  end

endfunction : sample

function bit uvma_isacov_cov_model_c::is_raw_hazard(uvma_isacov_instr_c instr,
                                                    uvma_isacov_instr_c instr_prev);

  if (instr_prev == null)
    return 0;

  // RAW hazard, destination register in previous is used as source in next register
  if (instr_prev.rd_valid &&
      instr_prev.rd != 0 &&
      (((instr_prev.rd == instr.rs1) && instr.rs1_valid) ||
       ((instr_prev.rd == instr.rs2) && instr.rs2_valid)))
    return 1;

  return 0;
endfunction : is_raw_hazard

function bit uvma_isacov_cov_model_c::is_csr_hazard(uvma_isacov_instr_c instr,
                                                    uvma_isacov_instr_c instr_prev);

  if (instr_prev == null)
    return 0;

  // CSR hazard, previous instruction wrote to a valid CSR
  if (instr_prev.group inside {CSR_GROUP} &&
      instr_prev.is_csr_write() &&
      !cfg.core_cfg.unsupported_csr_mask[instr_prev.csr])
    return 1;

  return 0;
endfunction : is_csr_hazard
