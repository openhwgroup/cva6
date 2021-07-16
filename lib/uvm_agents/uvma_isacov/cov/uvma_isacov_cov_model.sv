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


covergroup cg_rtype(
    string name,     
    bit reg_crosses_enabled,
    bit reg_hazards_enabled,
    bit rs1_is_signed = 1,
    bit rs2_is_signed = 1,
    bit rd_is_signed  = 1
) with function sample (
    uvma_isacov_instr_c instr
);
  option.per_instance = 1;
  option.name = name;

  cp_rs1: coverpoint instr.rs1;
  cp_rs2: coverpoint instr.rs2;
  cp_rd: coverpoint instr.rd;

  cp_rd_rs1_hazard: coverpoint instr.rd {
    ignore_bins IGN_RS1_HAZARD_OFF = {[0:$]} with (!reg_hazards_enabled);
    bins RD[] = {[0:31]} iff (instr.rd == instr.rs1);
  }

  cp_rd_rs2_hazard: coverpoint instr.rd {
    ignore_bins IGN_RS2_HAZARD_OFF = {[0:$]} with (!reg_hazards_enabled);
    bins RD[] = {[0:31]} iff (instr.rd == instr.rs2);
  }

  cross_rd_rs1_rs2: cross cp_rd, cp_rs1, cp_rs2 {
    ignore_bins IGN_OFF = cross_rd_rs1_rs2 with (!reg_crosses_enabled);
  }

  cp_rs1_value: coverpoint instr.rs1_value_type {
    ignore_bins POS_OFF = {POSITIVE} with (!rs1_is_signed);
    ignore_bins NEG_OFF = {NEGATIVE} with (!rs1_is_signed);
    ignore_bins NON_ZERO_OFF = {NON_ZERO} with (rs1_is_signed);
  }

  cp_rs2_value: coverpoint instr.rs2_value_type {
    ignore_bins POS_OFF = {POSITIVE} with (!rs2_is_signed);
    ignore_bins NEG_OFF = {NEGATIVE} with (!rs2_is_signed);
    ignore_bins NON_ZERO_OFF = {NON_ZERO} with (rs2_is_signed);
  }

  cross_rs1_rs2_value: cross cp_rs1_value, cp_rs2_value;

  cp_rd_value: coverpoint instr.rd_value_type {
    ignore_bins POS_OFF = {POSITIVE} with (!rd_is_signed);
    ignore_bins NEG_OFF = {NEGATIVE} with (!rd_is_signed);
    ignore_bins NON_ZERO_OFF = {NON_ZERO} with (rd_is_signed);
  }

  `ISACOV_CP_BITWISE(cp_rs1_toggle, instr.rs1_value, 1)
  `ISACOV_CP_BITWISE(cp_rs2_toggle, instr.rs2_value, 1)
  `ISACOV_CP_BITWISE(cp_rd_toggle,  instr.rd_value,  1)

endgroup : cg_rtype

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
    //ignore_bins IGN_OVERFLOW = {[0:$]} with (!check_overflow);
    bins OFLOW = {32'h8000_0000} with (check_overflow) iff (instr.rs2_value == 32'hffff_ffff);
  }

endgroup : cg_div_special_results

covergroup cg_itype(
    string name, 
    bit reg_crosses_enabled,
    bit reg_hazards_enabled,
    bit rs1_is_signed = 1,
    bit immi_is_signed = 1,
    bit rd_is_signed  = 1
) with function sample (
    uvma_isacov_instr_c instr
);
  option.per_instance = 1;
  option.name = name;

  cp_rs1: coverpoint instr.rs1;
  cp_rd: coverpoint instr.rd;

  cp_rd_rs1_hazard: coverpoint instr.rd {
    ignore_bins IGN_RS1_HAZARD_OFF = {[0:$]} with (!reg_hazards_enabled);
    bins RD[] = {[0:31]} iff (instr.rd == instr.rs1);
  }

  cross_rd_rs1: cross cp_rd, cp_rs1 {
    ignore_bins IGN_OFF = cross_rd_rs1 with (!reg_crosses_enabled);
  }

  cp_rs1_value: coverpoint instr.rs1_value_type {
    ignore_bins POS_OFF = {POSITIVE} with (!rs1_is_signed);
    ignore_bins NEG_OFF = {NEGATIVE} with (!rs1_is_signed);
    ignore_bins NON_ZERO_OFF = {NON_ZERO} with (rs1_is_signed);
  }

  cp_immi_value: coverpoint instr.immi_value_type {
    ignore_bins POS_OFF = {POSITIVE} with (!immi_is_signed);
    ignore_bins NEG_OFF = {NEGATIVE} with (!immi_is_signed);
    ignore_bins NON_ZERO_OFF = {NON_ZERO} with (immi_is_signed);
  }

  cross_rs1_immi_value: cross cp_rs1_value, cp_immi_value;

  cp_rd_value: coverpoint instr.rd_value_type {
    ignore_bins POS_OFF = {POSITIVE} with (!rd_is_signed);
    ignore_bins NEG_OFF = {NEGATIVE} with (!rd_is_signed);
    ignore_bins NON_ZERO_OFF = {NON_ZERO} with (rd_is_signed);
  }

  `ISACOV_CP_BITWISE(cp_rs1_toggle,  instr.rs1_value, 1)
  `ISACOV_CP_BITWISE_12(cp_imm1_toggle, instr.immi, 1)
  `ISACOV_CP_BITWISE(cp_rd_toggle,   instr.rd_value,  1)

endgroup : cg_itype

covergroup cg_itype_slt (
    string name, 
    bit reg_crosses_enabled,
    bit reg_hazards_enabled,
    bit rs1_is_signed = 1,
    bit immi_is_signed = 1,
    bit rd_is_signed  = 1
) with function sample (
    uvma_isacov_instr_c instr
);
  option.per_instance = 1;
  option.name = name;

  cp_rs1: coverpoint instr.rs1;
  cp_rd: coverpoint instr.rd;

  cp_rd_rs1_hazard: coverpoint instr.rd {
    ignore_bins IGN_RS1_HAZARD_OFF = {[0:$]} with (!reg_hazards_enabled);
    bins RD[] = {[0:31]} iff (instr.rd == instr.rs1);
  }

  cross_rd_rs1: cross cp_rd, cp_rs1 {
    ignore_bins IGN_OFF = cross_rd_rs1 with (!reg_crosses_enabled);
  }

  cp_rs1_value: coverpoint instr.rs1_value_type {
    ignore_bins POS_OFF = {POSITIVE} with (!rs1_is_signed);
    ignore_bins NEG_OFF = {NEGATIVE} with (!rs1_is_signed);
    ignore_bins NON_ZERO_OFF = {NON_ZERO} with (rs1_is_signed);
  }

  cp_immi_value: coverpoint instr.immi_value_type {
    ignore_bins POS_OFF = {POSITIVE} with (!immi_is_signed);
    ignore_bins NEG_OFF = {NEGATIVE} with (!immi_is_signed);
    ignore_bins NON_ZERO_OFF = {NON_ZERO} with (immi_is_signed);
  }

  cross_rs1_immi_value: cross cp_rs1_value, cp_immi_value;

  cp_rd_value: coverpoint instr.rd_value_type {
    bins SLT[] = {[0:1]};
  }

  `ISACOV_CP_BITWISE(cp_rs1_toggle,  instr.rs1_value, 1)
  `ISACOV_CP_BITWISE_12(cp_imm1_toggle, instr.immi, 1)

endgroup : cg_itype_slt

covergroup cg_itype_shift (
    string name, 
    bit reg_crosses_enabled,
    bit reg_hazards_enabled,
    bit rs1_is_signed = 1,
    bit immi_is_signed = 1,
    bit rd_is_signed  = 1
) with function sample (
    uvma_isacov_instr_c instr
);
  option.per_instance = 1;
  option.name = name;

  cp_rs1: coverpoint instr.rs1;
  cp_rd: coverpoint instr.rd;

  cp_rd_rs1_hazard: coverpoint instr.rd {
    ignore_bins IGN_RS1_HAZARD_OFF = {[0:$]} with (!reg_hazards_enabled);
    bins RD[] = {[0:31]} iff (instr.rd == instr.rs1);
  }

  cross_rd_rs1: cross cp_rd, cp_rs1 {
    ignore_bins IGN_OFF = cross_rd_rs1 with (!reg_crosses_enabled);
  }

  cp_rs1_value: coverpoint instr.rs1_value_type {
    ignore_bins POS_OFF = {POSITIVE} with (!rs1_is_signed);
    ignore_bins NEG_OFF = {NEGATIVE} with (!rs1_is_signed);
    ignore_bins NON_ZERO_OFF = {NON_ZERO} with (rs1_is_signed);
  }

  cp_immi_value: coverpoint instr.immi {
    bins SHAMT[] = {[0:31]};
  }

  cross_rs1_immi_value: cross cp_rs1_value, cp_immi_value;

  cp_rd_value: coverpoint instr.rd_value_type {
    ignore_bins POS_OFF = {POSITIVE} with (!rd_is_signed);
    ignore_bins NEG_OFF = {NEGATIVE} with (!rd_is_signed);
    ignore_bins NON_ZERO_OFF = {NON_ZERO} with (rd_is_signed);
  }

  `ISACOV_CP_BITWISE(cp_rs1_toggle,  instr.rs1_value, 1)
  `ISACOV_CP_BITWISE(cp_rd_toggle,   instr.rd_value,  1)

endgroup : cg_itype_shift

covergroup cg_stype(
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
    ignore_bins IGN_OFF = cross_rs1_rs2 with (!reg_crosses_enabled);
  }

  cp_imms_value: coverpoint instr.imms_value_type {
    ignore_bins NON_ZERO_OFF = {NON_ZERO};
  }

  `ISACOV_CP_BITWISE(cp_rs1_toggle, instr.rs1_value, 1)
  `ISACOV_CP_BITWISE(cp_rs2_toggle, instr.rs2_value, 1)
  `ISACOV_CP_BITWISE_12(cp_imms_toggle, instr.imms, 1)

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
    ignore_bins IGN_OFF = cross_rs1_rs2 with (!reg_crosses_enabled);
  }

  cp_imms_value: coverpoint instr.imms_value_type {
    ignore_bins NON_ZERO_OFF = {NON_ZERO};
  }

  `ISACOV_CP_BITWISE(cp_rs1_toggle, instr.rs1_value, 1)
  `ISACOV_CP_BITWISE(cp_rs2_toggle, instr.rs2_value, 1)
  `ISACOV_CP_BITWISE_12(cp_immb_toggle, instr.immb, 1)

endgroup : cg_btype


covergroup cg_utype(string name) with function sample (uvma_isacov_instr_c instr);
  option.per_instance = 1;
  option.name = name;

  cp_rd: coverpoint instr.rd;

  cp_immu_value: coverpoint instr.immu_value_type {
    ignore_bins POS_OFF = {POSITIVE};
    ignore_bins NEG_OFF = {NEGATIVE};
  }

  `ISACOV_CP_BITWISE(cp_rd_toggle, instr.rd_value, 1)
  `ISACOV_CP_BITWISE_20(cp_immu_toggle, instr.immu, 1)

endgroup : cg_utype


covergroup cg_jtype(string name) with function sample (uvma_isacov_instr_c instr);
  option.per_instance = 1;
  option.name = name;

  cp_rd: coverpoint instr.rd;  

  cp_immj_value: coverpoint instr.immu_value_type {
    ignore_bins NON_ZERO_OFF = {NON_ZERO};
  }

  `ISACOV_CP_BITWISE(cp_rd_toggle, instr.rd_value, 1)
  `ISACOV_CP_BITWISE_20(cp_immj_toggle, instr.immj, 1)

endgroup : cg_jtype

covergroup cg_csrtype(
    string name, bit[CSR_MASK_WL-1:0] cfg_illegal_csr, bit reg_crosses_enabled
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

  cross_rd_rs1: cross cp_rd, cp_rs1 {
    ignore_bins IGN_OFF = cross_rd_rs1 with (!reg_crosses_enabled);
  }
endgroup : cg_csrtype

covergroup cg_csritype(
    string name, bit[CSR_MASK_WL-1:0] cfg_illegal_csr, bit reg_crosses_enabled
) with function sample (
    uvma_isacov_instr_c instr
);
  option.per_instance = 1;
  option.name = name;
  
  cp_rd: coverpoint instr.rd;
  cp_csr: coverpoint instr.csr {
    bins CSR[] = {[USTATUS:VLENB]} with (cfg_illegal_csr[item] == 0);
  }
  cp_uimm: coverpoint instr.rs1;
endgroup : cg_csritype

covergroup cg_cr(
    string name, 
    bit reg_crosses_enabled,
    bit reg_hazards_enabled
) with function sample (
    uvma_isacov_instr_c instr
);
  option.per_instance = 1;
  option.name = name;

  cp_c_rdrs1: coverpoint instr.c_rdrs1;
  cp_c_rs2: coverpoint instr.c_rs2;

  cp_rd_rs2_hazard: coverpoint instr.rd {
    ignore_bins IGN_RS2_HAZARD_OFF = {[0:$]} with (!reg_hazards_enabled);
    bins RD[] = {[0:31]} iff (instr.rd == instr.rs2);
  }

  cross_rdrs1_rs2: cross cp_c_rdrs1, cp_c_rs2 {
    ignore_bins IGN_OFF = cross_rdrs1_rs2 with (!reg_crosses_enabled);
  }

endgroup : cg_cr


covergroup cg_ci(string name) with function sample (uvma_isacov_instr_c instr);
  option.per_instance = 1;
  option.name = name;

  cp_c_immi: coverpoint instr.c_immi;
  cp_c_rdrs1: coverpoint instr.c_rdrs1;
endgroup : cg_ci


covergroup cg_css(string name) with function sample (uvma_isacov_instr_c instr);
  option.per_instance = 1;
  option.name = name;

  cp_c_immss: coverpoint instr.c_immss;
  cp_c_rs2: coverpoint instr.c_rs2;
endgroup : cg_css


covergroup cg_ciw(string name) with function sample (uvma_isacov_instr_c instr);
  option.per_instance = 1;
  option.name = name;

  cp_c_immiw: coverpoint instr.c_immiw;
  cp_c_rdp: coverpoint instr.c_rdp;
endgroup : cg_ciw


covergroup cg_cl(
    string name, bit reg_crosses_enabled
) with function sample (
    uvma_isacov_instr_c instr
);
  option.per_instance = 1;
  option.name = name;

  cp_c_imml: coverpoint instr.c_imml;
  cp_c_rs1p: coverpoint instr.c_rs1p;
  cp_c_rdp: coverpoint instr.c_rdp;

  cross_rdp_rs1p: cross cp_c_rdp, cp_c_rs1p {
    ignore_bins IGN_OFF = cross_rdp_rs1p with (!reg_crosses_enabled);
  }
endgroup : cg_cl


covergroup cg_cs(
    string name, bit reg_crosses_enabled
) with function sample (
    uvma_isacov_instr_c instr
);
  option.per_instance = 1;
  option.name = name;

  cp_c_imms: coverpoint instr.c_imms;
  cp_c_rs1p: coverpoint instr.c_rs1p;
  cp_c_rs2p: coverpoint instr.c_rs2p;

  cross_rs1p_rs2p: cross cp_c_rs1p, cp_c_rs2p {
    ignore_bins IGN_OFF = cross_rs1p_rs2p with (!reg_crosses_enabled);
  }
endgroup : cg_cs


covergroup cg_ca(
    string name, bit reg_crosses_enabled
) with function sample (
    uvma_isacov_instr_c instr
);
  option.per_instance = 1;
  option.name = name;

  cp_c_rdprs1p: coverpoint instr.c_rdprs1p;
  cp_c_rs2p: coverpoint instr.c_rs2p;

  cross_rdprs1p_rs2p: cross cp_c_rdprs1p, cp_c_rs2p {
    ignore_bins IGN_OFF = cross_rdprs1p_rs2p with (!reg_crosses_enabled);
  }
endgroup : cg_ca


covergroup cg_cb(string name) with function sample (uvma_isacov_instr_c instr);
  option.per_instance = 1;
  option.name = name;

  cp_c_immb: coverpoint instr.c_immb;
  cp_c_rs1p: coverpoint instr.c_rs1p;
endgroup : cg_cb


covergroup cg_cj(string name) with function sample (uvma_isacov_instr_c instr);
  option.per_instance = 1;
  option.name = name;

  cp_c_immj: coverpoint instr.c_immj;
endgroup : cg_cj

covergroup cg_instr(string name,
                    bit seq_instr_group_x2_enabled,
                    bit seq_instr_group_x3_enabled,
                    bit seq_instr_group_x4_enabled,
                    bit [CSR_MASK_WL-1:0] cfg_illegal_csr,
                    bit ext_a_supported) with function sample (uvma_isacov_instr_c instr,
                                                               uvma_isacov_instr_c instr_prev,
                                                               uvma_isacov_instr_c instr_prev2,
                                                               uvma_isacov_instr_c instr_prev3,
                                                               bit raw_hazard,
                                                               bit csr_hazard);
  option.per_instance = 1;
  option.name = name;

  cp_instr: coverpoint(instr.name);
  cp_instr_prev: coverpoint(instr.name);

  cp_group: coverpoint (instr.group) {
    illegal_bins ILL_EXT_A = {ALOAD_GROUP, ASTORE_GROUP, AMEM_GROUP} with (!ext_a_supported);
  }

  cp_group_prev:  coverpoint (instr_prev.group) iff (instr_prev != null) {
    ignore_bins IGN_X2_OFF = {[0:$]} with (!seq_instr_group_x2_enabled);
    illegal_bins ILL_EXT_A = {ALOAD_GROUP, ASTORE_GROUP, AMEM_GROUP} with (!ext_a_supported);
  }

  cp_group_prev2: coverpoint (instr_prev2.group) iff (instr_prev2 != null) {
    ignore_bins IGN_X3_OFF = {[0:$]} with (!seq_instr_group_x3_enabled);
    illegal_bins ILL_EXT_A = {ALOAD_GROUP, ASTORE_GROUP, AMEM_GROUP} with (!ext_a_supported);
  }

  cp_group_prev3: coverpoint (instr_prev3.group) iff (instr_prev3 != null) {
    ignore_bins IGN_X4_OFF = {[0:$]} with (!seq_instr_group_x4_enabled);
    illegal_bins ILL_EXT_A = {ALOAD_GROUP, ASTORE_GROUP, AMEM_GROUP} with (!ext_a_supported);
  }

  cp_raw_hazard: coverpoint(raw_hazard) {
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

  cross_seq_x2: cross cp_group, cp_group_prev;  
  cross_seq_x3: cross cp_group, cp_group_prev, cp_group_prev2;
  cross_seq_x4: cross cp_group, cp_group_prev, cp_group_prev2, cp_group_prev3;

  // FIXME: This will need more filtering
  cross_seq_raw_hazard: cross cp_group, cp_group_prev, cp_raw_hazard {
    // Ignore non-hazard bins
    ignore_bins IGN_HAZ = binsof(cp_raw_hazard) intersect {0};
  }

  cross_csr_hazard: cross cp_csr, cp_instr, cp_csr_hazard {
    // Ignore non-hazard bins
    ignore_bins IGN_HAZ = binsof(cp_csr_hazard) intersect {0};
  }
endgroup : cg_instr


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
  cg_rtype instr_i_add_cg;
  cg_rtype instr_i_sub_cg;
  cg_rtype instr_i_sll_cg;
  cg_rtype instr_i_slt_cg;
  cg_rtype instr_i_sltu_cg;
  cg_rtype instr_i_xor_cg;
  cg_rtype instr_i_srl_cg;
  cg_rtype instr_i_sra_cg;
  cg_rtype instr_i_or_cg;
  cg_rtype instr_i_and_cg;

  cg_itype instr_i_jalr_cg;
  cg_itype instr_i_lb_cg;
  cg_itype instr_i_lh_cg;
  cg_itype instr_i_lw_cg;
  cg_itype instr_i_lbu_cg;
  cg_itype instr_i_lhu_cg;
  cg_itype instr_i_addi_cg;
  cg_itype_slt instr_i_slti_cg;
  cg_itype_slt instr_i_sltiu_cg;
  cg_itype instr_i_xori_cg;
  cg_itype instr_i_ori_cg;
  cg_itype instr_i_andi_cg;
  cg_itype_shift instr_i_slli_cg;
  cg_itype_shift instr_i_srli_cg;
  cg_itype_shift instr_i_srai_cg;

  cg_itype instr_i_fence_cg;  // TODO own cg?
  cg_itype instr_i_ecall_cg;  // TODO own cg?
  cg_itype instr_i_ebreak_cg;  // TODO own cg?

  cg_stype instr_i_sb_cg;
  cg_stype instr_i_sh_cg;
  cg_stype instr_i_sw_cg;

  cg_btype instr_i_beq_cg;
  cg_btype instr_i_bne_cg;
  cg_btype instr_i_blt_cg;
  cg_btype instr_i_bge_cg;
  cg_btype instr_i_bltu_cg;
  cg_btype instr_i_bgeu_cg;

  cg_utype instr_i_lui_cg;
  cg_utype instr_i_auipc_cg;

  cg_jtype instr_i_jal_cg;

  //32M:
  cg_rtype instr_m_mul_cg;
  cg_rtype instr_m_mulh_cg;
  cg_rtype instr_m_mulhsu_cg;
  cg_rtype instr_m_mulhu_cg;
  cg_rtype instr_m_div_cg;
  cg_div_special_results instr_m_div_results_cg;
  cg_rtype instr_m_divu_cg;
  cg_div_special_results instr_m_divu_results_cg;
  cg_rtype instr_m_rem_cg;
  cg_div_special_results instr_m_rem_results_cg;
  cg_rtype instr_m_remu_cg;
  cg_div_special_results instr_m_remu_results_cg;

  //32C:
  cg_ciw instr_c_addi4spn_cg;

  cg_cl  instr_c_lw_cg;

  cg_cs  instr_c_sw_cg;

  cg_ci  instr_c_addi_cg;
  cg_ci  instr_c_slli_cg;
  cg_ci  instr_c_lwsp_cg;
  cg_ci  instr_c_li_cg;
  cg_ci  instr_c_addi16sp_cg;
  cg_ci  instr_c_lui_cg;  // TODO need "cg_ci_lui" specialization?

  cg_cj  instr_c_jal_cg;
  cg_cj  instr_c_j_cg;

  cg_cb  instr_c_srli_cg;
  cg_cb  instr_c_srai_cg;
  cg_cb  instr_c_andi_cg;
  cg_cb  instr_c_beqz_cg;
  cg_cb  instr_c_bnez_cg;

  cg_ca  instr_c_sub_cg;
  cg_ca  instr_c_xor_cg;
  cg_ca  instr_c_or_cg;
  cg_ca  instr_c_and_cg;
  
  cg_cr  instr_c_jr_cg;
  cg_cr  instr_c_mv_cg;
  cg_cr  instr_c_ebreak_cg;  // TODO should have own cg?
  cg_cr  instr_c_jalr_cg;
  cg_cr  instr_c_add_cg;

  cg_css instr_c_swsp_cg;
  
  //Zicsr:
  cg_csrtype  instr_csrrw_cg;
  cg_csrtype  instr_csrrs_cg;
  cg_csrtype  instr_csrrc_cg;
  cg_csritype instr_csrrwi_cg;
  cg_csritype instr_csrrsi_cg;
  cg_csritype instr_csrrci_cg;

  //Zifence_i:
  cg_itype    instr_fence_i_cg;  // TODO own cg? (not itype)

  // Instruction groups
  cg_instr    group_cg;

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
    if (cfg.core_cfg.ext_i_supported) begin
      instr_i_lui_cg    = new("instr_i_lui_cg");
      instr_i_auipc_cg  = new("instr_i_auipc_cg");
      instr_i_jal_cg    = new("instr_i_jal_cg");
      instr_i_jalr_cg   = new("instr_i_jalr_cg", .reg_crosses_enabled(cfg.reg_crosses_enabled), .reg_hazards_enabled(cfg.reg_hazards_enabled));

      instr_i_beq_cg    = new("instr_i_beq_cg", .reg_crosses_enabled(cfg.reg_crosses_enabled));
      instr_i_bne_cg    = new("instr_i_bne_cg", .reg_crosses_enabled(cfg.reg_crosses_enabled));
      instr_i_blt_cg    = new("instr_i_blt_cg", .reg_crosses_enabled(cfg.reg_crosses_enabled));
      instr_i_bge_cg    = new("instr_i_bge_cg", .reg_crosses_enabled(cfg.reg_crosses_enabled));
      instr_i_bltu_cg   = new("instr_i_bltu_cg", .reg_crosses_enabled(cfg.reg_crosses_enabled));
      instr_i_bgeu_cg   = new("instr_i_bgeu_cg", .reg_crosses_enabled(cfg.reg_crosses_enabled));

      instr_i_lb_cg     = new("instr_i_lb_cg",  .reg_crosses_enabled(cfg.reg_crosses_enabled), .reg_hazards_enabled(cfg.reg_hazards_enabled));
      instr_i_lh_cg     = new("instr_i_lh_cg",  .reg_crosses_enabled(cfg.reg_crosses_enabled), .reg_hazards_enabled(cfg.reg_hazards_enabled));
      instr_i_lw_cg     = new("instr_i_lw_cg",  .reg_crosses_enabled(cfg.reg_crosses_enabled), .reg_hazards_enabled(cfg.reg_hazards_enabled));
      instr_i_lbu_cg    = new("instr_i_lbu_cg", .reg_crosses_enabled(cfg.reg_crosses_enabled), .reg_hazards_enabled(cfg.reg_hazards_enabled));
      instr_i_lhu_cg    = new("instr_i_lhu_cg", .reg_crosses_enabled(cfg.reg_crosses_enabled), .reg_hazards_enabled(cfg.reg_hazards_enabled));

      instr_i_sb_cg     = new("instr_i_sb_cg", .reg_crosses_enabled(cfg.reg_crosses_enabled));
      instr_i_sh_cg     = new("instr_i_sh_cg", .reg_crosses_enabled(cfg.reg_crosses_enabled));
      instr_i_sw_cg     = new("instr_i_sw_cg", .reg_crosses_enabled(cfg.reg_crosses_enabled));

      instr_i_addi_cg   = new("instr_i_addi_cg",  .reg_crosses_enabled(cfg.reg_crosses_enabled), .reg_hazards_enabled(cfg.reg_hazards_enabled));
      instr_i_slti_cg   = new("instr_i_slti_cg",  .reg_crosses_enabled(cfg.reg_crosses_enabled), .reg_hazards_enabled(cfg.reg_hazards_enabled));
      instr_i_sltiu_cg  = new("instr_i_sltiu_cg", .reg_crosses_enabled(cfg.reg_crosses_enabled), .reg_hazards_enabled(cfg.reg_hazards_enabled));
      instr_i_xori_cg   = new("instr_i_xori_cg",  .reg_crosses_enabled(cfg.reg_crosses_enabled), .reg_hazards_enabled(cfg.reg_hazards_enabled));
      instr_i_ori_cg    = new("instr_i_ori_cg",   .reg_crosses_enabled(cfg.reg_crosses_enabled), .reg_hazards_enabled(cfg.reg_hazards_enabled));
      instr_i_andi_cg   = new("instr_i_andi_cg",  .reg_crosses_enabled(cfg.reg_crosses_enabled), .reg_hazards_enabled(cfg.reg_hazards_enabled));
      instr_i_slli_cg   = new("instr_i_slli_cg",  .reg_crosses_enabled(cfg.reg_crosses_enabled), .reg_hazards_enabled(cfg.reg_hazards_enabled));
      instr_i_srli_cg   = new("instr_i_srli_cg",  .reg_crosses_enabled(cfg.reg_crosses_enabled), .reg_hazards_enabled(cfg.reg_hazards_enabled));
      instr_i_srai_cg   = new("instr_i_srai_cg",  .reg_crosses_enabled(cfg.reg_crosses_enabled), .reg_hazards_enabled(cfg.reg_hazards_enabled));

      instr_i_add_cg    = new("instr_i_add_cg",  .reg_crosses_enabled(cfg.reg_crosses_enabled), .reg_hazards_enabled(cfg.reg_hazards_enabled));
      instr_i_sub_cg    = new("instr_i_sub_cg",  .reg_crosses_enabled(cfg.reg_crosses_enabled), .reg_hazards_enabled(cfg.reg_hazards_enabled));
      instr_i_sll_cg    = new("instr_i_sll_cg",  .reg_crosses_enabled(cfg.reg_crosses_enabled), .reg_hazards_enabled(cfg.reg_hazards_enabled));
      instr_i_slt_cg    = new("instr_i_slt_cg",  .reg_crosses_enabled(cfg.reg_crosses_enabled), .reg_hazards_enabled(cfg.reg_hazards_enabled));
      instr_i_sltu_cg   = new("instr_i_sltu_cg", .reg_crosses_enabled(cfg.reg_crosses_enabled), .reg_hazards_enabled(cfg.reg_hazards_enabled));
      instr_i_xor_cg    = new("instr_i_xor_cg",  .reg_crosses_enabled(cfg.reg_crosses_enabled), .reg_hazards_enabled(cfg.reg_hazards_enabled));
      instr_i_srl_cg    = new("instr_i_srl_cg",  .reg_crosses_enabled(cfg.reg_crosses_enabled), .reg_hazards_enabled(cfg.reg_hazards_enabled));
      instr_i_sra_cg    = new("instr_i_sra_cg",  .reg_crosses_enabled(cfg.reg_crosses_enabled), .reg_hazards_enabled(cfg.reg_hazards_enabled));
      instr_i_or_cg     = new("instr_i_or_cg",   .reg_crosses_enabled(cfg.reg_crosses_enabled), .reg_hazards_enabled(cfg.reg_hazards_enabled));
      instr_i_and_cg    = new("instr_i_and_cg",  .reg_crosses_enabled(cfg.reg_crosses_enabled), .reg_hazards_enabled(cfg.reg_hazards_enabled));

      instr_i_fence_cg  = new("instr_i_fence_cg",  .reg_crosses_enabled(cfg.reg_crosses_enabled), .reg_hazards_enabled(cfg.reg_hazards_enabled));
      instr_i_ecall_cg  = new("instr_i_ecall_cg",  .reg_crosses_enabled(cfg.reg_crosses_enabled), .reg_hazards_enabled(cfg.reg_hazards_enabled));
      instr_i_ebreak_cg = new("instr_i_ebreak_cg", .reg_crosses_enabled(cfg.reg_crosses_enabled), .reg_hazards_enabled(cfg.reg_hazards_enabled));
    end
    if (cfg.core_cfg.ext_m_supported) begin
      instr_m_mul_cg    = new("instr_m_mul_cg",    
                              .reg_crosses_enabled(cfg.reg_crosses_enabled), 
                              .reg_hazards_enabled(cfg.reg_hazards_enabled), 
                              .rs1_is_signed(rs1_is_signed[MUL]),
                              .rs2_is_signed(rs2_is_signed[MUL]),
                              .rd_is_signed(rd_is_signed[MUL]));
      instr_m_mulh_cg   = new("instr_m_mulh_cg",   
                              .reg_crosses_enabled(cfg.reg_crosses_enabled), 
                              .reg_hazards_enabled(cfg.reg_hazards_enabled), 
                              .rs1_is_signed(rs1_is_signed[MULH]),
                              .rs2_is_signed(rs2_is_signed[MULH]),
                              .rd_is_signed(rd_is_signed[MULH]));
      instr_m_mulhsu_cg = new("instr_m_mulhsu_cg", 
                              .reg_crosses_enabled(cfg.reg_crosses_enabled), 
                              .reg_hazards_enabled(cfg.reg_hazards_enabled),
                              .rs1_is_signed(rs1_is_signed[MULHSU]),
                              .rs2_is_signed(rs2_is_signed[MULHSU]),
                              .rd_is_signed(rd_is_signed[MULHSU]));
      instr_m_mulhu_cg  = new("instr_m_mulhu_cg",  
                              .reg_crosses_enabled(cfg.reg_crosses_enabled), 
                              .reg_hazards_enabled(cfg.reg_hazards_enabled), 
                              .rs1_is_signed(rs1_is_signed[MULHU]),
                              .rs2_is_signed(rs2_is_signed[MULHU]),
                              .rd_is_signed(rd_is_signed[MULHU]));
      instr_m_div_cg    = new("instr_m_div_cg",    
                              .reg_crosses_enabled(cfg.reg_crosses_enabled), 
                              .reg_hazards_enabled(cfg.reg_hazards_enabled), 
                              .rs1_is_signed(rs1_is_signed[DIV]),
                              .rs2_is_signed(rs2_is_signed[DIV]),
                              .rd_is_signed(rd_is_signed[DIV]));      
      instr_m_div_results_cg = new("instr_m_div_results_cg",
                                    .check_overflow(1));
      instr_m_divu_cg   = new("instr_m_divu_cg",   
                              .reg_crosses_enabled(cfg.reg_crosses_enabled), 
                              .reg_hazards_enabled(cfg.reg_hazards_enabled), 
                              .rs1_is_signed(rs1_is_signed[DIVU]),
                              .rs2_is_signed(rs2_is_signed[DIVU]),
                              .rd_is_signed(rd_is_signed[DIVU]));                              
      instr_m_divu_results_cg = new("instr_m_udiv_results_cg",    
                                    .check_overflow(0));
      instr_m_rem_cg    = new("instr_m_rem_cg",
                              .reg_crosses_enabled(cfg.reg_crosses_enabled), 
                              .reg_hazards_enabled(cfg.reg_hazards_enabled), 
                              .rs1_is_signed(rs1_is_signed[REM]),
                              .rs2_is_signed(rs2_is_signed[REM]),
                              .rd_is_signed(rd_is_signed[REM]));    
      instr_m_rem_results_cg = new("instr_m_rem_results_cg",    
                                   .check_overflow(1));
      instr_m_remu_cg   = new("instr_m_remu_cg",
                              .reg_crosses_enabled(cfg.reg_crosses_enabled), 
                              .reg_hazards_enabled(cfg.reg_hazards_enabled), 
                              .rs1_is_signed(rs1_is_signed[REMU]),
                              .rs2_is_signed(rs2_is_signed[REMU]),
                              .rd_is_signed(rd_is_signed[REMU]));    
      instr_m_remu_results_cg = new("instr_m_remu_results_cg",
                                    .check_overflow(0));
    end
    if (cfg.core_cfg.ext_c_supported) begin
      instr_c_addi4spn_cg = new("instr_c_addi4spn_cg");
      instr_c_lw_cg       = new("instr_c_lw_cg", .reg_crosses_enabled(cfg.reg_crosses_enabled));
      instr_c_sw_cg       = new("instr_c_sw_cg", .reg_crosses_enabled(cfg.reg_crosses_enabled));

      instr_c_addi_cg     = new("instr_c_addi_cg");
      instr_c_jal_cg      = new("instr_c_jal_cg");
      instr_c_li_cg       = new("instr_c_li_cg");
      instr_c_addi16sp_cg = new("instr_c_addi16sp_cg");
      instr_c_lui_cg      = new("instr_c_lui_cg");
      instr_c_srli_cg     = new("instr_c_srli_cg");
      instr_c_srai_cg     = new("instr_c_srai_cg");
      instr_c_andi_cg     = new("instr_c_andi_cg");
      instr_c_sub_cg      = new("instr_c_sub_cg", .reg_crosses_enabled(cfg.reg_crosses_enabled));
      instr_c_xor_cg      = new("instr_c_xor_cg", .reg_crosses_enabled(cfg.reg_crosses_enabled));
      instr_c_or_cg       = new("instr_c_or_cg", .reg_crosses_enabled(cfg.reg_crosses_enabled));
      instr_c_and_cg      = new("instr_c_and_cg", .reg_crosses_enabled(cfg.reg_crosses_enabled));
      instr_c_j_cg        = new("instr_c_j_cg");
      instr_c_beqz_cg     = new("instr_c_beqz_cg");
      instr_c_bnez_cg     = new("instr_c_bnez_cg");

      instr_c_slli_cg     = new("instr_c_slli_cg");
      instr_c_lwsp_cg     = new("instr_c_lwsp_cg");
      instr_c_jr_cg       = new("instr_c_jr_cg", .reg_crosses_enabled(cfg.reg_crosses_enabled), .reg_hazards_enabled(0));
      instr_c_mv_cg       = new("instr_c_mv_cg", .reg_crosses_enabled(cfg.reg_crosses_enabled), .reg_hazards_enabled(cfg.reg_hazards_enabled));
      instr_c_ebreak_cg   = new("instr_c_ebreak_cg", .reg_crosses_enabled(cfg.reg_crosses_enabled), .reg_hazards_enabled(0));
      instr_c_jalr_cg     = new("instr_c_jalr_cg", .reg_crosses_enabled(cfg.reg_crosses_enabled), .reg_hazards_enabled(0));
      instr_c_add_cg      = new("instr_c_add_cg", .reg_crosses_enabled(cfg.reg_crosses_enabled), .reg_hazards_enabled(cfg.reg_hazards_enabled));
      instr_c_swsp_cg     = new("instr_c_swsp_cg");
    end
    if (cfg.core_cfg.ext_zicsri_supported) begin
      instr_csrrw_cg  = new("instr_csrrw_cg", cfg.core_cfg.unsupported_csr_mask, .reg_crosses_enabled(cfg.reg_crosses_enabled));
      instr_csrrs_cg  = new("instr_csrrs_cg", cfg.core_cfg.unsupported_csr_mask, .reg_crosses_enabled(cfg.reg_crosses_enabled));
      instr_csrrc_cg  = new("instr_csrrc_cg", cfg.core_cfg.unsupported_csr_mask, .reg_crosses_enabled(cfg.reg_crosses_enabled));
      instr_csrrwi_cg = new("instr_csrrwi_cg", cfg.core_cfg.unsupported_csr_mask, .reg_crosses_enabled(cfg.reg_crosses_enabled));
      instr_csrrsi_cg = new("instr_csrrsi_cg", cfg.core_cfg.unsupported_csr_mask, .reg_crosses_enabled(cfg.reg_crosses_enabled));
      instr_csrrci_cg = new("instr_csrrci_cg", cfg.core_cfg.unsupported_csr_mask, .reg_crosses_enabled(cfg.reg_crosses_enabled));
    end
    if (cfg.core_cfg.ext_zifencei_supported) begin
      instr_fence_i_cg = new("instr_fence_i_cg", .reg_crosses_enabled(cfg.reg_crosses_enabled), .reg_hazards_enabled(cfg.reg_hazards_enabled));
    end
    group_cg = new("group_cg",
                   .seq_instr_group_x2_enabled(cfg.seq_instr_group_x2_enabled),
                   .seq_instr_group_x3_enabled(cfg.seq_instr_group_x3_enabled),
                   .seq_instr_group_x4_enabled(cfg.seq_instr_group_x4_enabled),
                   .cfg_illegal_csr(cfg.core_cfg.unsupported_csr_mask),
                   .ext_a_supported(cfg.core_cfg.ext_a_supported));
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

  if (!have_sampled && cfg.core_cfg.ext_i_supported) begin
    have_sampled = 1;
    case (instr.name)
      LUI:   instr_i_lui_cg.sample(instr);
      AUIPC: instr_i_auipc_cg.sample(instr);
      JAL:   instr_i_jal_cg.sample(instr);
      JALR:  instr_i_jalr_cg.sample(instr);

      BEQ:  instr_i_beq_cg.sample(instr);
      BNE:  instr_i_bne_cg.sample(instr);
      BLT:  instr_i_blt_cg.sample(instr);
      BGE:  instr_i_bge_cg.sample(instr);
      BLTU: instr_i_bltu_cg.sample(instr);
      BGEU: instr_i_bgeu_cg.sample(instr);

      LB:  instr_i_lb_cg.sample(instr);
      LH:  instr_i_lh_cg.sample(instr);
      LW:  instr_i_lw_cg.sample(instr);
      LBU: instr_i_lbu_cg.sample(instr);
      LHU: instr_i_lhu_cg.sample(instr);
      SB:  instr_i_sb_cg.sample(instr);
      SH:  instr_i_sh_cg.sample(instr);
      SW:  instr_i_sw_cg.sample(instr);

      ADDI:  instr_i_addi_cg.sample(instr);
      SLTI:  instr_i_slti_cg.sample(instr);
      SLTIU: instr_i_sltiu_cg.sample(instr);
      XORI:  instr_i_xori_cg.sample(instr);
      ORI:   instr_i_ori_cg.sample(instr);
      ANDI:  instr_i_andi_cg.sample(instr);
      SLLI:  instr_i_slli_cg.sample(instr);
      SRLI:  instr_i_srli_cg.sample(instr);
      SRAI:  instr_i_srai_cg.sample(instr);

      ADD:  instr_i_add_cg.sample(instr);      
      SUB:  instr_i_sub_cg.sample(instr);
      SLL:  instr_i_sll_cg.sample(instr);
      SLT:  instr_i_slt_cg.sample(instr);
      SLTU: instr_i_sltu_cg.sample(instr);
      XOR:  instr_i_xor_cg.sample(instr);
      SRL:  instr_i_srl_cg.sample(instr);
      SRA:  instr_i_sra_cg.sample(instr);
      OR:   instr_i_or_cg.sample(instr);
      AND:  instr_i_and_cg.sample(instr);

      FENCE:  instr_i_fence_cg.sample(instr);
      ECALL:  instr_i_ecall_cg.sample(instr);
      EBREAK: instr_i_ebreak_cg.sample(instr);

      default: have_sampled = 0;
    endcase
  end

  if (!have_sampled && cfg.core_cfg.ext_m_supported) begin
    have_sampled = 1;
    case (instr.name)
      MUL:     instr_m_mul_cg.sample(instr);
      MULH:    instr_m_mulh_cg.sample(instr);
      MULHSU:  instr_m_mulhsu_cg.sample(instr);
      MULHU:   instr_m_mulhu_cg.sample(instr);
      DIV: begin
               instr_m_div_results_cg.sample(instr);
               instr_m_div_cg.sample(instr);
               
      end    
      DIVU: begin
               instr_m_divu_cg.sample(instr);
               instr_m_divu_results_cg.sample(instr);
      end    
      REM: begin
               instr_m_rem_cg.sample(instr);
               instr_m_rem_results_cg.sample(instr);
      end    
      REMU: begin
               instr_m_remu_cg.sample(instr);
               instr_m_remu_results_cg.sample(instr);
      end    
      default: have_sampled = 0;
    endcase
  end

  if (!have_sampled && cfg.core_cfg.ext_c_supported) begin
    have_sampled = 1;
    case (instr.name)
      C_ADDI4SPN: instr_c_addi4spn_cg.sample(instr);
      C_LW:       instr_c_lw_cg.sample(instr);
      C_SW:       instr_c_sw_cg.sample(instr);

      C_ADDI:     instr_c_addi_cg.sample(instr);
      C_JAL:      instr_c_jal_cg.sample(instr);
      C_LI:       instr_c_li_cg.sample(instr);
      C_ADDI16SP: instr_c_addi16sp_cg.sample(instr);
      C_LUI:      instr_c_lui_cg.sample(instr);
      C_SRLI:     instr_c_srli_cg.sample(instr);
      C_SRAI:     instr_c_srai_cg.sample(instr);
      C_ANDI:     instr_c_andi_cg.sample(instr);
      C_SUB:      instr_c_sub_cg.sample(instr);
      C_XOR:      instr_c_xor_cg.sample(instr);
      C_OR:       instr_c_or_cg.sample(instr);
      C_AND:      instr_c_and_cg.sample(instr);
      C_J:        instr_c_j_cg.sample(instr);
      C_BEQZ:     instr_c_beqz_cg.sample(instr);
      C_BNEZ:     instr_c_bnez_cg.sample(instr);

      C_SLLI:   instr_c_slli_cg.sample(instr);
      C_LWSP:   instr_c_lwsp_cg.sample(instr);
      C_JR:     instr_c_jr_cg.sample(instr);
      C_MV:     instr_c_mv_cg.sample(instr);
      C_EBREAK: instr_c_ebreak_cg.sample(instr);
      C_JALR:   instr_c_jalr_cg.sample(instr);
      C_ADD:    instr_c_add_cg.sample(instr);
      C_SWSP:   instr_c_swsp_cg.sample(instr);

      default: have_sampled = 0;
    endcase
  end

  if (!have_sampled && cfg.core_cfg.ext_zicsri_supported) begin
    have_sampled = 1;
    case (instr.name)
      CSRRW:   instr_csrrw_cg.sample(instr);
      CSRRS:   instr_csrrs_cg.sample(instr);
      CSRRC:   instr_csrrc_cg.sample(instr);
      CSRRWI:  instr_csrrwi_cg.sample(instr);
      CSRRSI:  instr_csrrsi_cg.sample(instr);
      CSRRCI:  instr_csrrci_cg.sample(instr);
      default: have_sampled = 0;
    endcase
  end

  if (!have_sampled && cfg.core_cfg.ext_zifencei_supported) begin
    have_sampled = 1;
    case (instr.name)
      FENCE_I: instr_fence_i_cg.sample(instr);
      default: have_sampled = 0;
    endcase
  end

  if (!have_sampled) begin
    `uvm_info("ISACOV", $sformatf("Could not sample instruction: %s", instr.name.name()), UVM_DEBUG);
  end

  group_cg.sample(instr, 
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
