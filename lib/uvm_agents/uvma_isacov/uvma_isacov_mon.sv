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

`uvm_analysis_imp_decl(_rvfi_instr)

class uvma_isacov_mon_c#(int ILEN=DEFAULT_ILEN,
                         int XLEN=DEFAULT_XLEN) extends uvm_monitor;

  `uvm_component_param_utils(uvma_isacov_mon_c);

  uvma_isacov_cntxt_c                        cntxt;
  uvma_isacov_cfg_c                          cfg;
  uvm_analysis_port#(uvma_isacov_mon_trn_c)  ap;
  instr_name_t                               instr_name_lookup[string];

  // Analysis export to receive instructions from RVFI
  uvm_analysis_imp_rvfi_instr#(uvma_rvfi_instr_seq_item_c#(ILEN,XLEN), uvma_isacov_mon_c) rvfi_instr_imp;

  extern function new(string name = "uvma_isacov_mon", uvm_component parent = null);
  extern virtual function void build_phase(uvm_phase phase);

  /**
   * Convert enumeration from <instr_name_t> to match Spike disassembler
   */
  extern function string convert_instr_to_spike_name(string instr_name);

  /**
   * Analysis port write from RVFI instruction retirement monitor
   */
  extern virtual function void write_rvfi_instr(uvma_rvfi_instr_seq_item_c#(ILEN,XLEN) rvfi_instr);

endclass : uvma_isacov_mon_c


function uvma_isacov_mon_c::new(string name = "uvma_isacov_mon", uvm_component parent = null);

  super.new(name, parent);
  rvfi_instr_imp = new("rvfi_instr_imp", this);

endfunction : new


function void uvma_isacov_mon_c::build_phase(uvm_phase phase);

  instr_name_t in;

  super.build_phase(phase);

  void'(uvm_config_db#(uvma_isacov_cntxt_c)::get(this, "", "cntxt", cntxt));
  if (!cntxt) begin
    `uvm_fatal("CNTXT", "Context handle is null")
  end

  void'(uvm_config_db#(uvma_isacov_cfg_c)::get(this, "", "cfg", cfg));
  if (!cfg) begin
    `uvm_fatal("CFG", "Configuration handle is null")
  end

  ap = new("ap", this);

  dasm_set_config(32, "rv32imc", 0);

  // Use the enumerations in <instr_name_t> to setup the instr_name_lookup
  // convert the enums to lower-case and substitute underscore with . to match
  // Spike disassembler
  in = in.first;
  repeat(in.num) begin
    string instr_name_key = convert_instr_to_spike_name(in.name());

    `uvm_info("ISACOV", $sformatf("Converting: %s to %s", in.name(), instr_name_key), UVM_HIGH);
    instr_name_lookup[instr_name_key] = in;
    in = in.next;
  end

endfunction : build_phase

function string uvma_isacov_mon_c::convert_instr_to_spike_name(string instr_name);

  string spike_instr_name;

  foreach (instr_name[i]) begin
    string chr;

    chr = instr_name.substr(i,i).tolower();

    if (chr == "_") chr = ".";

    spike_instr_name = { spike_instr_name, chr };
  end

  // But fence.i is encoded as fence_i in the disassembler
  if (spike_instr_name == "fence.i")
    spike_instr_name = "fence_i";
  // Ugh
  if (spike_instr_name == "lr.w")
    spike_instr_name = "lr_w";
  if (spike_instr_name == "bset")
    spike_instr_name = "bset (args unknown)";
  if (spike_instr_name == "bseti")
    spike_instr_name = "bseti (args unknown)";
  if (spike_instr_name == "bclr")
    spike_instr_name = "bclr (args unknown)";
  if (spike_instr_name == "bclri")
    spike_instr_name = "bclri (args unknown)";
  if (spike_instr_name == "binv")
    spike_instr_name = "binv (args unknown)";
  if (spike_instr_name == "binvi")
    spike_instr_name = "binvi (args unknown)";
  if (spike_instr_name == "bext")
    spike_instr_name = "bext (args unknown)";
  if (spike_instr_name == "bexti")
    spike_instr_name = "bexti (args unknown)";

  return spike_instr_name;

endfunction : convert_instr_to_spike_name

function void uvma_isacov_mon_c::write_rvfi_instr(uvma_rvfi_instr_seq_item_c#(ILEN,XLEN) rvfi_instr);

  uvma_isacov_mon_trn_c mon_trn;
  string                instr_name;
  bit [63:0]            instr;

  mon_trn = uvma_isacov_mon_trn_c#(.ILEN(ILEN), .XLEN(XLEN))::type_id::create("mon_trn");
  mon_trn.instr = uvma_isacov_instr_c#(ILEN,XLEN)::type_id::create("mon_instr");
  mon_trn.instr.rvfi = rvfi_instr;

  // Mark trapped instructions from RVFI
  mon_trn.instr.trap = rvfi_instr.trap;

  // Attempt to decode instruction with Spike DASM
  instr_name = dasm_name(rvfi_instr.insn);
  if (instr_name_lookup.exists(instr_name)) begin
    mon_trn.instr.name = instr_name_lookup[instr_name];
  end else begin
    // Undecodable instruction
    // Note that Spike can decode "everything" so if it doesn't map above, then it is an undecodable instruction
    // from OpenHW core-v-verif perspective so set to UNKNOWN
    mon_trn.instr.name = UNKNOWN;
  end

  `uvm_info("ISACOVMON", $sformatf("rvfi = 0x%08x %s", rvfi_instr.insn, instr_name), UVM_HIGH);

  mon_trn.instr.itype = get_instr_type(mon_trn.instr.name);
  mon_trn.instr.ext   = get_instr_ext(mon_trn.instr.name);
  mon_trn.instr.group = get_instr_group(mon_trn.instr.name, rvfi_instr.mem_addr);

  instr = $signed(rvfi_instr.insn);

  // Disassemble the instruction using Spike (via DPI)
  if (mon_trn.instr.ext == C_EXT) begin
    mon_trn.instr.rs1     = dasm_rvc_rs1(instr);
    mon_trn.instr.rs2     = dasm_rvc_rs2(instr);
    mon_trn.instr.rd      = dasm_rvc_rd(instr);
    mon_trn.instr.c_rdrs1 = dasm_rvc_rd(instr);
    mon_trn.instr.c_rd    = mon_trn.instr.decode_rd_c(instr);
    mon_trn.instr.c_rs1   = mon_trn.instr.decode_rs1_c(instr);
    mon_trn.instr.c_rs2   = mon_trn.instr.decode_rs2_c(instr);
  end
  else begin
    mon_trn.instr.rs1  = dasm_rs1(instr);
    mon_trn.instr.rs2  = dasm_rs2(instr);
    mon_trn.instr.rd   = dasm_rd(instr);
    mon_trn.instr.immi = dasm_i_imm(instr);
    mon_trn.instr.imms = dasm_s_imm(instr);
    mon_trn.instr.immb = dasm_sb_imm(instr) >> 1;  // Because dasm gives [12:0], not [12: 1]
    mon_trn.instr.immu = dasm_u_imm(instr) >> 12;  // Because dasm gives [31:0], not [31:12]
    mon_trn.instr.immj = dasm_uj_imm(instr) >> 1;  // Because dasm gives [20:0], not [20: 1]
  end

  // Make instructions as illegal,
  // 1. If UNKNOWN (undecodable)
  if (mon_trn.instr.name == UNKNOWN)
    mon_trn.instr.illegal = 1;
  // 2. If a CSR instruction is not targeted to a valid CSR
  if (mon_trn.instr.group == CSR_GROUP) begin
    mon_trn.instr.csr_val = dasm_csr(instr);
    if (!$cast(mon_trn.instr.csr, mon_trn.instr.csr_val) ||
         cfg.core_cfg.unsupported_csr_mask[mon_trn.instr.csr_val]) begin
      mon_trn.instr.illegal = 1;
    end
  end
  // 3. Instruction is in unsupported extension
  if ((mon_trn.instr.ext == A_EXT && !cfg.core_cfg.ext_a_supported) ||
      (mon_trn.instr.ext == C_EXT && !cfg.core_cfg.ext_c_supported) ||
      (mon_trn.instr.ext == F_EXT && !cfg.core_cfg.ext_f_supported) ||
      (mon_trn.instr.ext == M_EXT && !cfg.core_cfg.ext_m_supported) ||
      (mon_trn.instr.ext == P_EXT && !cfg.core_cfg.ext_p_supported) ||
      (mon_trn.instr.ext == ZICSR_EXT && !cfg.core_cfg.ext_zicsr_supported) ||
      (mon_trn.instr.ext == ZIFENCEI_EXT && !cfg.core_cfg.ext_zifencei_supported) ||
      (mon_trn.instr.itype == ZBA_TYPE && !cfg.core_cfg.ext_zba_supported) ||
      (mon_trn.instr.itype == ZBB_TYPE && !cfg.core_cfg.ext_zbb_supported) ||
      (mon_trn.instr.itype == ZBC_TYPE && !cfg.core_cfg.ext_zbc_supported) ||
      (mon_trn.instr.itype == ZBS_TYPE && !cfg.core_cfg.ext_zbs_supported)) begin
    mon_trn.instr.illegal = 1;
  end
  // 4. Valid supported instruction with invalid operands
  if (mon_trn.instr.name == C_ADDI4SPN && mon_trn.instr.get_field_imm() == 0)
    mon_trn.instr.illegal = 1;

  // Set enumerations for each immediate value (if applicable)
  if (mon_trn.instr.itype == B_TYPE)
    mon_trn.instr.immb_value_type = mon_trn.instr.get_instr_value_type(mon_trn.instr.immb, $bits(mon_trn.instr.immb), 1);

  if (mon_trn.instr.itype == S_TYPE)
    mon_trn.instr.imms_value_type = mon_trn.instr.get_instr_value_type(mon_trn.instr.imms, $bits(mon_trn.instr.imms), 1);

  if (mon_trn.instr.itype == U_TYPE)
    mon_trn.instr.immu_value_type = mon_trn.instr.get_instr_value_type(mon_trn.instr.immu, $bits(mon_trn.instr.immu), 0);

  if (mon_trn.instr.itype == I_TYPE)
    mon_trn.instr.immi_value_type = mon_trn.instr.get_instr_value_type(mon_trn.instr.immi, $bits(mon_trn.instr.immi), immi_is_signed[mon_trn.instr.name]);

  if (mon_trn.instr.itype == J_TYPE)
    mon_trn.instr.immj_value_type = mon_trn.instr.get_instr_value_type(mon_trn.instr.immj, $bits(mon_trn.instr.immj), 1);

  if (mon_trn.instr.itype == CI_TYPE) begin
    case (mon_trn.instr.name)
      C_ADDI:      mon_trn.instr.c_imm_value_type = mon_trn.instr.get_instr_value_type(mon_trn.instr.get_field_imm(), 6, c_imm_is_signed[mon_trn.instr.name]);
      C_NOP:       mon_trn.instr.c_imm_value_type = mon_trn.instr.get_instr_value_type(mon_trn.instr.get_field_imm(), 6, c_imm_is_signed[mon_trn.instr.name]);
      C_ADDI16SP:  mon_trn.instr.c_imm_value_type = mon_trn.instr.get_instr_value_type(mon_trn.instr.get_field_imm(), 6, c_imm_is_signed[mon_trn.instr.name]);
      C_LWSP:      mon_trn.instr.c_imm_value_type = mon_trn.instr.get_instr_value_type(mon_trn.instr.get_field_imm(), 6, c_imm_is_signed[mon_trn.instr.name]);
      C_SLLI:      mon_trn.instr.c_imm_value_type = mon_trn.instr.get_instr_value_type(mon_trn.instr.get_field_imm(), 6, c_imm_is_signed[mon_trn.instr.name]);
      C_LI:        mon_trn.instr.c_imm_value_type = mon_trn.instr.get_instr_value_type(mon_trn.instr.get_field_imm(), 6, c_imm_is_signed[mon_trn.instr.name]);
      C_LUI:       mon_trn.instr.c_imm_value_type = mon_trn.instr.get_instr_value_type(mon_trn.instr.get_field_imm(), 6, c_imm_is_signed[mon_trn.instr.name]);
      default:     `uvm_fatal("ISACOV", $sformatf("unhandled CI instruction: %s", mon_trn.instr.name.name()))
    endcase
  end
  if (mon_trn.instr.itype == CSS_TYPE) begin
    case (mon_trn.instr.name)
      C_SWSP: mon_trn.instr.c_imm_value_type = mon_trn.instr.get_instr_value_type(mon_trn.instr.get_field_imm(), 6, c_imm_is_signed[mon_trn.instr.name]);
      default:     `uvm_fatal("ISACOV", $sformatf("unhandled CSS instruction: %s", mon_trn.instr.name.name()))
    endcase
  end
  if (mon_trn.instr.itype == CIW_TYPE) begin
    case (mon_trn.instr.name)
      C_ADDI4SPN: mon_trn.instr.c_imm_value_type = mon_trn.instr.get_instr_value_type(mon_trn.instr.get_field_imm(), 8, c_imm_is_signed[mon_trn.instr.name]);
      default:     `uvm_fatal("ISACOV", $sformatf("unhandled CIW instruction: %s", mon_trn.instr.name.name()))
    endcase
  end
  if (mon_trn.instr.itype == CL_TYPE) begin
    case (mon_trn.instr.name)
      C_LW: mon_trn.instr.c_imm_value_type = mon_trn.instr.get_instr_value_type(mon_trn.instr.get_field_imm(), 5, c_imm_is_signed[mon_trn.instr.name]);
      default:     `uvm_fatal("ISACOV", $sformatf("unhandled CL instruction: %s", mon_trn.instr.name.name()))
    endcase
  end
  if (mon_trn.instr.itype == CS_TYPE) begin
    case (mon_trn.instr.name)
      C_SW: mon_trn.instr.c_imm_value_type = mon_trn.instr.get_instr_value_type(mon_trn.instr.get_field_imm(), 5, c_imm_is_signed[mon_trn.instr.name]);
      default:     `uvm_fatal("ISACOV", $sformatf("unhandled CS instruction: %s", mon_trn.instr.name.name()))
    endcase
  end
  if (mon_trn.instr.itype == CB_TYPE) begin
    case (mon_trn.instr.name)
      C_BEQZ,
      C_BNEZ: mon_trn.instr.c_imm_value_type = mon_trn.instr.get_instr_value_type(mon_trn.instr.get_field_imm(), 8, c_imm_is_signed[mon_trn.instr.name]);
      C_ANDI: mon_trn.instr.c_imm_value_type = mon_trn.instr.get_instr_value_type(mon_trn.instr.get_field_imm(), 6, c_imm_is_signed[mon_trn.instr.name]);
      C_SRLI,
      C_SRAI: mon_trn.instr.c_imm_value_type = mon_trn.instr.get_instr_value_type(mon_trn.instr.get_field_imm(), 6, c_imm_is_signed[mon_trn.instr.name]);
      default:     `uvm_fatal("ISACOV", $sformatf("unhandled CB instruction: %s", mon_trn.instr.name.name()))
    endcase
  end
  if (mon_trn.instr.itype == CJ_TYPE) begin
    case (mon_trn.instr.name)
      C_J,
      C_JAL: mon_trn.instr.c_imm_value_type = mon_trn.instr.get_instr_value_type(mon_trn.instr.get_field_imm(), 11, c_imm_is_signed[mon_trn.instr.name]);
      default:     `uvm_fatal("ISACOV", $sformatf("unhandled CJ instruction: %s", mon_trn.instr.name.name()))
    endcase
  end

  mon_trn.instr.set_valid_flags();

  // Set enumerations for register values as reported from RVFI
  if (mon_trn.instr.rs1_valid) begin
    mon_trn.instr.rs1_value = rvfi_instr.rs1_rdata;
    mon_trn.instr.rs1_value_type = mon_trn.instr.get_instr_value_type(mon_trn.instr.rs1_value, $bits(mon_trn.instr.rs1_value), rs1_is_signed[mon_trn.instr.name]);
  end
  if (mon_trn.instr.rs2_valid) begin
    mon_trn.instr.rs2_value = rvfi_instr.rs2_rdata;
    mon_trn.instr.rs2_value_type = mon_trn.instr.get_instr_value_type(mon_trn.instr.rs2_value, $bits(mon_trn.instr.rs2_value), rs2_is_signed[mon_trn.instr.name]);
  end
  if (mon_trn.instr.rd_valid) begin
    mon_trn.instr.rd_value  = rvfi_instr.rd1_wdata;
    mon_trn.instr.rd_value_type = mon_trn.instr.get_instr_value_type(mon_trn.instr.rd_value, $bits(mon_trn.instr.rd_value), rd_is_signed[mon_trn.instr.name]);
  end

  // Write to analysis port
  ap.write(mon_trn);

endfunction : write_rvfi_instr


