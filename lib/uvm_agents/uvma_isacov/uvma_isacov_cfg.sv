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


class uvma_isacov_cfg_c extends uvm_object;

  rand bit                     enabled;
  rand uvm_active_passive_enum is_active;

  rand bit                     cov_model_enabled;
  rand bit                     trn_log_enabled;
  rand bit                     ext_i_enabled;
  rand bit                     ext_m_enabled;
  rand bit                     ext_c_enabled;
  rand bit                     ext_a_enabled;  
  rand bit                     ext_zifencei_enabled;
  rand bit                     ext_zicsr_enabled;

  rand bit                     mode_s_enabled;
  rand bit                     mode_u_enabled;

  rand bit                     seq_instr_group_x2_enabled;
  rand bit                     seq_instr_group_x3_enabled;
  rand bit                     seq_instr_group_x4_enabled;

  // Bitmask to enable/disable CSRs in coverage model
  // Mode configurations above will set cfg_illegal_csr settings when predictable
  // Users may set any bit to 1 in this bitmask to signal that a respective CSR should be
  // considered illegal
  bit [CSR_MASK_WL-1:0]        cfg_illegal_csr;

  `uvm_object_utils_begin(uvma_isacov_cfg_c);
    `uvm_field_int(enabled, UVM_DEFAULT);
    `uvm_field_enum(uvm_active_passive_enum, is_active, UVM_DEFAULT);
    `uvm_field_int(cov_model_enabled, UVM_DEFAULT);
    `uvm_field_int(trn_log_enabled, UVM_DEFAULT);
    `uvm_field_int(ext_i_enabled, UVM_DEFAULT);
    `uvm_field_int(ext_m_enabled, UVM_DEFAULT);
    `uvm_field_int(ext_c_enabled, UVM_DEFAULT);
    `uvm_field_int(ext_a_enabled, UVM_DEFAULT);
    `uvm_field_int(ext_zifencei_enabled, UVM_DEFAULT);
    `uvm_field_int(ext_zicsr_enabled, UVM_DEFAULT);
    `uvm_field_int(mode_s_enabled, UVM_DEFAULT);
    `uvm_field_int(mode_u_enabled, UVM_DEFAULT);
    `uvm_field_int(seq_instr_group_x2_enabled, UVM_DEFAULT);
    `uvm_field_int(seq_instr_group_x3_enabled, UVM_DEFAULT);
    `uvm_field_int(seq_instr_group_x4_enabled, UVM_DEFAULT);
    `uvm_field_int(cfg_illegal_csr, UVM_DEFAULT | UVM_NOPRINT);
  `uvm_object_utils_end;

  extern function new(string name = "uvma_isacov_cfg");

  extern function void post_randomize();
endclass : uvma_isacov_cfg_c

function uvma_isacov_cfg_c::new(string name = "uvma_isacov_cfg");

  super.new(name);

  // Populate initial cfg_illegal_csr mask based on CSR types mapped in enum instr_csr_t
  cfg_illegal_csr = '1;
  begin
    instr_csr_t csr = csr.first();
    forever begin
      cfg_illegal_csr[csr] = 0;
      if (csr == csr.last()) break;
      csr = csr.next();
    end
  end
endfunction : new

function void uvma_isacov_cfg_c::post_randomize();
  if (!mode_s_enabled) begin
    cfg_illegal_csr[SSTATUS] = 1;
    cfg_illegal_csr[SEDELEG] = 1;
    cfg_illegal_csr[SIE] = 1;
    cfg_illegal_csr[STVEC] = 1;
    cfg_illegal_csr[SCOUNTEREN] = 1;
    cfg_illegal_csr[SSCRATCH] = 1;
    cfg_illegal_csr[SEPC] = 1;
    cfg_illegal_csr[SCAUSE] = 1;
    cfg_illegal_csr[STVAL] = 1;
    cfg_illegal_csr[SIP] = 1;
    cfg_illegal_csr[SATP] = 1;
  end

  if (!mode_u_enabled) begin
    cfg_illegal_csr[USTATUS] = 1;
    cfg_illegal_csr[UIE] = 1;
    cfg_illegal_csr[UTVEC] = 1;    
    cfg_illegal_csr[USCRATCH] = 1;
    cfg_illegal_csr[UEPC] = 1;
    cfg_illegal_csr[UCAUSE] = 1;
    cfg_illegal_csr[UTVAL] = 1;
    cfg_illegal_csr[UIP] = 1;    
  end

endfunction : post_randomize
