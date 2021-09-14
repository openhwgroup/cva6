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

  rand bit                     seq_instr_group_x2_enabled;
  rand bit                     seq_instr_group_x3_enabled;
  rand bit                     seq_instr_group_x4_enabled;

  rand bit                     seq_instr_x2_enabled;

  rand bit                     reg_crosses_enabled;
  rand bit                     reg_hazards_enabled;

  // Core configuration object to filter extensions, csrs, modes, supported
  uvma_core_cntrl_cfg_c        core_cfg;

  `uvm_object_utils_begin(uvma_isacov_cfg_c);
    `uvm_field_int(enabled, UVM_DEFAULT);
    `uvm_field_enum(uvm_active_passive_enum, is_active, UVM_DEFAULT);
    `uvm_field_int(cov_model_enabled, UVM_DEFAULT);
    `uvm_field_int(trn_log_enabled, UVM_DEFAULT);

    `uvm_field_int(seq_instr_group_x2_enabled, UVM_DEFAULT);
    `uvm_field_int(seq_instr_group_x3_enabled, UVM_DEFAULT);
    `uvm_field_int(seq_instr_group_x4_enabled, UVM_DEFAULT);
    `uvm_field_int(seq_instr_x2_enabled, UVM_DEFAULT);
    `uvm_field_int(reg_crosses_enabled, UVM_DEFAULT);
    `uvm_field_int(reg_hazards_enabled, UVM_DEFAULT);
  `uvm_object_utils_end;

  extern function new(string name = "uvma_isacov_cfg");

endclass : uvma_isacov_cfg_c

function uvma_isacov_cfg_c::new(string name = "uvma_isacov_cfg");

  super.new(name);

endfunction : new

