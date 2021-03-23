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


class uvma_isa_cfg_c extends uvm_object;

  `uvm_object_utils(uvma_isa_cfg_c);

  rand bit                     enabled;
  rand uvm_active_passive_enum is_active;
  rand bit                     cov_model_enabled;
  rand bit                     trn_log_enabled;
  rand bit                     ext_i_enabled;
  rand bit                     ext_m_enabled;
  rand bit                     ext_c_enabled;
  rand bit                     ext_zifencei_enabled;
  rand bit                     ext_zicsr_enabled;

  extern function new(string name = "uvma_isa_cfg");

endclass : uvma_isa_cfg_c


function uvma_isa_cfg_c::new(string name = "uvma_isa_cfg");

  super.new(name);

endfunction : new
