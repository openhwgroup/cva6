/*
 * Copyright 2018 Google LLC
 * Copyright 2023 Thales
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

//-----------------------------------------------------------------------------
// RISC-V assembly program generator configuration class
//-----------------------------------------------------------------------------

class cva6_instr_gen_config_c extends riscv_instr_gen_config;

  //-----------------------------------------------------------------------------
  // Random instruction generation option
  //-----------------------------------------------------------------------------

  // cvxif extension support
  bit                     enable_x_extension;
  bit                     enable_rdrs1_hazard;
  bit                     enable_rdrs2_hazard;
  bit                     enable_same_reg;
  bit                     enable_zicond_extension;
  bit                     enable_zcb_extension;
  bit                     enable_zcmp_extension;
  int                     unsupported_instr_ratio;

  constraint hazard_reg_c {
    if (enable_same_reg) {
      enable_rdrs1_hazard == 1'b0;
      enable_rdrs2_hazard == 1'b0;
    }
  }

  constraint mtvec_mode_c {
    mtvec_mode == DIRECT;
  }

    `uvm_object_utils_begin(cva6_instr_gen_config_c)
      `uvm_field_int(enable_x_extension, UVM_DEFAULT)
      `uvm_field_int(enable_rdrs1_hazard, UVM_DEFAULT)
      `uvm_field_int(enable_rdrs2_hazard, UVM_DEFAULT)
      `uvm_field_int(enable_same_reg, UVM_DEFAULT)
      `uvm_field_int(enable_zicond_extension, UVM_DEFAULT)
      `uvm_field_int(enable_zcb_extension, UVM_DEFAULT)
      `uvm_field_int(enable_zcmp_extension, UVM_DEFAULT)
      `uvm_field_int(unsupported_instr_ratio, UVM_DEFAULT)
    `uvm_object_utils_end

  function new (string name = "");
    super.new(name);
    get_bool_arg_value("+enable_x_extension=", enable_x_extension);
    get_bool_arg_value("+enable_rdrs1_hazard=", enable_rdrs1_hazard);
    get_bool_arg_value("+enable_rdrs2_hazard=", enable_rdrs2_hazard);
    get_bool_arg_value("+enable_same_reg=", enable_same_reg);
    get_bool_arg_value("+enable_zicond_extension=", enable_zicond_extension);
    get_bool_arg_value("+enable_zcb_extension=", enable_zcb_extension);
    get_bool_arg_value("+enable_zcmp_extension=", enable_zcmp_extension);
    get_int_arg_value("+unsupported_instr_ratio=", unsupported_instr_ratio);
  endfunction

endclass : cva6_instr_gen_config_c
