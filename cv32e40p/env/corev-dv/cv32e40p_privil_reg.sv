/*
 * Copyright 2018 Google LLC
 * Copyright 2020 OpenHW Group
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

//------------------------------------------------------------------------------
// CORE-V privileged register class
//     Extends privilege registers for CORE-V core platform extensions
//
// The base test Uses the factory to replace riscv_privil_reg with corev_privil_reg
//------------------------------------------------------------------------------

class cv32e40p_privil_reg extends riscv_privil_reg;

  `uvm_object_utils(cv32e40p_privil_reg);

  function new(string name="");
    super.new(name);
  endfunction

  // Add fields in privileged registers
  function void init_reg(REG_T reg_name);
    super.init_reg(reg_name);
    
    case(reg_name) inside 
      // Machine interrupt-enable register
      MIE: begin
        fld.delete();

        add_field("USIE",   1,  WARL);
        add_field("SSIE",   1,  WARL);
        add_field("WPRI0",  1,  WPRI);
        add_field("MSIE",   1,  WARL);
        add_field("UTIE",   1,  WARL);
        add_field("STIE",   1,  WARL);
        add_field("WPRI1",  1,  WPRI);
        add_field("MTIE",   1,  WARL);
        add_field("UEIE",   1,  WARL);
        add_field("SEIE",   1,  WARL);
        add_field("WPRI2",  1,  WPRI);
        add_field("MEIE",   1,  WARL);
        add_field("WPRI3",  4,  WPRI);
        for (int i = 0; i < 16; i++) begin
          add_field($sformatf("FIE%0d", i), 1, WARL);
        end
      end
      MIP: begin
        fld.delete();

        add_field("USIP",   1,  WARL);
        add_field("SSIP",   1,  WARL);
        add_field("WPRI0",  1,  WPRI);
        add_field("MSIP",   1,  WARL);
        add_field("UTIP",   1,  WARL);
        add_field("STIP",   1,  WARL);
        add_field("WPRI1",  1,  WPRI);
        add_field("MTIP",   1,  WARL);
        add_field("UEIP",   1,  WARL);
        add_field("SEIP",   1,  WARL);
        add_field("WPRI2",  1,  WPRI);
        add_field("MEIP",   1,  WARL);
        add_field("WPRI3",  4,  WPRI);
        for (int i = 0; i < 16; i++) begin
          add_field($sformatf("FIP%0d", i), 1, WARL);
        end
      end
    endcase
  endfunction : init_reg

endclass : cv32e40p_privil_reg
