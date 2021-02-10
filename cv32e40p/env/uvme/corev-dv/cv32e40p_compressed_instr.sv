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
// CORE-V compressed_instruction class
//   Addresses issues with random constraints in riscv-dv
//
// The base test Uses the factory to replace riscv_privil_reg with corev_privil_reg
//------------------------------------------------------------------------------

class cv32e40p_C_LUI_instr extends riscv_C_LUI_instr;

  // Fix an issue with constraints nzimm6 for C_LUI instructions
  // The original definition is in riscv_compressed_instr.sv

  constraint imm_val_c {
    if(imm_type inside {NZIMM, NZUIMM}) {
      imm[5:0] != 0;
      if (instr_name == C_LUI) {
        // Original: imm[31:5] == 0;        
        imm[31:6] == 0;
      }
      if (instr_name inside {C_SRAI, C_SRLI, C_SLLI}) {
        imm[31:5] == 0;
      }
    }
    if (instr_name == C_ADDI4SPN) {
      imm[1:0] == 0;
    }
  }

  `uvm_object_utils(cv32e40p_C_LUI_instr)

  function new(string name="");
    super.new(name);
  endfunction : new

  virtual function void extend_imm();
    bit sign;

    imm = imm << (32 - imm_len);
    sign = imm[31];
    imm = imm >> (32 - imm_len);
    imm_mask = imm_mask << imm_len;
    if (sign) begin
      imm |= imm_mask;      
    end   
  endfunction : extend_imm

  virtual function void update_imm_str();
    if ($signed(imm) < 0) begin
      // GNU Assembler will not accept negative values for LUI even thought actuall nzimm6 range is [-32, 31]
      // Must encode as a hex value to be loaded into upper 20 bits of rd
      // See https://github.com/riscv/riscv-tools/issues/182
      imm_str = $sformatf("0x%x", imm[19:0]);
    end
    else begin
      super.update_imm_str();
    end
  endfunction : update_imm_str

endclass : cv32e40p_C_LUI_instr
