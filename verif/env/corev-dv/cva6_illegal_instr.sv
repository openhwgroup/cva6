/*
 * Copyright 2019 Google LLC
 * Copyright 2023 Thales DIS France SAS
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

// ---------------------------------------------------------------------------------------------
// This class is used to generate illegal or HINT instructions.
// The illegal instruction will be generated in binary format and mixed with other valid instr.
// The mixed instruction stream will be stored in data section and loaded to instruction pages
// at run time.
// ---------------------------------------------------------------------------------------------

class cva6_illegal_instr_c extends riscv_illegal_instr;

  `uvm_object_utils(cva6_illegal_instr_c)
  `uvm_object_new

  //Overriding the riscv_illegal_instr to ovveride this constraint, and disable kReservedC* constraint
  constraint reserved_compressed_instr_c {
    solve exception  before reserved_c;
    solve exception  before opcode;
    solve reserved_c before instr_bin;
    solve reserved_c before c_msb;
    solve reserved_c before c_op;
    if (XLEN == 32) {
      //c.addiw is RV64/RV128 only instruction, the encoding is used for C.JAL for RV32C
      reserved_c != kReservedAddiw;
    }
    if (exception == kReservedCompressedInstr) {
      (reserved_c == kIllegalCompressed) -> (instr_bin[15:0] == 0);
      (reserved_c == kReservedAddispn)   -> ((instr_bin[15:5] == '0) && (c_op == 2'b00));
      (reserved_c == kReservedAddiw)     -> ((c_msb == 3'b001) && (c_op == 2'b01) &&
                                             (instr_bin[11:7] == 5'b0));
      reserved_c != kReservedC0;
      reserved_c != kReservedC1;
      reserved_c != kReservedC2;
      (reserved_c == kReservedAddi16sp)  -> ((c_msb == 3'b011) && (c_op == 2'b01) &&
                                             (instr_bin[11:7] == 2) &&
                                             !instr_bin[12] && (instr_bin[6:2] == 0));
      (reserved_c == kReservedLui)       -> ((c_msb == 3'b011) && (c_op == 2'b01) &&
                                             !instr_bin[12] && (instr_bin[6:2] == 0));
      (reserved_c == kReservedJr)        -> (instr_bin == 16'b1000_0000_0000_0010);
      (reserved_c == kReservedLqsp)      -> ((c_msb == 3'b001) && (c_op == 2'b10) &&
                                             (instr_bin[11:7] == 5'b0));
      (reserved_c == kReservedLwsp)      -> ((c_msb == 3'b010) && (c_op == 2'b10) &&
                                             (instr_bin[11:7] == 5'b0));
      (reserved_c == kReservedLdsp)      -> ((c_msb == 3'b011) && (c_op == 2'b10) &&
                                             (instr_bin[11:7] == 5'b0));
    }
  }

  // Invalid SYSTEM instructions
  constraint system_instr_c {
    if (!(SUPERVISOR_MODE inside {supported_privileged_mode})) {
       if (exception == kIllegalSystemInstr) {
         opcode == 7'b1110011;
         func3 == 3'b000;
         // Constrain the upper 12 bits to generate SRET instruction
         instr_bin[31:20] == 12'b100000010;
       }
    }
  }

endclass
