/*
 * Copyright 2019 Google LLC
 * Copyright 2023 Thales DIS
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
// This class is used to generate instruction in extension that do not supported by a given configuration.
// The illegal instruction will be generated in binary format and mixed with other valid instr.
// The mixed instruction stream will be stored in data section and loaded to instruction pages
// at run time.
// ---------------------------------------------------------------------------------------------

class cva6_unsupported_instr_c extends uvm_object;

  string comment;

  typedef enum bit [3:0] {
    rv64i_instr,
    rv64c_instr,
    rv64m_instr,
    rvfdq_instr,
    sys_instr,
    illegal_slli_srai,
    rv64zcb_instr,
    illegal_rv32zcb_instr,
    rv32vf_instr
  } illegal_ext_instr_type_e;

  // Default legal opcode for RV32I instructions
  bit [6:0]  legal_rv64i_opcode[$] = '{7'b0000011,
                                       7'b0100011,
                                       7'b0011011,
                                       7'b0111011};

  bit [6:0]  legal_rvfdq_opcode[$] = '{7'b0000111,
                                       7'b0100111,
                                       7'b1000011,
                                       7'b1000111,
                                       7'b1001011,
                                       7'b1001111,
                                       7'b1010011};

  bit [6:0]  legal_rvfdq_func7[$] = '{7'b0000000,
                                      7'b0000100,
                                      7'b0001000,
                                      7'b0001100,
                                      7'b0101100,
                                      7'b0010000,
                                      7'b1010000,
                                      7'b1101000,
                                      7'b1111000,
                                      7'b0010100,
                                      7'b1100000,
                                      7'b1110000,
                                      7'b0000001,
                                      7'b0000101,
                                      7'b0001001,
                                      7'b0001101,
                                      7'b0101101,
                                      7'b0010001,
                                      7'b0010101,
                                      7'b0100000,
                                      7'b0100001,
                                      7'b1010001,
                                      7'b1110001,
                                      7'b1100001,
                                      7'b1101001,
                                      7'b1111001,
                                      7'b0000011,
                                      7'b0000111,
                                      7'b0001011,
                                      7'b0001111,
                                      7'b0101111,
                                      7'b0010011,
                                      7'b0010111,
                                      7'b0100011,
                                      7'b1010011,
                                      7'b1110011,
                                      7'b1100011,
                                      7'b1101011};

  bit [2:0]  legal_func3[$] = '{3'b000, 
                                3'b001, 
                                3'b010,
                                3'b011, 
                                3'b100};

  bit [1:0]  legal_func2[$] = '{2'b00,
                                2'b01,
                                2'b11};

  rand illegal_ext_instr_type_e  unsupported_instr;
  rand bit [31:0]                instr_bin;
  rand bit [6:0]                 opcode;
  rand bit [2:0]                 func3;
  rand bit [1:0]                 func2;
  rand bit [6:0]                 func7;
  rand bit                       has_func3;
  rand bit                       has_func7;
  rand bit                       has_func2;
  rand bit                       compressed;
  rand bit [1:0]                 c_op;
  rand bit [2:0]                 c_msb;
  cva6_instr_gen_config_c        cfg_cva6;

  constraint exception_dist_c {
    unsupported_instr dist {
      rv64i_instr := 3,
      rv64c_instr := 3,
      rv64m_instr := 3,
      rvfdq_instr := 3,
      sys_instr   := 1,
      illegal_slli_srai := 1,
      rv64zcb_instr := 1,
      illegal_rv32zcb_instr := 1,
      rv32vf_instr :=1
    };
  }

  constraint instr_bit_assignment_c {
    solve opcode before instr_bin;
    solve func3 before instr_bin;
    solve func2 before instr_bin;
    solve func7 before instr_bin;
    solve c_msb before instr_bin;
    solve c_op before instr_bin;
    if (compressed) {
      instr_bin[1:0] == c_op;
      instr_bin[15:13] == c_msb;
    } else {
      instr_bin[6:0] == opcode;
      if (has_func7) {
        instr_bin[31:25] == func7;
      }
      if (has_func3) {
        instr_bin[14:12] == func3;
      }
      if (has_func2) {
        instr_bin[26:25] == func2;
      }
    }
  }

  // unsupported system instructions
  // sfence.vma instruction
  constraint sys_instr_c {
    if (unsupported_instr == sys_instr) {
         compressed == 0;
         opcode == 7'b1110011;
         func3 == 3'b000;
         instr_bin[11:7] inside {5'b0, 5'b00001};
         func7 inside {7'b1111111, 7'b0001001};
    }
  }

  // illegal RV32 SLLI & SRAI instruction with 25th bit is high
  constraint illegal_slli_srai_32_instr_c {
    if (unsupported_instr == illegal_slli_srai) {
         compressed == 0;
         opcode == 7'b0010011;
         instr_bin[25] != 1'b0;
         func3 inside {3'b001, 3'b101};
         if (func3 == 3'b001) {
            instr_bin[31:26] == 6'b000000;
         }
         else if (func3 == 3'b101) {
            instr_bin[31:26] == 6'b010000;
         }
    }
  }

  // RV64I instructions
  constraint rv64i_instr_c {
    if (!(RV64I inside {supported_isa})) {
      if (unsupported_instr == rv64i_instr) {
        compressed == 0;
        opcode inside {legal_rv64i_opcode};
        func3 inside {3'b110, 3'b011, 3'b001, 3'b101, 3'b0};
        if (opcode == 7'b0000011) {
           func3 inside {3'b110, 3'b011};
        }
        if (opcode == 7'b0100011) {
           func3 == 3'b011;
        }
        if (opcode == 7'b0011011) {
           func3 inside {3'b101, 3'b001, 3'b0};
           if (func3 == 3'b101) {
              func7 inside {7'b0, 7'b0100000};
           }
           if (func3 == 3'b001) {
              func7 == 7'b0;
           }
        }
        if (opcode == 7'b0111011) {
           func3 inside {3'b101, 3'b001, 3'b0};
           if (func3 == 3'b0) {
              func7 inside {7'b0, 7'b0100000};
           }
           if (func3 == 3'b001) {
              func7 == 7'b0;
           }
           if (func3 == 3'b101) {
              func7 inside {7'b0, 7'b0100000};
           }
        }
      }
    }
  }

  // RV64M instructions
  constraint rv64m_instr_c {
    if (!(RV64M inside {supported_isa})) {
      if (unsupported_instr == rv64m_instr) {
           compressed == 0;
           opcode == 7'b0111011;
           func3 inside {3'b100, 3'b110, 3'b000, 3'b101, 3'b111};
           func7 == 7'b0000001;
      }
    }
  }

  // RV32 Vectorial FP instructions
  constraint rv32vf_instr_c {
    if (unsupported_instr == rv32vf_instr) {
         compressed == 0;
         opcode == 7'b0110011;
         instr_bin[31:30] == 2'b10;
    }
  }

  // RV64C instructions
  constraint rv64c_instr_c {
    if (!(RV64C inside {supported_isa}) ||
        !(RV32FC inside {supported_isa}) ||
        !(RV32DC inside {supported_isa}) ||
        !(RV128C inside {supported_isa})) {
      if (unsupported_instr == rv64c_instr) {
           compressed == 1;
           c_op != 2'b11;
           if (c_op == 2'b0) {
              !(c_msb inside {3'b0, 3'b010, 3'b100, 3'b110});
           }
           if (c_op == 2'b01) {
              c_msb == 3'b100;
              instr_bin[12:10] inside {3'b0, 3'b001, 3'b111};
              if (instr_bin[12:10] != 3'b111) {
                 instr_bin[6:2] == 5'b0;
              }
              else {
                !(instr_bin[6:5] inside {2'b10, 2'b11});
              }
           }
           if (c_op == 2'b10) {
              !(c_msb inside {3'b100, 3'b010, 3'b110});
              if (c_msb == 3'b0) {
                 instr_bin[6:2] == 5'b0;
                 instr_bin[12] == 1'b0;
              }
           }
      }
    }
  }

  // RV64Zcb instructions
  constraint rv64zcb_instr_c {
    if (unsupported_instr == rv64zcb_instr) {
         compressed == 1;
         c_op  == 2'b01;
         c_msb == 3'b100;
         instr_bin[12:10] == 3'b111;
         instr_bin[6:2] == 5'b11100;
    }
  }

  // Illegal RV32Zcb instructions
  constraint illegal_rv32zcb_instr_c {
    if (unsupported_instr == illegal_rv32zcb_instr) {
         compressed == 1;
         c_op inside {2'b00, 2'b01};
         c_msb == 3'b100;
         if (c_op == 2'b00) {
            !(instr_bin[12:10] inside {3'b000, 3'b001, 3'b010, 3'b011});
         }
         if (c_op == 2'b01) {
            instr_bin[12:10] == 3'b111;
            !(instr_bin[4:2] inside {3'b000, 3'b001, 3'b010, 3'b011, 3'b100, 3'b101});
            instr_bin[6:5] == 2'b11;
         }
    }
  }

  // RV32FDQ, RV64FDQ instructions
  constraint rvfdq_instr_c {
    if (!(RV32F inside {supported_isa}) ||
        !(RV64F inside {supported_isa}) ||
        !(RV32D inside {supported_isa}) ||
        !(RV64D inside {supported_isa})) {
      if (unsupported_instr == rvfdq_instr) {
        compressed == 0;
        opcode inside {legal_rvfdq_opcode};
        func7 inside {legal_rvfdq_func7};
        if (opcode == 7'b0000111) {
           func3 inside {3'b010, 3'b011, 3'b100};
        }
        if (opcode == 7'b0100111) {
           func3 inside {3'b010, 3'b011, 3'b100};
        }
        if (opcode == 7'b1000011) {
           func2 inside {legal_func2};
        }
        if (opcode == 7'b1000111) {
           func2 inside {legal_func2};
        }
        if (opcode == 7'b1001011) {
           func2 inside {legal_func2};
        }
        if (opcode == 7'b1001111) {
           func2 inside {legal_func2};
        }
        if (opcode == 7'b1010011) {
           func3 inside {3'b0, 3'b010, 3'b001};
           if (func3 == 3'b0) {
              func7 inside {7'b0010000,7'b0010100,7'b1110000,7'b1010000,
                            7'b1111000,7'b0010001,7'b0010101,7'b1010001,
                            7'b1110001,7'b1111001,7'b0010011,7'b0010111,
                            7'b1010011};
              if (func7 == 7'b1110000) {
                 instr_bin[24:20] == 5'b0;
              }
              if (func7 == 7'b1111000) {
                 instr_bin[24:20] == 5'b0;
              }
              if (func7 == 7'b1110001) {
                 instr_bin[24:20] == 5'b0;
              }
              if (func7 == 7'b1111001) {
                 instr_bin[24:20] == 5'b0;
              }
           }
           if (func3 == 3'b001) {
              func7 inside {7'b0010000,7'b0010100,7'b1110000,7'b1010000,
                            7'b0010001,7'b0010101,7'b1010001,7'b1110001,
                            7'b1010011,7'b1110011,7'b0010011,7'b0010111};
              if (func7 == 7'b1110000) {
                 instr_bin[24:20] == 5'b0;
              }
              if (func7 == 7'b1110001) {
                 instr_bin[24:20] == 5'b0;
              }
              if (func7 == 7'b1110011) {
                 instr_bin[24:20] == 5'b0;
              }
           }
           if (func3 == 3'b010) {
              func7 inside {7'b0010000,7'b1010000,7'b0010001,7'b1010001,
                            7'b0010011,7'b1010011};
           }
           if (func7 == 7'b0101100) {
              instr_bin[24:20] == 5'b0;
           }
           if (func7 == 7'b1100000) {
              instr_bin[24:20] inside {5'b0, 5'b00001, 5'b00010, 5'b00011};
           }
           if (func7 == 7'b1101000) {
              instr_bin[24:20] inside {5'b0, 5'b00001, 5'b00010, 5'b00011};
           }
           if (func7 == 7'b0101101) {
              instr_bin[24:20] == 5'b0;
           }
           if (func7 == 7'b0100000) {
              instr_bin[24:20] inside {5'b00001, 5'b00011};
           }
           if (func7 == 7'b0100001) {
              instr_bin[24:20] inside {5'b0, 5'b00011};
           }
           if (func7 == 7'b1100001) {
              instr_bin[24:20] inside {5'b0, 5'b00001, 5'b00010, 5'b00011};
           }
           if (func7 == 7'b1101001) {
              instr_bin[24:20] inside {5'b0, 5'b00001, 5'b00010, 5'b00011};
           }
           if (func7 == 7'b0101111) {
              instr_bin[24:20] == 5'b0;
           }
           if (func7 == 7'b0100011) {
              instr_bin[24:20] inside {5'b0, 5'b00001};
           }
           if (func7 == 7'b1100011) {
              instr_bin[24:20] inside {5'b0, 5'b00001, 5'b00010, 5'b00011};
           }
           if (func7 == 7'b1101011) {
              instr_bin[24:20] inside {5'b0, 5'b00001, 5'b00010, 5'b00011};
           }
        }
      }
    }
  }

  constraint has_func7_c {
    solve opcode before func7;
    solve func7 before func3;
    if (opcode inside {7'b0111011, 7'b1110011}) {
      has_func3 == 1'b1;
      has_func7 == 1'b1;
      has_func2 == 1'b0;  
    }
    if (opcode inside {legal_rv64i_opcode}) {
      has_func3 == 1'b1;
      has_func2 == 1'b0;
      if (((opcode == 7'b0011011) && (func3 == 3'b000)) ||
         (opcode inside {7'b0000011, 7'b0100011})) {
        has_func7 == 1'b0;
      } else {
        has_func7 == 1'b1;
      }
    }
    if (opcode inside {7'b0000111, 7'b0100111, 7'b0010011}) {
      has_func2 == 1'b0;
      has_func3 == 1'b1;
      has_func7 == 1'b0;
    }
    if (opcode inside {7'b1000011, 7'b1000111, 7'b1001011, 7'b1001111}) {
      has_func2 == 1'b1;
      has_func3 == 1'b0;
      has_func7 == 1'b0;
    }
    if (opcode == 7'b1010011) {
      has_func2 == 1'b0;
      has_func7 == 1'b1;
      if (func7 inside {7'b0010000, 7'b0010100, 7'b1110000, 7'b1010000, 7'b1110000, 7'b1111000,
                        7'b0010001, 7'b0010101, 7'b1010001, 7'b1110001, 7'b1111001, 7'b0010011,
                        7'b0010011, 7'b0010111, 7'b1010011, 7'b1110011}) {
         has_func3 == 1'b1;
      } else {
         has_func3 == 1'b0;
      }
    }
  }

  `uvm_object_utils(cva6_unsupported_instr_c)
  `uvm_object_new

  function string get_bin_str();
    if (compressed) begin
      get_bin_str = $sformatf("%4h", instr_bin[15:0]);
    end else begin
      get_bin_str = $sformatf("%8h", instr_bin[31:0]);
    end
    `uvm_info(`gfn, $sformatf("unsupported extension instruction type: %0s, unsupported instruction: 0x%0x",
                               unsupported_instr.name(), instr_bin), UVM_HIGH)
  endfunction

  function void post_randomize();
    comment = unsupported_instr.name();
    if (unsupported_instr == rv64i_instr) begin
      comment = {comment};
    end else if (unsupported_instr == rv64m_instr) begin
      comment = {comment};
    end else if (unsupported_instr == rvfdq_instr) begin
      comment = {comment};
    end else if (unsupported_instr == rv64c_instr) begin
      comment = {comment};
   end
   endfunction

endclass
