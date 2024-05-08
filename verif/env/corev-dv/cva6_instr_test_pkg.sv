// Copyright 2022 Thales DIS design services SAS
// Copyright 2022 OpenHW Group
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Zineb EL KACIMI (zineb.el-kacimi@external.thalesgroup.com)
// ------------------------------------------------------------------------------ //

package cva6_instr_test_pkg;

   import uvm_pkg::*;
   `include "cva6_defines.svh"
   import riscv_instr_pkg::*;
   import riscv_instr_test_pkg::*;
   import cva6_signature_pkg::*;

   `include "cva6_instr_gen_config.sv"
   `include "cva6_unsupported_instr.sv"
   `include "cva6_illegal_instr.sv"
   `include "cva6_reg_hazard_stream.sv"
   `include "cva6_instr_sequence.sv"
   `include "cva6_asm_program_gen.sv"
   `include "cva6_instr_base_test.sv"
   `include "cva6_instr_hazard_test.sv"
   `include "cva6_load_store_instr_lib.sv"
   `include "cva6_ecall_instr_stream.sv"
   `include "cvxif_custom_instr.sv"
   `include "riscv_zicond_instr.sv"
   `include "riscv_zcb_instr.sv"
   `include "riscv_zcmp_instr.sv"
   `include "rv32x_instr.sv"
   `include "rv32zicond_instr.sv"
   `include "rv32zcb_instr.sv"
   `include "rv32zcmp_instr.sv"
   `include "rv64zcb_instr.sv"
   
endpackage : cva6_instr_test_pkg
