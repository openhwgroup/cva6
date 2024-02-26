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

// HEADERS
+incdir+${RISCV_DV_ROOT}/src
+incdir+${RISCV_DV_ROOT}/test
+incdir+${CVA6_DV_ROOT}/
+incdir+${CVA6_DV_ROOT}/custom
+incdir+${CVA6_DV_ROOT}/user_extension

// SOURCES
${RISCV_DV_ROOT}/src/riscv_signature_pkg.sv
${RISCV_DV_ROOT}/src/riscv_instr_pkg.sv
${RISCV_DV_ROOT}/test/riscv_instr_test_pkg.sv
${CVA6_DV_ROOT}/cva6_signature_pkg.sv
${CVA6_DV_ROOT}/cva6_instr_test_pkg.sv
${CVA6_DV_ROOT}/cva6_instr_gen_tb_top.sv
