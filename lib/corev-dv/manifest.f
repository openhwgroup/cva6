// Copyright 2018 Google LLC
// Copyright 2020 OpenHW Group
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// HEADERS
+incdir+${RISCV_DV_ROOT}/src
+incdir+${RISCV_DV_ROOT}/test

// SOURCES
${RISCV_DV_ROOT}/src/riscv_signature_pkg.sv
${RISCV_DV_ROOT}/src/riscv_instr_pkg.sv
${RISCV_DV_ROOT}/test/riscv_instr_test_pkg.sv

// General CORE-V-VERIF
${COREV_DV_ROOT}/corev_instr_test_pkg.sv

// Core-specific CORE-V-VERIF
${CV_CORE_COREV_DV_ROOT}/${CV_CORE_LC}_instr_test_pkg.sv
${CV_CORE_COREV_DV_ROOT}/${CV_CORE_LC}_instr_gen_tb_top.sv
