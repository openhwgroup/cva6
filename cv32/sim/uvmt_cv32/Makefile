###############################################################################
#
# Copyright 2020 OpenHW Group
# 
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
# 
#     https://solderpad.org/licenses/
# 
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
# 
###############################################################################
#
# Makefile for the CV32E40P "uvmt_cv32" testbench.  Substantially modified
# from the original Makefile for the RI5CY testbench.
#
###############################################################################
# 
# Copyright 2019 Clifford Wolf
# Copyright 2019 Robert Balas
#
# Permission to use, copy, modify, and/or distribute this software for any
# purpose with or without fee is hereby granted, provided that the above
# copyright notice and this permission notice appear in all copies.
#
# THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES WITH
# REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF MERCHANTABILITY
# AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY SPECIAL, DIRECT,
# INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES WHATSOEVER RESULTING FROM
# LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION OF CONTRACT, NEGLIGENCE OR
# OTHER TORTIOUS ACTION, ARISING OUT OF OR IN CONNECTION WITH THE USE OR
# PERFORMANCE OF THIS SOFTWARE.
#
# Original Author: Robert Balas (balasr@iis.ee.ethz.ch)
#
###############################################################################

# "Constants"
MAKE           = make
MAKE_PATH     := $(shell dirname $(realpath $(firstword $(MAKEFILE_LIST))))
COREV_PROJ     = cv32
PROJ_ROOT_DIR  = $(abspath $(MAKE_PATH)/../../..)
DATE           = $(shell date +%F)
.DEFAULT_GOAL := no_rule 

# Useful commands
MKDIR_P = mkdir -p

# Compile compile flags for all simulators (careful!)
WAVES        ?= 0
SV_CMP_FLAGS ?= 
TIMESCALE    ?= -timescale 1ns/1ps
UVM_PLUSARGS ?=

# User selectable SystemVerilog simulator targets/rules
CV_SIMULATOR ?= unsim
SIMULATOR    ?= $(CV_SIMULATOR)

# Optionally exclude the OVPsim (not recommended)
USE_ISS      ?= YES

# UVM Environment
export DV_UVMT_CV32_PATH      = $(PROJ_ROOT_DIR)/$(COREV_PROJ)/tb/uvmt_cv32
export DV_UVME_CV32_PATH      = $(PROJ_ROOT_DIR)/$(COREV_PROJ)/env/uvme_cv32
export DV_UVML_HRTBT_PATH     = $(PROJ_ROOT_DIR)/lib/uvm_libs/uvml_hrtbt
export DV_UVMA_CLKNRST_PATH   = $(PROJ_ROOT_DIR)/lib/uvm_agents/uvma_clknrst
export DV_UVMA_INTERRUPT_PATH = $(PROJ_ROOT_DIR)/lib/uvm_agents/uvma_interrupt
export DV_UVML_TRN_PATH       = $(PROJ_ROOT_DIR)/lib/uvm_libs/uvml_trn
export DV_UVML_LOGS_PATH      = $(PROJ_ROOT_DIR)/lib/uvm_libs/uvml_logs
export DV_UVML_SB_PATH        = $(PROJ_ROOT_DIR)/lib/uvm_libs/uvml_sb
  
export DV_OVPM_HOME           = $(PROJ_ROOT_DIR)/vendor_lib/imperas
export DV_OVPM_MODEL          = $(DV_OVPM_HOME)/riscv_CV32E40P_OVPsim
export DV_OVPM_DESIGN         = $(DV_OVPM_HOME)/verilog/design

DV_UVMT_CV32_SRCS  = $(wildcard $(DV_UVMT_CV32_PATH)/*.sv))

# Testcase name: must be the CLASS name of the testcase (not the filename).
# Look in ../../tests/uvmt_cv32.
UVM_TESTNAME ?= uvmt_cv32_firmware_test_c

# Google's random instruction generator
RISCVDV_PKG   := $(PROJ_ROOT_DIR)/vendor_lib/google/riscv-dv
COREVDV_PKG   := $(PROJ_ROOT_DIR)/vendor_lib/google/corev-dv
export RISCV_DV_ROOT = $(RISCVDV_PKG)
export COREV_DV_ROOT = $(COREVDV_PKG)

# RISC-V Foundation's RISC-V Compliance Test-suite
COMPLIANCE_PKG   := $(PROJ_ROOT_DIR)/vendor_lib/riscv/riscv-compliance

# TB source files for the CV32E core
TBSRC_TOP   := $(TBSRC_HOME)/uvmt_cv32/uvmt_cv32_tb.sv
TBSRC_HOME  := $(PROJ_ROOT_DIR)/$(COREV_PROJ)/tb
export TBSRC_HOME  = $(PROJ_ROOT_DIR)/$(COREV_PROJ)/tb

SIM_LIBS    := $(PROJ_ROOT_DIR)/lib/sim_libs

RTLSRC_VLOG_TB_TOP	:= $(basename $(notdir $(TBSRC_TOP)))
RTLSRC_VOPT_TB_TOP	:= $(addsuffix _vopt, $(RTLSRC_VLOG_TB_TOP))

# RTL source files for the CV32E core
# DESIGN_RTL_DIR is used by CV32E40P_MANIFEST file
CV32E40P_PKG         := $(PROJ_ROOT_DIR)/core-v-cores/cv32e40p
FPNEW_PKG            := $(CV32E40P_PKG)/rtl/fpnew
CV32E40P_MANIFEST    := $(CV32E40P_PKG)/cv32e40p_manifest.flist
export DESIGN_RTL_DIR = $(CV32E40P_PKG)/rtl

RTLSRC_HOME   := $(CV32E40P_PKG)/rtl
RTLSRC_INCDIR := $(RTLSRC_HOME)/include

###############################################################################
# Seed management for constrained-random sims
SEED    ?= 1
RNDSEED ?= 

ifeq ($(SEED),random)
RNDSEED = $(shell date +%N)
else
ifeq ($(SEED),)
# Empty SEED variable selects 1
RNDSEED = 1
else
RNDSEED = $(SEED)
endif
endif

###############################################################################
# Common Makefile:
#    - Core Firmware and the RISCV GCC Toolchain (SDK)
#    - Variables for RTL dependencies
include $(MAKE_PATH)/../Common.mk


###############################################################################
# Clone CV32E40P RTL and DV dependencies
clone_cv32e40p_rtl:
	$(CLONE_CV32E40P_CMD)

clone_fpnew_rtl: clone_cv32e40p_rtl
	$(CLONE_FPNEW_CMD)

clone_riscv-dv:
	$(CLONE_RISCVDV_CMD)

clone_compliance:
	$(CLONE_COMPLIANCE_CMD)

$(CV32E40P_PKG):
	$(CLONE_CV32E40P_CMD)
	$(CLONE_FPNEW_CMD)


###############################################################################
# Include the targets/rules for the selected SystemVerilog simulator
#ifeq ($(SIMULATOR), unsim)
#include unsim.mk
#else
ifeq ($(SIMULATOR), dsim)
include $(MAKE_PATH)/dsim.mk
else
ifeq ($(SIMULATOR), xrun)
include $(MAKE_PATH)/xrun.mk
else
ifeq ($(SIMULATOR), vsim)
include $(MAKE_PATH)/vsim.mk
else
ifeq ($(SIMULATOR), vcs)
include $(MAKE_PATH)/vcs.mk
else
include $(MAKE_PATH)/unsim.mk
endif
endif
endif
endif
#endif


###############################################################################
# Clean up your mess!
#   1. Clean all generated files of the C and assembler tests in tests/core
#      Note: CORE_TEST_DIR is defined in ../Common.mk
#   2. Simulator-specific clean targets are in ./<simulator>.mk
clean_core_tests:
	find $(CORE_TEST_DIR) -name *.o       -exec rm {} \;
	find $(CORE_TEST_DIR) -name *.hex     -exec rm {} \;
	find $(CORE_TEST_DIR) -name *.elf     -exec rm {} \;
	find $(CORE_TEST_DIR) -name *.map     -exec rm {} \;
	find $(CORE_TEST_DIR) -name *.readelf -exec rm {} \;
	find $(CORE_TEST_DIR) -name *.objdump -exec rm {} \;
	find $(CORE_TEST_DIR) -name corev_*.S -exec rm {} \;

clean_test_programs:
	find $(PROJ_ROOT_DIR)/cv32/tests/uvmt_cv32/test-programs -name *.o       -exec rm {} \;
	find $(PROJ_ROOT_DIR)/cv32/tests/uvmt_cv32/test-programs -name *.hex     -exec rm {} \;
	find $(PROJ_ROOT_DIR)/cv32/tests/uvmt_cv32/test-programs -name *.elf     -exec rm {} \;
	find $(PROJ_ROOT_DIR)/cv32/tests/uvmt_cv32/test-programs -name *.map     -exec rm {} \;
	find $(PROJ_ROOT_DIR)/cv32/tests/uvmt_cv32/test-programs -name *.readelf -exec rm {} \;
	find $(PROJ_ROOT_DIR)/cv32/tests/uvmt_cv32/test-programs -name *.objdump -exec rm {} \;

clean_riscv-dv:
	rm -rf $(RISCVDV_PKG)
	rm -rf $(COREVDV_PKG)/out_*
	find ../../tests/core/google-riscv-dv -name "*.S" -exec rm {} \;

clean_compliance:
	rm -rf $(COMPLIANCE_PKG)

