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
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
#
###############################################################################
#
# Makefile for the CORE testbench for multiple OpenHW-verified cores.
#
###############################################################################

# Variable checks
ifndef CV_CORE
$(error Must set CV_CORE to a valid core)
endif

# "Constants"
DATE           = $(shell date +%F)
CV_CORE_LC     = $(shell echo $(CV_CORE) | tr A-Z a-z)
CV_CORE_UC     = $(shell echo $(CV_CORE) | tr a-z A-Z)
export CV_CORE_LC
export CV_CORE_UC
.DEFAULT_GOAL := no_rule

# Useful commands
MKDIR_P = mkdir -p

# Compile compile flags for all simulators (careful!)
WAVES        ?= 0
SV_CMP_FLAGS ?= "+define+$(CV_CORE_UC)_ASSERT_ON"
TIMESCALE    ?= -timescale 1ns/1ps
UVM_PLUSARGS ?=

# User selectable SystemVerilog simulator targets/rules
CV_SIMULATOR ?= unsim
SIMULATOR    ?= $(CV_SIMULATOR)

# Optionally exclude the OVPsim (not recommended)
USE_ISS      ?= YES

# Common configuration variables
CFG             ?= default

# Common Generation variables
GEN_START_INDEX ?= 0
GEN_NUM_TESTS   ?= 1

# Commont test variables
RUN_INDEX       ?= 0

# UVM Environment
export DV_UVMT_PATH           = $(CORE_V_VERIF)/$(CV_CORE_LC)/tb/uvmt
export DV_UVME_PATH           = $(CORE_V_VERIF)/$(CV_CORE_LC)/env/uvme
export DV_UVML_HRTBT_PATH     = $(CORE_V_VERIF)/lib/uvm_libs/uvml_hrtbt
export DV_UVMA_ISACOV_PATH    = $(CORE_V_VERIF)/lib/uvm_agents/uvma_isacov
export DV_UVMA_CLKNRST_PATH   = $(CORE_V_VERIF)/lib/uvm_agents/uvma_clknrst
export DV_UVMA_INTERRUPT_PATH = $(CORE_V_VERIF)/lib/uvm_agents/uvma_interrupt
export DV_UVMA_DEBUG_PATH     = $(CORE_V_VERIF)/lib/uvm_agents/uvma_debug
export DV_UVML_TRN_PATH       = $(CORE_V_VERIF)/lib/uvm_libs/uvml_trn
export DV_UVML_LOGS_PATH      = $(CORE_V_VERIF)/lib/uvm_libs/uvml_logs
export DV_UVML_SB_PATH        = $(CORE_V_VERIF)/lib/uvm_libs/uvml_sb

export DV_OVPM_HOME           = $(CORE_V_VERIF)/vendor_lib/imperas
export DV_OVPM_MODEL          = $(DV_OVPM_HOME)/imperas_DV_COREV
export DV_OVPM_DESIGN         = $(DV_OVPM_HOME)/design

DV_UVMT_SRCS                  = $(wildcard $(DV_UVMT_PATH)/*.sv))

# Testcase name: must be the CLASS name of the testcase (not the filename).
# Look in ../../tests/uvmt
UVM_TESTNAME ?= uvmt_$(CV_CORE_LC)_firmware_test_c

# Google's random instruction generator
RISCVDV_PKG         := $(CORE_V_VERIF)/$(CV_CORE_LC)/vendor_lib/google/riscv-dv
COREVDV_PKG         := $(CORE_V_VERIF)/lib/corev-dv
CV_CORE_COREVDV_PKG := $(CORE_V_VERIF)/$(CV_CORE_LC)/env/corev-dv
export RISCV_DV_ROOT         = $(RISCVDV_PKG)
export COREV_DV_ROOT         = $(COREVDV_PKG)
export CV_CORE_COREV_DV_ROOT = $(CV_CORE_COREVDV_PKG)

# RISC-V Foundation's RISC-V Compliance Test-suite
COMPLIANCE_PKG   := $(CORE_V_VERIF)/$(CV_CORE_LC)/vendor_lib/riscv/riscv-compliance

# TB source files for the CV32E core
TBSRC_TOP   := $(TBSRC_HOME)/uvmt/uvmt_$(CV_CORE_LC)_tb.sv
TBSRC_HOME  := $(CORE_V_VERIF)/$(CV_CORE_LC)/tb
export TBSRC_HOME = $(CORE_V_VERIF)/$(CV_CORE_LC)/tb

SIM_LIBS    := $(CORE_V_VERIF)/lib/sim_libs

RTLSRC_VLOG_TB_TOP	:= $(basename $(notdir $(TBSRC_TOP)))
RTLSRC_VOPT_TB_TOP	:= $(addsuffix _vopt, $(RTLSRC_VLOG_TB_TOP))

# RTL source files for the CV32E core
# DESIGN_RTL_DIR is used by CV32E40P_MANIFEST file
CV_CORE_PKG          := $(CORE_V_VERIF)/core-v-cores/$(CV_CORE_LC)
CV_CORE_MANIFEST     := $(CV_CORE_PKG)/$(CV_CORE_LC)_manifest.flist
export DESIGN_RTL_DIR = $(CV_CORE_PKG)/rtl

RTLSRC_HOME   := $(CV_CORE_PKG)/rtl
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
include $(CORE_V_VERIF)/mk/Common.mk
###############################################################################
# Clone core RTL and DV dependencies
clone_cv_core_rtl:
	$(CLONE_CV_CORE_CMD)

clone_riscv-dv:
	$(CLONE_RISCVDV_CMD)

$(CV_CORE_PKG):
	echo "Cloning"
	$(CLONE_CV_CORE_CMD)

$(COMPLIANCE_PKG):
	$(CLONE_COMPLIANCE_CMD)

###############################################################################
# RISC-V Compliance Test-suite
#     As much as possible, the test suite is used "out-of-the-box".  The
#     "build_compliance" target below uses the Makefile supplied by the suite
#     to compile all the individual test-programs in the suite to generate the
#     elf and hex files used in simulation.  Each <sim>.mk is assumed to have a
#     target to run the compiled test-program.

# RISCV_ISA='rv32i|rv32im|rv32imc|rv32Zicsr|rv32Zifencei'
RISCV_ISA    ?= rv32i
RISCV_TARGET ?= OpenHW
RISCV_DEVICE ?= $(CV_CORE_LC)

clone_compliance:
	$(CLONE_COMPLIANCE_CMD)

clr_compliance:
	make clean -C $(CORE_V_VERIF)/$(CV_CORE_LC)/vendor_lib/riscv/riscv-compliance

build_compliance: $(COMPLIANCE_PKG)
	make simulate -i -C $(CORE_V_VERIF)/$(CV_CORE_LC)/vendor_lib/riscv/riscv-compliance \
		RISCV_TARGET=${RISCV_TARGET} \
		RISCV_DEVICE=${RISCV_DEVICE} \
		PATH=$(RISCV)/bin:$(PATH) \
		RISCV_PREFIX=$(RISCV_PREFIX) \
		NOTRAPS=1 \
		RISCV_ISA=$(RISCV_ISA)
#		VERBOSE=1

all_compliance: $(COMPLIANCE_PKG)
	make build_compliance RISCV_ISA=rv32i        && \
	make build_compliance RISCV_ISA=rv32im       && \
	make build_compliance RISCV_ISA=rv32imc      && \
	make build_compliance RISCV_ISA=rv32Zicsr    && \
	make build_compliance RISCV_ISA=rv32Zifencei

# "compliance" is a simulator-specific target defined in <sim>.mk

compliance_check_sig: compliance
	@echo "Checking Compliance Signature for $(RISCV_ISA)/$(COMPLIANCE_PROG)"
	@echo "Reference: $(REF)"
	@echo "Signature: $(SIG)"
	@export SUITEDIR=$(CORE_V_VERIF)/$(CV_CORE_LC)/vendor_lib/riscv/riscv-compliance/riscv-test-suite/$(RISCV_ISA) && \
	export REF=$(REF) && export SIG=$(SIG) && export COMPL_PROG=$(COMPLIANCE_PROG) && \
	export RISCV_TARGET=${RISCV_TARGET} && export RISCV_DEVICE=${RISCV_DEVICE} && \
	export RISCV_ISA=${RISCV_ISA} export SIG_ROOT=${SIG_ROOT} && \
	$(CORE_V_VERIF)/bin/diff_signatures.sh | tee $(SIMULATOR)_results/$(COMPLIANCE_PROG)/diff_signatures.log

compliance_check_all_sigs:
	@$(MKDIR_P) $(SIMULATOR)_results/$(RISCV_ISA)
	@echo "Checking Compliance Signature for all tests in $(RISCV_ISA)"
	@export SUITEDIR=$(CORE_V_VERIF)/$(CV_CORE_LC)/vendor_lib/riscv/riscv-compliance/riscv-test-suite/$(RISCV_ISA) && \
	export RISCV_TARGET=${RISCV_TARGET} && export RISCV_DEVICE=${RISCV_DEVICE} && \
	export RISCV_ISA=${RISCV_ISA} export SIG_ROOT=${SIG_ROOT} && \
	$(CORE_V_VERIF)/bin/diff_signatures.sh $(RISCV_ISA) | tee $(SIMULATOR)_results/$(RISCV_ISA)/diff_signatures.log

#	export REF=$(REF) && export SIG=$(SIG) && export COMPL_PROG=$(COMPLIANCE_PROG) && \

compliance_regression:
	make build_compliance RISCV_ISA=$(RISCV_ISA)
	@export SIM_DIR=$(CORE_V_VERIF)/$(CV_CORE_LC)/sim/uvmt && \
	$(CORE_V_VERIF)/bin/run_compliance.sh $(RISCV_ISA)
	make compliance_check_all_sigs RISCV_ISA=$(RISCV_ISA)

dah:
	@export SIM_DIR=$(CORE_V_VERIF)/cv32/sim/uvmt && \
	$(CORE_V_VERIF)/bin/run_compliance.sh $(RISCV_ISA)

###############################################################################
# Clean up your mess!
#   1. Clean all generated files of the C and assembler tests
#   2. Simulator-specific clean targets are in ./<simulator>.mk
#   3. clean-bsp target is specified in ../Common.mk
clean_test_programs: clean-bsp
	find $(CORE_V_VERIF)/$(CV_CORE_LC)/tests/uvmt/test-programs -name *.o       -exec rm {} \;
	find $(CORE_V_VERIF)/$(CV_CORE_LC)/tests/uvmt/test-programs -name *.hex     -exec rm {} \;
	find $(CORE_V_VERIF)/$(CV_CORE_LC)/tests/uvmt/test-programs -name *.elf     -exec rm {} \;
	find $(CORE_V_VERIF)/$(CV_CORE_LC)/tests/uvmt/test-programs -name *.map     -exec rm {} \;
	find $(CORE_V_VERIF)/$(CV_CORE_LC)/tests/uvmt/test-programs -name *.readelf -exec rm {} \;
	find $(CORE_V_VERIF)/$(CV_CORE_LC)/tests/uvmt/test-programs -name *.objdump -exec rm {} \;
	find $(CORE_V_VERIF)/$(CV_CORE_LC)/tests/programs -name *.o       -exec rm {} \;
	find $(CORE_V_VERIF)/$(CV_CORE_LC)/tests/programs -name *.hex     -exec rm {} \;
	find $(CORE_V_VERIF)/$(CV_CORE_LC)/tests/programs -name *.elf     -exec rm {} \;
	find $(CORE_V_VERIF)/$(CV_CORE_LC)/tests/programs -name *.map     -exec rm {} \;
	find $(CORE_V_VERIF)/$(CV_CORE_LC)/tests/programs -name *.itb     -exec rm {} \;
	find $(CORE_V_VERIF)/$(CV_CORE_LC)/tests/programs -name *.readelf -exec rm {} \;
	find $(CORE_V_VERIF)/$(CV_CORE_LC)/tests/programs -name *.objdump -exec rm {} \;
	find $(CORE_V_VERIF)/$(CV_CORE_LC)/tests/programs -name corev_*.S -exec rm {} \;

clean_compliance:
	rm -rf $(COMPLIANCE_PKG)
