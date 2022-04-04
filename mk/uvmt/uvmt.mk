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
# Makefile for the UVMT testbench for multiple OpenHW-verified cores.  Substantially modified
# from the original Makefile for the RI5CY testbench.
#
###############################################################################
#
# Copyright 2019 Claire Wolf
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

# Variable checks
ifndef CV_CORE
$(error Must set CV_CORE to a valid core)
endif

# "Constants"
DATE           = $(shell date +%F)
CV_CORE_LC     = $(shell echo $(CV_CORE) | tr A-Z a-z)
CV_CORE_UC     = $(shell echo $(CV_CORE) | tr a-z A-Z)
SIMULATOR_UC   = $(shell echo $(SIMULATOR) | tr a-z A-Z)
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
export RUN_INDEX       ?= 0

# Common output directories
SIM_RESULTS             ?= $(if $(CV_RESULTS),$(abspath $(CV_RESULTS))/$(SIMULATOR)_results,$(MAKE_PATH)/$(SIMULATOR)_results)
SIM_CFG_RESULTS          = $(SIM_RESULTS)/$(CFG)
SIM_COREVDV_RESULTS      = $(SIM_CFG_RESULTS)/corev-dv
SIM_LDGEN_RESULTS        = $(SIM_CFG_RESULTS)/$(LDGEN)
SIM_TEST_RESULTS         = $(SIM_CFG_RESULTS)/$(TEST)
SIM_RUN_RESULTS          = $(SIM_TEST_RESULTS)/$(RUN_INDEX)
SIM_TEST_PROGRAM_RESULTS = $(SIM_RUN_RESULTS)/test_program
SIM_BSP_RESULTS          = $(SIM_TEST_PROGRAM_RESULTS)/bsp

# EMBench options
EMB_TYPE           ?= speed
EMB_TARGET         ?= 0
EMB_CPU_MHZ        ?= 1
EMB_TIMEOUT        ?= 3600
EMB_PARALLEL_ARG    = $(if $(filter $(YES_VALS),$(EMB_PARALLEL)),YES,NO)
EMB_BUILD_ONLY_ARG  = $(if $(filter $(YES_VALS),$(EMB_BUILD_ONLY)),YES,NO)
EMB_DEBUG_ARG       = $(if $(filter $(YES_VALS),$(EMB_DEBUG)),YES,NO)

# UVM Environment
export DV_UVMT_PATH             = $(CORE_V_VERIF)/$(CV_CORE_LC)/tb/uvmt
export DV_UVME_PATH             = $(CORE_V_VERIF)/$(CV_CORE_LC)/env/uvme
export DV_UVML_HRTBT_PATH       = $(CORE_V_VERIF)/lib/uvm_libs/uvml_hrtbt
export DV_UVMA_CORE_CNTRL_PATH  = $(CORE_V_VERIF)/lib/uvm_agents/uvma_core_cntrl
export DV_UVMA_ISACOV_PATH      = $(CORE_V_VERIF)/lib/uvm_agents/uvma_isacov
export DV_UVMA_RVFI_PATH        = $(CORE_V_VERIF)/lib/uvm_agents/uvma_rvfi
export DV_UVMA_RVVI_PATH        = $(CORE_V_VERIF)/lib/uvm_agents/uvma_rvvi
export DV_UVMA_RVVI_OVPSIM_PATH = $(CORE_V_VERIF)/lib/uvm_agents/uvma_rvvi_ovpsim
export DV_UVMA_CLKNRST_PATH     = $(CORE_V_VERIF)/lib/uvm_agents/uvma_clknrst
export DV_UVMA_INTERRUPT_PATH   = $(CORE_V_VERIF)/lib/uvm_agents/uvma_interrupt
export DV_UVMA_DEBUG_PATH       = $(CORE_V_VERIF)/lib/uvm_agents/uvma_debug
export DV_UVMA_PMA_PATH         = $(CORE_V_VERIF)/lib/uvm_agents/uvma_pma
export DV_UVMA_OBI_MEMORY_PATH  = $(CORE_V_VERIF)/lib/uvm_agents/uvma_obi_memory
export DV_UVMA_FENCEI_PATH      = $(CORE_V_VERIF)/lib/uvm_agents/uvma_fencei
export DV_UVML_TRN_PATH         = $(CORE_V_VERIF)/lib/uvm_libs/uvml_trn
export DV_UVML_LOGS_PATH        = $(CORE_V_VERIF)/lib/uvm_libs/uvml_logs
export DV_UVML_SB_PATH          = $(CORE_V_VERIF)/lib/uvm_libs/uvml_sb
export DV_UVML_MEM_PATH         = $(CORE_V_VERIF)/lib/uvm_libs/uvml_mem

export DV_OVPM_HOME             = $(CORE_V_VERIF)/vendor_lib/imperas
export DV_OVPM_MODEL            = $(DV_OVPM_HOME)/imperas_DV_COREV

export DV_OVPM_DESIGN           = $(DV_OVPM_HOME)/design

export DV_SVLIB_PATH            = $(CORE_V_VERIF)/$(CV_CORE_LC)/vendor_lib/verilab

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

# EMBench benchmarking suite
EMBENCH_PKG	:= $(CORE_V_VERIF)/$(CV_CORE_LC)/vendor_lib/embench
EMBENCH_TESTS	:= $(CORE_V_VERIF)/$(CV_CORE_LC)/tests/programs/embench

# Disassembler
DPI_DASM_PKG       := $(CORE_V_VERIF)/lib/dpi_dasm
DPI_DASM_SPIKE_PKG := $(CORE_V_VERIF)/$(CV_CORE_LC)/vendor_lib/dpi_dasm_spike
export DPI_DASM_ROOT       = $(DPI_DASM_PKG)
export DPI_DASM_SPIKE_ROOT = $(DPI_DASM_SPIKE_PKG)

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

# SVLIB
SVLIB_PKG            := $(CORE_V_VERIF)/$(CV_CORE_LC)/vendor_lib/verilab/svlib

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
clone_cv_core_rtl: $(CV_CORE_PKG)

clone_riscv-dv: $(RISCVDV_PKG)

clone_embench: $(EMBENCH_PKG)

clone_compliance: $(COMPLIANCE_PKG)

clone_dpi_dasm_spike:
	$(CLONE_DPI_DASM_SPIKE_CMD)

clone_svlib: $(SVLIB_PKG)

$(CV_CORE_PKG):
	$(CLONE_CV_CORE_CMD)

$(RISCVDV_PKG):
	$(CLONE_RISCVDV_CMD)

$(COMPLIANCE_PKG):
	$(CLONE_COMPLIANCE_CMD)

$(EMBENCH_PKG):
	$(CLONE_EMBENCH_CMD)

$(DPI_DASM_SPIKE_PKG):
	$(CLONE_DPI_DASM_SPIKE_CMD)

$(SVLIB_PKG):
	$(CLONE_SVLIB_CMD)

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
COMPLIANCE_RESULTS = $(SIM_RESULTS)

compliance_check_sig: compliance
	@echo "Checking Compliance Signature for $(RISCV_ISA)/$(COMPLIANCE_PROG)"
	@echo "Reference: $(REF)"
	@echo "Signature: $(SIG)"
	@export SUITEDIR=$(CORE_V_VERIF)/$(CV_CORE_LC)/vendor_lib/riscv/riscv-compliance/riscv-test-suite/$(RISCV_ISA) && \
	export REF=$(REF) && export SIG=$(SIG) && export COMPL_PROG=$(COMPLIANCE_PROG) && \
	export RISCV_TARGET=${RISCV_TARGET} && export RISCV_DEVICE=${RISCV_DEVICE} && \
	export RISCV_ISA=${RISCV_ISA} export SIG_ROOT=${SIG_ROOT} && \
	$(CORE_V_VERIF)/bin/diff_signatures.sh | tee $(COMPLIANCE_RESULTS)/$(CFG)/$(RISCV_ISA)/$(COMPLIANCE_PROG)/$(RUN_INDEX)/diff_signatures.log

compliance_check_all_sigs:
	@$(MKDIR_P) $(COMPLIANCE_RESULTS)/$(CFG)/$(RISCV_ISA)
	@echo "Checking Compliance Signature for all tests in $(CFG)/$(RISCV_ISA)"
	@export SUITEDIR=$(CORE_V_VERIF)/$(CV_CORE_LC)/vendor_lib/riscv/riscv-compliance/riscv-test-suite/$(RISCV_ISA) && \
	export RISCV_TARGET=${RISCV_TARGET} && export RISCV_DEVICE=${RISCV_DEVICE} && \
	export RISCV_ISA=${RISCV_ISA} export SIG_ROOT=${SIG_ROOT} && \
	$(CORE_V_VERIF)/bin/diff_signatures.sh $(RISCV_ISA) | tee $(COMPLIANCE_RESULTS)/$(CFG)/$(RISCV_ISA)/diff_signatures.log

compliance_regression:
	make build_compliance RISCV_ISA=$(RISCV_ISA)
	@export SIM_DIR=$(CORE_V_VERIF)/$(CV_CORE_LC)/sim/uvmt && \
	$(CORE_V_VERIF)/bin/run_compliance.sh $(RISCV_ISA)
	make compliance_check_all_sigs RISCV_ISA=$(RISCV_ISA)

dah:
	@export SIM_DIR=$(CORE_V_VERIF)/cv32/sim/uvmt && \
	$(CORE_V_VERIF)/bin/run_compliance.sh $(RISCV_ISA)

###############################################################################
# EMBench benchmark
# 	target to check out and run the EMBench suite for code size and speed
#

embench: $(EMBENCH_PKG)
	$(CORE_V_VERIF)/bin/run_embench.py \
		-c $(CV_CORE) \
		-cc $(RISCV_EXE_PREFIX)$(RISCV_CC) \
		-sim $(SIMULATOR) \
		-t $(EMB_TYPE) \
		--timeout $(EMB_TIMEOUT) \
		--parallel $(EMB_PARALLEL_ARG) \
		-b $(EMB_BUILD_ONLY_ARG) \
		-tgt $(EMB_TARGET) \
		-f $(EMB_CPU_MHZ) \
		-d $(EMB_DEBUG_ARG)

###############################################################################
# ISACOV (ISA coverage)
#   Compare the log against the tracer log.
#   This checks that sampling went correctly without false positives/negatives.

ISACOV_LOGDIR = $(SIM_CFG_RESULTS)/$(TEST)/$(RUN_INDEX)
ISACOV_RVFILOG = $(ISACOV_LOGDIR)/uvm_test_top.env.rvfi_agent.trn.log
ISACOV_COVERAGELOG = $(ISACOV_LOGDIR)/uvm_test_top.env.isacov_agent.trn.log

isacov_logdiff:
	@echo isacov_logdiff:
	@echo checking that env/dirs/files are as expected...
		@printenv TEST > /dev/null || (echo specify TEST; false)
		@ls $(ISACOV_LOGDIR) > /dev/null
		@ls $(ISACOV_RVFILOG) > /dev/null
		@ls $(ISACOV_COVERAGELOG) > /dev/null
	@echo extracting assembly code from logs...
		@cat $(ISACOV_RVFILOG)                                                      \
			| awk -F ' - ' '{print $$2}' `#discard everything but the assembly` \
			| sed 's/ *#.*//'            `#discard comments`                    \
			| sed 's/ *<.*//'            `#discard symbol information`          \
			| sed 's/,/, /g'             `#add space after commas`              \
			| tail -n +4 > trace.tmp     `#don't include banner`
		@cat $(ISACOV_COVERAGELOG)                       \
			| awk -F '\t' '{print $$3}' `#discard everything but the assembly` \
			| sed 's/_/./'              `#convert "c_addi" to "c.addi" etc`    \
			| tail -n +2 > agent.tmp    `#don't include banner`
	@echo diffing the instruction sequences...
		@echo saving to $(ISACOV_LOGDIR)/isacov_logdiff
		@rm -rf $(ISACOV_LOGDIR)/isacov_logdiff
		@diff trace.tmp agent.tmp > $(ISACOV_LOGDIR)/isacov_logdiff; true
		@rm -rf trace.tmp agent.tmp
		@(test ! -s $(ISACOV_LOGDIR)/isacov_logdiff && echo OK) || (echo FAIL; false)

###############################################################################
# Include the targets/rules for the selected SystemVerilog simulator
#ifeq ($(SIMULATOR), unsim)
#include unsim.mk
#else
ifeq ($(SIMULATOR), dsim)
include $(CORE_V_VERIF)/mk/uvmt/dsim.mk
else
ifeq ($(SIMULATOR), xrun)
include $(CORE_V_VERIF)/mk/uvmt/xrun.mk
else
ifeq ($(SIMULATOR), vsim)
include $(CORE_V_VERIF)/mk/uvmt/vsim.mk
else
ifeq ($(SIMULATOR), vcs)
include $(CORE_V_VERIF)/mk/uvmt/vcs.mk
else
ifeq ($(SIMULATOR), riviera)
include $(CORE_V_VERIF)/mk/uvmt/riviera.mk
else
include $(CORE_V_VERIF)/mk/uvmt/unsim.mk
endif
endif
endif
endif
endif
#endif

################################################################################
# Open a DVT Eclipse IDE instance with the project imported automatically
ifeq ($(MAKECMDGOALS), open_in_dvt_ide)
include $(CORE_V_VERIF)/mk/uvmt/dvt.mk
else
ifeq ($(MAKECMDGOALS), create_dvt_build_file)
include $(CORE_V_VERIF)/mk/uvmt/dvt.mk
else
ifeq ($(MAKECMDGOALS), dvt_dump_env_vars)
include $(CORE_V_VERIF)/mk/uvmt/dvt.mk
endif
endif
endif

###############################################################################
# Clean up your mess!
#   1. Clean all generated files of the C and assembler tests
#   2. Simulator-specific clean targets are in ./<simulator>.mk
#   3. clean_bsp target is specified in ../Common.mk
clean_hex:
	rm -rf $(SIM_TEST_PROGRAM_RESULTS)

clean_test_programs: clean_bsp
	if [ -d "$(SIM_RESULTS)" ]; then \
		find $(SIM_RESULTS) -depth -type d -name test_program | xargs rm -rf; \
	fi

clean_riscv-dv:
	rm -rf $(RISCVDV_PKG)
	rm -rf $(COREVDV_PKG)/out_*

clean_compliance:
	rm -rf $(COMPLIANCE_PKG)

clean_embench:
	rm -rf $(EMBENCH_PKG)
	cd $(EMBENCH_TESTS) && \
		find . ! -path . ! -path ./README.md -delete
	if [ -d "$(SIM_RESULTS)" ]; then \
		cd $(SIM_RESULTS) && find . -depth -type d -name "emb_*" | xargs rm -rf; \
	fi

clean_dpi_dasm_spike:
	rm -rf $(DPI_DASM_SPIKE_PKG)

clean_svlib:
	rm -rf $(SVLIB_PKG)
