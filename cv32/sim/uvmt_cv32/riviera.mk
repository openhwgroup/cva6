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
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# 
###############################################################################
#
# Riviera-PRO-specific Makefile for the CV32E40P "uvmt_cv32" testbench.
# Riviera-PRO is the Aldec SystemVerilog simulator.
#
###############################################################################

# Executables
VLIB   					= vlib
VMAP 					= vmap
VLOG 					= $(CV_SIM_PREFIX) vlog
VSIM 					= $(CV_SIM_PREFIX) vsim
VWORK     				= work

# Paths
VSIM_RESULTS           ?= $(MAKE_PATH)/riviera_results
VSIM_COREVDV_RESULTS   ?= $(VSIM_RESULTS)/corev-dv
VSIM_COV_MERGE_DIR     ?= $(VSIM_RESULTS)/merged
UVM_HOME               ?= ${ALDEC_PATH}/vlib/uvm-1.2/src/
USES_DPI = 1

# Default flags
VLOG_COV                ?= -coverage sbecam
VSIM_USER_FLAGS         ?=
VSIM_COV 		?= -acdb -acdb_cov sbfectapm -acdb_file $(VSIM_TEST).acdb
VSIM_WAVES_ADV_DEBUG    ?= 
VSIM_WAVES_DO           ?= 

# Common QUIET flag defaults to -quiet unless VERBOSE is set
ifeq ($(call IS_YES,$(VERBOSE)),YES)
QUIET=
else
QUIET=-quiet
endif

ifeq ($(USES_DPI),1)
  DPILIB_VLOG_OPT = 
  DPILIB_VSIM_OPT = -sv_lib "$(ALDEC_PATH)/bin/uvm_1_2_dpi.so"
else
  DPILIB_VLOG_OPT = +define+UVM_NO_DPI 
  DPILIB_VSIM_OPT = 
endif

LIBDIR  = $(UVM_HOME)/lib
LIBNAME = uvm_dpi

###############################################################################
# VLOG (Compilation)
VLOG_FLAGS    ?= \
				-timescale "1ns/1ps" \
				-err VCP2694 W1 #for riscv dv

VLOG_FILE_LIST = -f $(DV_UVMT_CV32_PATH)/uvmt_cv32.flist

VLOG_DEBUG_FLAGS ?= -dbg
VLOG_FLAGS += $(DPILIB_VLOG_OPT)

# Add the ISS to compilation
ifeq ($(call IS_YES,$(USE_ISS)),YES)
VLOG_FILE_LIST += -f $(DV_UVMT_CV32_PATH)/imperas_iss.flist
VLOG_FLAGS += "+define+ISS+CV32E40P_TRACE_EXECUTION"
VLOG_FLAGS += -dpilib
endif

###############################################################################
# VSIM (Simulaion)
VSIM_FLAGS        += $(VSIM_USER_FLAGS) +access +r+w
VSIM_DEBUG_FLAGS  ?= -dbg
VSIM_GUI_FLAGS    ?= -gui
VSIM_SCRIPT_DIR	   = $(abspath $(MAKE_PATH)/../tools/riviera)

VSIM_UVM_ARGS      =

ifeq ($(call IS_YES,$(USE_ISS)),YES)
VSIM_FLAGS += +USE_ISS
VSIM_FLAGS += -sv_lib $(DV_OVPM_MODEL)/bin/Linux64/riscv_CV32E40P.dpi
endif

# Skip compile if requested (COMP=NO)
ifneq ($(call IS_NO,$(COMP)),NO)
VSIM_SIM_PREREQ = comp
endif

################################################################################
# Coverage database generation
#TODO
ifeq ($(call IS_YES,$(COV)),YES)
VLOG_FLAGS  += $(VLOG_COV)
VSIM_FLAGS  += $(VSIM_COV)
endif

################################################################################
# Waveform generation
#TODO

################################################################################
# Interactive simulation
ifeq ($(call IS_YES,$(GUI)),YES)
VRUN_FLAGS += run -all
ifeq ($(call IS_YES,$(ADV_DEBUG)),YES)
VLOG_FLAGS += $(VLOG_DEBUG_FLAGS)
VSIM_FLAGS += $(VSIM_GUI_FLAGS) $(VSIM_DEBUG_FLAGS)
else
VSIM_FLAGS += $(VSIM_GUI_FLAGS)
endif
else
VSIM_FLAGS += -c
VRUN_FLAGS += run -all; endsim; quit -force
endif

################################################################################
# Coverage command
#TODO

################################################################################
# Waveform (post-process) command line
#TODO

################################################################################
# Targets

.PHONY: no_rule help mk_vsim_dir lib comp run

no_rule:
	@echo 'makefile: SIMULATOR is set to $(SIMULATOR), but no rule/target specified.'
	@echo 'try "make SIMULATOR=vsim sanity" (or just "make sanity" if shell ENV variable SIMULATOR is already set).'

help:
	vsim -help

################################################################################
# core-dv generation targets

comp_core-dv:
	$(MKDIR_P) $(VSIM_COREVDV_RESULTS)
	$(MKDIR_P) $(COREVDV_PKG)/out_$(DATE)/run
	cd $(VSIM_COREVDV_RESULTS) && \
		$(VLIB) $(VWORK)
	cd $(VSIM_COREVDV_RESULTS) && \
		$(VLOG) \
			$(VLOG_FLAGS) \
			-uvmver 1.2 \
			+incdir+$(COREVDV_PKG)/target/cv32e40p \
			+incdir+$(RISCVDV_PKG)/user_extension \
			+incdir+$(RISCVDV_PKG)/tests \
			+incdir+$(COREVDV_PKG) \
			-f $(COREVDV_PKG)/manifest.f \

gen_corev-dv: 
	mkdir -p $(VSIM_COREVDV_RESULTS)/$(TEST)
	# Clean old assembler generated tests in results
	idx=$(GEN_START_INDEX); sum=$$(($(GEN_START_INDEX) + $(GEN_NUM_TESTS))); \
	while [ $$idx -lt $${sum} ]; do \
		rm -f ${VSIM_COREVDV_RESULTS}/${TEST}/${TEST}_$$idx.S; \
		echo "idx = $$idx"; \
		idx=$$((idx + 1)); \
	done
	cd  $(VSIM_COREVDV_RESULTS)/$(TEST) && \
		$(VSIM) \
			$(VSIM_FLAGS) \
			corev_instr_gen_tb_top \
			$(DPILIB_VSIM_OPT) \
			-lib $(VSIM_COREVDV_RESULTS)/work \
			+UVM_TESTNAME=$(GEN_UVM_TEST) \
			+num_of_tests=$(GEN_NUM_TESTS)  \
			-l $(TEST)_$(GEN_START_INDEX)_$(GEN_NUM_TESTS).log \
			+start_idx=$(GEN_START_INDEX) \
			+num_of_tests=$(GEN_NUM_TESTS) \
			+asm_file_name_opts=$(TEST) \
			$(GEN_PLUSARGS) \
			-do '$(VRUN_FLAGS)'
	# Copy out final assembler files to test directory
	idx=$(GEN_START_INDEX); sum=$$(($(GEN_START_INDEX) + $(GEN_NUM_TESTS))); \
	while [ $$idx -lt $${sum} ]; do \
		cp ${VSIM_COREVDV_RESULTS}/${TEST}/${TEST}_$$idx.S ${GEN_TEST_DIR}; \
		idx=$$((idx + 1)); \
	done

corev-dv: clean_riscv-dv \
	clone_riscv-dv \
	comp_core-dv \

################################################################################
# Riviera-PRO simulation targets

mk_vsim_dir: 
	$(MKDIR_P) $(VSIM_RESULTS)

################################################################################
# If the configuration specified OVPSIM arguments, generate an ovpsim.ic file and
# set IMPERAS_TOOLS to point to it
gen_ovpsim_ic:
	@if [ ! -z "$(CFG_OVPSIM)" ]; then \
		mkdir -p $(VSIM_RESULTS)/$(TEST_NAME); \
		echo "$(CFG_OVPSIM)" > $(VSIM_RESULTS)/$(TEST_NAME)/ovpsim.ic; \
	fi
ifneq ($(CFG_OVPSIM),)
export IMPERAS_TOOLS=$(VSIM_RESULTS)/$(TEST_NAME)/ovpsim.ic
endif

# Target to create work directory in $(VSIM_RESULTS)/
lib: mk_vsim_dir $(CV32E40P_PKG) $(TBSRC_PKG) $(TBSRC)
	if [ ! -d "$(VSIM_RESULTS)/$(VWORK)" ]; then \
		$(VLIB) "$(VSIM_RESULTS)/$(VWORK)"; \
	fi

# Target to run vlog over SystemVerilog source in $(VSIM_RESULTS)/
comp: lib
	@echo "$(BANNER)"
	@echo "* Running vlog in $(VSIM_RESULTS)"
	@echo "* Log: $(VSIM_RESULTS)/vlog.log"
	@echo "$(BANNER)"
	cd $(VSIM_RESULTS) && \
		$(VLOG) \
			$(VLOG_FLAGS) \
			+incdir+$(DV_UVME_CV32_PATH) \
			+incdir+$(DV_UVMT_CV32_PATH) \
			+incdir+$(UVM_HOME) \
			$(UVM_HOME)/uvm_pkg.sv \
			-f $(CV32E40P_MANIFEST) \
			$(VLOG_FILE_LIST) \
			$(TBSRC_PKG)

# Target to run VSIM (i.e. run the simulation)
run: $(VSIM_SIM_PREREQ) gen_ovpsim_ic
	@echo "$(BANNER)"
	@echo "* Running vsim in $(VSIM_RESULTS)/$(VSIM_TEST)"
	@echo "* Log: $(VSIM_RESULTS)/$(VSIM_TEST)/vsim-$(VSIM_TEST).log"
	@echo "$(BANNER)"
	mkdir -p $(VSIM_RESULTS)/$(VSIM_TEST) && \
	cd $(VSIM_RESULTS)/$(VSIM_TEST) && \
		$(VSIM) \
			$(VSIM_FLAGS) \
			${DPILIB_VSIM_OPT} \
			-l vsim-$(VSIM_TEST).log \
			-lib $(VSIM_RESULTS)/work \
			+UVM_TESTNAME=$(TEST_UVM_TEST)\
			$(RTLSRC_VLOG_TB_TOP) \
			$(TEST_PLUSARGS) \
			-do '$(VRUN_FLAGS)'

################################################################################
# Test targets

.PHONY: hello-world

# This special target is to support the special sanity target in the Common Makefile
hello-world:
	$(MAKE) test TEST=hello-world

custom: VSIM_TEST=$(CUSTOM_PROG)
custom: VSIM_FLAGS += +firmware=$(CUSTOM_DIR)/$(CUSTOM_PROG).hex +elf_file=$(CUSTOM_DIR)/$(CUSTOM_PROG).elf
custom: TEST_UVM_TEST=uvmt_cv32_firmware_test_c
custom: $(CUSTOM_DIR)/$(CUSTOM_PROG).hex run

################################################################################
# The new general test target
test: VSIM_TEST=$(TEST_NAME)
test: VSIM_FLAGS += +firmware=$(TEST_TEST_DIR)/$(TEST_NAME).hex +elf_file=$(TEST_TEST_DIR)/$(TEST_NAME).elf
test: $(TEST_TEST_DIR)/$(TEST_NAME).hex run

################################################################################
# Invoke post-process waveform viewer
#TODO

################################################################################
# Invoke coverage
#TODO

###############################################################################
# Clean up your mess!

clean:
	rm -rf $(VSIM_RESULTS) library.cfg $(VWORK)

# All generated files plus the clone of the RTL
clean_all: clean clean_core_tests
	rm -rf $(CV32E40P_PKG)
