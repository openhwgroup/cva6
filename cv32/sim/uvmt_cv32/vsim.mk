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
# VSIM-specific Makefile for the CV32E40P "uvmt_cv32" testbench.
# VSIM is the Mentor Graphics Questa SystemVerilog simulator.
#
###############################################################################

# Executables
VLIB   					= vlib
VMAP 					= vmap
VLOG 					= $(CV_SIM_PREFIX) vlog
VOPT 					= $(CV_SIM_PREFIX) vopt
VSIM 					= $(CV_SIM_PREFIX) vsim
VISUALIZER				= $(CV_TOOL_PREFIX) visualizer
VCOVER                  = vcover

# Paths
VWORK     				= work
VSIM_RESULTS           ?= $(MAKE_PATH)/vsim_results
VSIM_COREVDV_RESULTS   ?= $(VSIM_RESULTS)/corev-dv
VSIM_COV_MERGE_DIR     ?= $(VSIM_RESULTS)/merged
UVM_HOME               ?= $(abspath $(shell which $(VLIB))/../../verilog_src/uvm-1.2/src)
USES_DPI = 1

# Default flags
VSIM_USER_FLAGS         ?=
VOPT_COV  				?= +cover=setf+$(RTLSRC_VLOG_TB_TOP).
VSIM_COV 				?= -coverage
VOPT_WAVES_ADV_DEBUG    ?= -designfile design.bin
VSIM_WAVES_ADV_DEBUG    ?= -qwavedb=+signal+assertion+ignoretxntime+msgmode=both
VSIM_WAVES_DO           ?= $(VSIM_SCRIPT_DIR)/waves.tcl

# Common QUIET flag defaults to -quiet unless VERBOSE is set
ifeq ($(call IS_YES,$(VERBOSE)),YES)
QUIET=
else
QUIET=-quiet
endif

ifeq ($(USES_DPI),1)
  DPILIB_VLOG_OPT = 
  DPILIB_VSIM_OPT = -sv_lib $(UVM_HOME)/../../../uvm-1.2/linux_x86_64/uvm_dpi
  DPILIB_TARGET = dpi_lib$(BITS)
else
  DPILIB_VLOG_OPT = +define+UVM_NO_DPI 
  DPILIB_VSIM_OPT = 
  DPILIB_TARGET =
endif

LIBDIR  = $(UVM_HOME)/lib
LIBNAME = uvm_dpi

###############################################################################
# VLOG (Compilation)
VLOG_FLAGS    ?= \
				-suppress 2577 \
				-suppress 2583 \
				-suppress 13314 \
				-suppress 13288 \
        		-suppress 2181 \
				-suppress 13262 \
				-timescale "1ns/1ps" \
				-sv \
        		-mfcu \
        		+acc=rb \
				$(QUIET) \
        		-writetoplevels  uvmt_cv32_tb
VLOG_FILE_LIST = -f $(DV_UVMT_CV32_PATH)/uvmt_cv32.flist

VLOG_FLAGS += $(DPILIB_VLOG_OPT)

# Add the ISS to compilation
ifeq ($(call IS_YES,$(USE_ISS)),YES)
VLOG_FILE_LIST += -f $(DV_UVMT_CV32_PATH)/imperas_iss.flist
VLOG_FLAGS += "+define+ISS+CV32E40P_TRACE_EXECUTION"
endif

###############################################################################
# VOPT (Optimization)
VOPT_FLAGS    ?= -debugdb \
				 -fsmdebug \
				 -suppress 7034 \
				 +acc \
				 $(QUIET)

###############################################################################
# VSIM (Simulaion)
VSIM_FLAGS        += $(VSIM_USER_FLAGS)
VSIM_FLAGS        += $(USER_RUN_FLAGS)
VSIM_FLAGS        += -sv_seed $(RNDSEED)
VSIM_FLAGS        += -suppress 7031
VSIM_DEBUG_FLAGS  ?= -debugdb
VSIM_GUI_FLAGS    ?= -gui -debugdb
VSIM_SCRIPT_DIR	   = $(abspath $(MAKE_PATH)/../tools/vsim)

VSIM_UVM_ARGS      = +incdir+$(UVM_HOME)/src $(UVM_HOME)/src/uvm_pkg.sv

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
ifeq ($(call IS_YES,$(COV)),YES)
VOPT_FLAGS  += $(VOPT_COV)
VSIM_FLAGS  += $(VSIM_COV)
VSIM_FLAGS  += -do 'set TEST ${VSIM_TEST}; source $(VSIM_SCRIPT_DIR)/cov.tcl'
endif

################################################################################
# Waveform generation
ifeq ($(call IS_YES,$(WAVES)),YES)
ifeq ($(call IS_YES,$(ADV_DEBUG)),YES)
VSIM_FLAGS += $(VSIM_WAVES_ADV_DEBUG)
else
VSIM_FLAGS += -do $(VSIM_WAVES_DO)
endif
endif

ifeq ($(call IS_YES,$(ADV_DEBUG)),YES)
VOPT_FLAGS += $(VOPT_WAVES_ADV_DEBUG)
endif

################################################################################
# Interactive simulation
ifeq ($(call IS_YES,$(GUI)),YES)
ifeq ($(call IS_YES,$(ADV_DEBUG)),YES)
VSIM_FLAGS += -visualizer=+designfile=../design.bin
else
VSIM_FLAGS += -gui
endif
VSIM_FLAGS += -do $(VSIM_SCRIPT_DIR)/gui.tcl
else
VSIM_FLAGS += -batch
VSIM_FLAGS += -do $(VSIM_SCRIPT_DIR)/vsim.tcl
endif

################################################################################
# Coverage command
COV_FLAGS = 
COV_REPORT = cov_report
COV_MERGE_TARGET =
COV_MERGE_FIND = find $(VSIM_RESULTS) -type f -name "*.ucdb" | grep -v merged.ucdb > $(VSIM_COV_MERGE_DIR)/ucdb.list
COV_MERGE_FLAGS=merge -64 -out merged.ucdb -inputs ucdb.list

ifeq ($(call IS_YES,$(MERGE)),YES)
COV_DIR=$(VSIM_RESULTS)/$(COV_MERGE_DIR)
COV_MERGE_TARGET=cov_merge
else
COV_DIR=$(VSIM_RESULTS)/$(TEST)
endif

ifeq ($(call IS_YES,$(MERGE)),YES)
ifeq ($(call IS_YES,$(GUI)),YES)
# Merged coverage GUI
COV_FLAGS=-viewcov merged.ucdb
else
# Merged coverage report
COV_FLAGS=-c -viewcov merged.ucdb -do "file delete -force $(COV_REPORT); coverage report -html -details -precision 2 -annotate -output $(COV_REPORT); exit -f"
endif
else
ifeq ($(call IS_YES,$(GUI)),YES)
# Test coverage GUI
COV_FLAGS=-viewcov $(TEST).ucdb
else
# Test coverage report
COV_FLAGS=-c -viewcov $(TEST).ucdb -do "file delete -force $(COV_REPORT); coverage report -html -details -precision 2 -annotate -output $(COV_REPORT); exit -f"
endif
endif

################################################################################
# Waveform (post-process) command line
ifeq ($(call IS_YES,$(ADV_DEBUG)),YES)
WAVES_CMD = \
	cd $(VSIM_RESULTS)/$(TEST) && \
		$(VISUALIZER) \
			-designfile ../design.bin \
			-wavefile qwave.db
else
WAVES_CMD = \
	cd $(VSIM_RESULTS)/$(TEST) && \
		$(VSIM) \
			-gui \
			-view vsim.wlf
endif

# Compute vsim (run) prereqs, by default do a full compile + run when running 
# a test, set COMP=NO to skip vlib-vlog-vopt and just run vsim
ifneq ($(call IS_NO,$(COMP)),NO)
VSIM_RUN_PREREQ = opt
endif

################################################################################
# Targets

.PHONY: no_rule help mk_vsim_dir lib comp opt run

no_rule:
	@echo 'makefile: SIMULATOR is set to $(SIMULATOR), but no rule/target specified.'
	@echo 'try "make SIMULATOR=vsim sanity" (or just "make sanity" if shell ENV variable SIMULATOR is already set).'

help:
	vsim -help

################################################################################
# corev-dv generation targets

vlog_corev-dv:
	$(MKDIR_P) $(VSIM_COREVDV_RESULTS)
	$(MKDIR_P) $(COREVDV_PKG)/out_$(DATE)/run
	cd $(VSIM_COREVDV_RESULTS) && \
		$(VLIB) $(VWORK)
	cd $(VSIM_COREVDV_RESULTS) && \
		$(VLOG) \
			$(VLOG_FLAGS) \
			+incdir+$(UVM_HOME) \
			$(UVM_HOME)/uvm_pkg.sv \
			+incdir+$(COREVDV_PKG)/target/cv32e40p \
			+incdir+$(RISCVDV_PKG)/user_extension \
			+incdir+$(RISCVDV_PKG)/tests \
			+incdir+$(COREVDV_PKG) \
			-f $(COREVDV_PKG)/manifest.f \
			-l vlog.log

vopt_corev-dv:
	cd $(VSIM_COREVDV_RESULTS) && \
		$(VOPT) \
			-work $(VWORK) \
			$(VOPT_FLAGS) \
			corev_instr_gen_tb_top \
			-o corev_instr_gen_tb_top_vopt \
			-l vopt.log

gen_corev-dv: 
	mkdir -p $(VSIM_COREVDV_RESULTS)/$(TEST)
	# Clean old assembler generated tests in results
	for (( idx=${GEN_START_INDEX}; idx < $$((${GEN_START_INDEX} + ${GEN_NUM_TESTS})); idx++ )); do \
		rm -f ${VSIM_COREVDV_RESULTS}/${TEST}/${TEST}_$$idx.S; \
	done
	cd $(VSIM_COREVDV_RESULTS)/$(TEST) && \
		$(VMAP) work ../work
	cd  $(VSIM_COREVDV_RESULTS)/$(TEST) && \
		$(VSIM) \
			$(VSIM_FLAGS) \
			corev_instr_gen_tb_top_vopt \
			$(DPILIB_VSIM_OPT) \
			+UVM_TESTNAME=$(GEN_UVM_TEST) \
			+num_of_tests=$(GEN_NUM_TESTS)  \
			-l $(TEST)_$(GEN_START_INDEX)_$(GEN_NUM_TESTS).log \
			+start_idx=$(GEN_START_INDEX) \
			+num_of_tests=$(GEN_NUM_TESTS) \
			+UVM_TESTNAME=$(GEN_UVM_TEST) \
			+asm_file_name_opts=$(TEST) \
			$(GEN_PLUSARGS)
	# Copy out final assembler files to test directory
	for (( idx=${GEN_START_INDEX}; idx < $$((${GEN_START_INDEX} + ${GEN_NUM_TESTS})); idx++ )); do \
		cp ${VSIM_COREVDV_RESULTS}/${TEST}/${TEST}_$$idx.S ${GEN_TEST_DIR}; \
	done

comp_corev-dv: $(RISCVDV_PKG) vlog_corev-dv vopt_corev-dv

corev-dv: clean_riscv-dv \
          clone_riscv-dv \
          comp_corev-dv

################################################################################
# Questa simulation targets

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
		$(VLIB) $(VSIM_RESULTS)/$(VWORK); \
	fi

# Target to run vlog over SystemVerilog source in $(VSIM_RESULTS)/
vlog: lib
	@echo "$(BANNER)"
	@echo "* Running vlog in $(VSIM_RESULTS)"
	@echo "* Log: $(VSIM_RESULTS)/vlog.log"
	@echo "$(BANNER)"
	cd $(VSIM_RESULTS) && \
		$(VLOG) \
			-work $(VWORK) \
			-l vlog.log \
			$(VLOG_FLAGS) \
			$(CFG_COMPILE_FLAGS) \
			+incdir+$(DV_UVME_CV32_PATH) \
			+incdir+$(DV_UVMT_CV32_PATH) \
			+incdir+$(UVM_HOME) \
			$(UVM_HOME)/uvm_pkg.sv \
			-f $(CV32E40P_MANIFEST) \
			$(VLOG_FILE_LIST) \
			$(TBSRC_PKG)

# Target to run vopt over compiled code in $(VSIM_RESULTS)/
opt: vlog
	@echo "$(BANNER)"
	@echo "* Running vopt in $(VSIM_RESULTS)"
	@echo "* Log: $(VSIM_RESULTS)/vopt.log"
	@echo "$(BANNER)"
	cd $(VSIM_RESULTS) && \
		$(VOPT) \
			-work $(VWORK) \
			-l vopt.log \
			$(VOPT_FLAGS) \
			$(RTLSRC_VLOG_TB_TOP) \
			-o $(RTLSRC_VOPT_TB_TOP)

comp: opt

# Target to run VSIM (i.e. run the simulation)
run: $(VSIM_RUN_PREREQ) gen_ovpsim_ic
	@echo "$(BANNER)"
	@echo "* Running vsim in $(VSIM_RESULTS)/$(VSIM_TEST)"
	@echo "* Log: $(VSIM_RESULTS)/$(VSIM_TEST)/vsim-$(VSIM_TEST).log"
	@echo "$(BANNER)"
	mkdir -p $(VSIM_RESULTS)/$(VSIM_TEST) && \
	cd $(VSIM_RESULTS)/$(VSIM_TEST) && \
		$(VMAP) work ../work
	cd $(VSIM_RESULTS)/$(VSIM_TEST) && \
		$(VSIM) \
			-work $(VWORK) \
			$(VSIM_FLAGS) \
			-l vsim-$(VSIM_TEST).log \
			$(DPILIB_VSIM_OPT) \
			+UVM_TESTNAME=$(TEST_UVM_TEST) \
			$(RTLSRC_VOPT_TB_TOP) \
			$(TEST_PLUSARGS)

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
waves:
	@if [ -z "$(TEST)" ]; then \
		echo "Error: TEST variable must be defined"; \
		exit 2; \
	fi
	$(WAVES_CMD)

################################################################################
# Invoke coverage
cov_merge:
	$(MKDIR_P) $(VSIM_RESULTS)/$(COV_MERGE_DIR)
	cd $(COV_DIR) && \
		$(COV_MERGE_FIND)
	cd $(VSIM_RESULTS)/$(COV_MERGE_DIR) && \
		$(VCOVER) \
			$(COV_MERGE_FLAGS)
cov: $(COV_MERGE_TARGET)
	cd $(COV_DIR) && \
		$(VSIM) \
			$(COV_FLAGS)

###############################################################################
# Clean up your mess!

clean:
	rm -rf $(VSIM_RESULTS)

# All generated files plus the clone of the RTL
clean_all: clean clean_core_tests clean-bsp
	rm -rf $(CV32E40P_PKG)
