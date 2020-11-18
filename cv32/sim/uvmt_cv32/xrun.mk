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
# XRUN-specific Makefile for the CV32E40P "uvmt_cv32" testbench.
# XRUN is the Cadence Xcelium SystemVerilog simulator (https://cadence.com/)
#
###############################################################################

#
# Cadence do not (officially) support Ubuntu, so suppress the nonzero return code from XRUN
#
OS_IS_UBUNTU = $(findstring Ubuntu,$(shell lsb_release -d))
ifeq ($(OS_IS_UBUNTU),Ubuntu)
    .IGNORE: hello-world comp test custom compliance comp_corev-dv corev-dv gen_corev-dv
endif

# Executables
XRUN              = $(CV_SIM_PREFIX) xrun
SIMVISION         = $(CV_TOOL_PREFIX) simvision
INDAGO            = $(CV_TOOL_PREFIX) indago
IMC               = $(CV_SIM_PREFIX) imc

# Paths
XRUN_RESULTS         ?= $(PWD)/xrun_results
XRUN_COREVDV_RESULTS ?= $(XRUN_RESULTS)/corev-dv
XRUN_DIR             ?= $(XRUN_RESULTS)/xcelium.d
XRUN_UVMHOME_ARG     ?= CDNS-1.2-ML

# Flags
XRUN_COMP_FLAGS  ?= -64bit -disable_sem2009 -access +rwc \
                    -nowarn UEXPSC \
                    -sv -uvm -uvmhome $(XRUN_UVMHOME_ARG) \
                    $(TIMESCALE) $(SV_CMP_FLAGS)
XRUN_RUN_BASE_FLAGS   ?= -64bit $(XRUN_GUI) -licqueue +UVM_VERBOSITY=$(XRUN_UVM_VERBOSITY) \
                         $(XRUN_PLUSARGS) -svseed $(RNDSEED) -sv_lib $(OVP_MODEL_DPI)
XRUN_GUI         ?=
XRUN_SINGLE_STEP ?=
XRUN_ELAB_COV     = -covdut uvmt_cv32_tb -coverage b:e:f:u
XRUN_ELAB_COVFILE = -covfile ../../tools/xrun/covfile.tcl
XRUN_RUN_COV      = -covscope uvmt_cv32_tb \
					-nowarn CGDEFN

XRUN_UVM_VERBOSITY ?= UVM_MEDIUM

###############################################################################
# Common QUIET flag defaults to -quiet unless VERBOSE is set
ifeq ($(call IS_YES,$(VERBOSE)),YES)
QUIET=
else
QUIET=-quiet
endif

################################################################################
# GUI interactive simulation
# GUI=YES enables interactive mode
# ADV_DEBUG=YES will enable Indago, default is to use SimVision
ifeq ($(call IS_YES,$(GUI)),YES)
XRUN_GUI += -gui
XRUN_USER_COMPILE_ARGS += -linedebug
ifeq ($(call IS_YES,$(ADV_DEBUG)),YES)
XRUN_GUI += -indago
endif
endif

################################################################################
# Waveform generation
# WAVES=YES enables waveform generation for entire testbench
# ADV_DEBUG=YES will enable Indago waves, default is to generate SimVision waves
ifeq ($(call IS_YES,$(WAVES)),YES)
ifeq ($(call IS_YES,$(ADV_DEBUG)),YES)
XRUN_RUN_WAVES_FLAGS = -input ../../../tools/xrun/indago.tcl
else
XRUN_RUN_WAVES_FLAGS = -input ../../../tools/xrun/probe.tcl
endif
endif

################################################################################
# Waveform (post-process) command line
ifeq ($(call IS_YES,$(ADV_DEBUG)),YES)
WAVES_CMD = cd $(XRUN_RESULTS)/$(TEST_NAME) && $(INDAGO) -db ida.db
else
WAVES_CMD = cd $(XRUN_RESULTS)/$(TEST_NAME) && $(SIMVISION) waves.shm
endif

XRUN_USER_COMPILE_ARGS += $(USER_COMPILE_FLAGS)

################################################################################
# Coverage options
# COV=YES generates coverage database, must be specified for comp and run
IMC_MERGE_ARGS = merge -initial_model union_all -overwrite -message 1
IMC_REPORT_ARGS = report_metrics -summary -overwrite -out cov_report
MERGED_COV_DIR ?= merged_cov

ifeq ($(call IS_YES,$(COV)),YES)
XRUN_ELAB_COV_FLAGS += $(XRUN_ELAB_COV)
XRUN_ELAB_COV_FLAGS += $(XRUN_ELAB_COVFILE)
XRUN_RUN_COV_FLAGS += $(XRUN_RUN_COV)
endif

# Find command to gather ucd files 
COV_MERGE_FIND = find "$$(pwd -P)" -type f -name "*.ucd" | grep -v `d_cov | xargs dirname > $(XRUN_RESULTS)/merged_cov/ucd.list

ifeq ($(call IS_YES,$(MERGE)),YES)
COV_MERGE = cov_merge
TEST = $(MERGED_COV_DIR)
else
COV_MERGE =
endif

ifeq ($(call IS_YES,$(MERGE)),YES)
COV_ARGS = -load cov_work/scope/merged
else
COV_ARGS = -load cov_work/uvmt_cv32_tb/$(TEST_NAME)
endif

ifeq ($(call IS_YES,$(GUI)),YES)
COV_ARGS += -gui
else
COV_ARGS += -execcmd "$(IMC_REPORT_ARGS)"
endif

################################################################################

# File to `include "uvm_macros.svh" since Xcelium automatic UVM compilation
# does not source the macros file. 
XRUN_UVM_MACROS_INC_FILE = $(DV_UVMT_CV32_PATH)/uvmt_cv32_uvm_macros_inc.sv

XRUN_FILE_LIST ?= -f $(DV_UVMT_CV32_PATH)/uvmt_cv32.flist
ifeq ($(call IS_YES,$(USE_ISS)),YES)
    XRUN_FILE_LIST += -f $(DV_UVMT_CV32_PATH)/imperas_iss.flist
    XRUN_USER_COMPILE_ARGS += +define+ISS+CV32E40P_TRACE_EXECUTION
    XRUN_PLUSARGS +="+USE_ISS"
#     XRUN_PLUSARGS += +USE_ISS +ovpcfg="--controlfile $(OVP_CTRL_FILE)"
else
	XRUN_USER_COMPILE_ARGS += +define+CV32E40P_TRACE_EXECUTION
endif

# Simulate using latest elab
XRUN_RUN_FLAGS        ?= -R -xmlibdirname ../xcelium.d 
XRUN_RUN_FLAGS        += -covoverwrite
XRUN_RUN_FLAGS        += $(XRUN_RUN_BASE_FLAGS)
XRUN_RUN_FLAGS        += $(XRUN_RUN_COV_FLAGS)
XRUN_RUN_FLAGS        += $(XRUN_USER_RUN_FLAGS)
XRUN_RUN_FLAGS        += $(USER_RUN_FLAGS)

###############################################################################
# Xcelium warning suppression

# Xcelium constraint solver
XRUN_RUN_FLAGS  += -nowarn XCLGNOPTM
XRUN_RUN_FLAGS  += -nowarn RNDNOXCEL

# Probes
XRUN_RUN_FLAGS  += -nowarn PRLDYN

# Allow extra semicolons
XRUN_COMP_FLAGS += -nowarn UEXPSC

# SOP expression evaluates to a constant - remove from coverage calculation
XRUN_COMP_FLAGS += -nowarn COVSEC

# Warning that no timescale defined for package, this is by design as no
# core-v-verif code should contain its own timescale
XRUN_COMP_FLAGS += -nowarn TSNSPK

# Warning on expression coverage speedup (only counts always blocks in expression if output changes)
XRUN_COMP_FLAGS += -nowarn COVVPO
XRUN_RUN_COV    += -nowarn COVVPO

# Warning about new style struct expression scoring
XRUN_COMP_FLAGS += -nowarn COVEOS

# +incdir in -f file not used
XRUN_COMP_FLAGS += -nowarn SPDUSD

# scoring events not included in expression coverage
XRUN_COMP_FLAGS += -nowarn COVNSO

# instance reporting warings for covergroups
XRUN_COMP_FLAGS += -nowarn COVCGN
XRUN_COMP_FLAGS += -nowarn CGPIZE

# per_instance option is 0
XRUN_COMP_FLAGS += -nowarn CGPIDF

# deselect_coverage -all warnings
XRUN_COMP_FLAGS += -nowarn CGNSWA

# instance reporting warings for covergroups
XRUN_RUN_COV    += -nowarn COVCGN
XRUN_RUN_COV    += -nowarn CGPIZE

# Un-named covergroup instances
XRUN_RUN_COV    += -nowarn CGDEFN

###############################################################################
# Targets

no_rule:
	@echo 'makefile: SIMULATOR is set to $(SIMULATOR), but no rule/target specified.'
	@echo 'try "make SIMULATOR=xrun sanity" (or just "make sanity" if shell ENV variable SIMULATOR is already set).'

help:
	xrun -help

.PHONY: comp test waves cov

mk_xrun_dir: 
	$(MKDIR_P) $(XRUN_DIR)

# This special target is to support the special sanity target in the Common Makefile
hello-world:
	$(MAKE) test TEST=hello-world

XRUN_COMP = $(XRUN_COMP_FLAGS) \
		$(QUIET) \
		$(CFG_COMPILE_FLAGS) \
		$(XRUN_USER_COMPILE_ARGS) \
		+incdir+$(DV_UVME_CV32_PATH) \
		+incdir+$(DV_UVMT_CV32_PATH) \
		$(XRUN_UVM_MACROS_INC_FILE) \
		-f $(CV32E40P_MANIFEST) \
		$(XRUN_FILE_LIST) \
		$(UVM_PLUSARGS)

comp: mk_xrun_dir $(CV32E40P_PKG) $(OVP_MODEL_DPI)
	@echo "$(BANNER)"
	@echo "* Compiling xrun in $(XRUN_RESULTS)"
	@echo "* Log: $(XRUN_RESULTS)/xrun.log"
	@echo "$(BANNER)"
	cd $(XRUN_RESULTS) && $(XRUN) \
		$(XRUN_COMP) \
		$(XRUN_ELAB_COV_FLAGS) \
		-top $(RTLSRC_VLOG_TB_TOP) \
		-l xrun.log \
		-elaborate

ifneq ($(call IS_NO,$(COMP)),NO)
XRUN_SIM_PREREQ = comp
endif

XRUN_COMP_RUN = $(XRUN_RUN_FLAGS)

ifeq ($(call IS_YES,$(XRUN_SINGLE_STEP)), YES)
	XRUN_SIM_PREREQ = mk_xrun_dir $(CV32E40P_PKG) $(OVP_MODEL_DPI)
	XRUN_COMP_RUN = $(XRUN_COMP) $(XRUN_RUN_BASE_FLAGS)
endif

################################################################################
# If the configuration specified OVPSIM arguments, generate an ovpsim.ic file and
# set IMPERAS_TOOLS to point to it
gen_ovpsim_ic:
	@if [ ! -z "$(CFG_OVPSIM)" ]; then \
		mkdir -p $(XRUN_RESULTS)/$(TEST_NAME); \
		echo "$(CFG_OVPSIM)" > $(XRUN_RESULTS)/$(TEST_NAME)/ovpsim.ic; \
	fi
ifneq ($(CFG_OVPSIM),)
export IMPERAS_TOOLS=$(XRUN_RESULTS)/$(TEST_NAME)/ovpsim.ic
endif

################################################################################
# The new general test target
test: $(XRUN_SIM_PREREQ) $(TEST_TEST_DIR)/$(TEST_PROGRAM).hex gen_ovpsim_ic
	echo $(IMPERAS_TOOLS)
	mkdir -p $(XRUN_RESULTS)/$(TEST_NAME) && \
	cd $(XRUN_RESULTS)/$(TEST_NAME) && \
		$(XRUN) \
			-l xrun-$(TEST_NAME).log \
			$(XRUN_COMP_RUN) \
			$(XRUN_RUN_WAVES_FLAGS) \
			-covtest $(TEST_NAME) \
			$(TEST_PLUSARGS) \
			+UVM_TESTNAME=$(TEST_UVM_TEST) \
			+elf_file=$(TEST_TEST_DIR)/$(TEST_PROGRAM).elf \
			+nm_file=$(TEST_TEST_DIR)/$(TEST_PROGRAM).nm \
			+firmware=$(TEST_TEST_DIR)/$(TEST_PROGRAM).hex

################################################################################
# Custom test-programs.  See comment in dsim.mk for more info
custom: $(XRUN_SIM_PREREQ) $(CUSTOM_DIR)/$(CUSTOM_PROG).hex
	mkdir -p $(XRUN_RESULTS)/$(CUSTOM_PROG) && cd $(XRUN_RESULTS)/$(CUSTOM_PROG) && \
	$(XRUN) -l xrun-$(CUSTOM_PROG).log -covtest $(CUSTOM_PROG) $(XRUN_COMP_RUN) \
		+elf_file=$(CUSTOM_DIR)/$(CUSTOM_PROG).elf \
		+nm_file=$(CUSTOM_DIR)/$(CUSTOM_PROG).nm \
		+UVM_TESTNAME=uvmt_cv32_firmware_test_c \
		+firmware=$(CUSTOM_DIR)/$(CUSTOM_PROG).hex

###############################################################################
# Run a test-program from the RISC-V Compliance Test-suite. The parent Makefile
COMPLIANCE_PROG ?= I-ADD-01

compliance: comp build_compliance
	mkdir -p $(XRUN_RESULTS)/$(COMPLIANCE_PROG) && cd $(XRUN_RESULTS)/$(COMPLIANCE_PROG)  && \
	export IMPERAS_TOOLS=$(PROJ_ROOT_DIR)/cv32/tests/cfg/ovpsim_no_pulp.ic && \
	$(XRUN) -l xrun-$(@).log -covtest riscv-compliance $(XRUN_COMP_RUN) \
		+UVM_TESTNAME=uvmt_cv32_firmware_test_c \
		+firmware=$(COMPLIANCE_PKG)/work/$(RISCV_ISA)/$(COMPLIANCE_PROG).hex \
		+elf_file=$(COMPLIANCE_PKG)/work/$(RISCV_ISA)/$(COMPLIANCE_PROG).elf

###############################################################################
# Use Google instruction stream generator (RISCV-DV) to create new test-programs
comp_corev-dv: $(RISCVDV_PKG)
	mkdir -p $(XRUN_COREVDV_RESULTS)
	cd $(XRUN_COREVDV_RESULTS) && \
	$(XRUN) $(XRUN_COMP_FLAGS) \
		$(QUIET) \
		$(XRUN_USER_COMPILE_ARGS) \
		-elaborate \
		+incdir+$(COREVDV_PKG)/target/cv32e40p \
		+incdir+$(RISCVDV_PKG)/user_extension \
		+incdir+$(RISCVDV_PKG)/tests \
		+incdir+$(COREVDV_PKG) \
		-f $(COREVDV_PKG)/manifest.f \
		-l xrun.log


corev-dv: clean_riscv-dv \
          clone_riscv-dv \
	  comp_corev-dv

gen_corev-dv: 
	mkdir -p $(XRUN_COREVDV_RESULTS)/$(TEST)
	# Clean old assembler generated tests in results
	for (( idx=${GEN_START_INDEX}; idx < $$((${GEN_START_INDEX} + ${GEN_NUM_TESTS})); idx++ )); do \
		rm -f ${XRUN_COREVDV_RESULTS}/${TEST}/${TEST}_$$idx.S; \
	done
	cd  $(XRUN_COREVDV_RESULTS)/$(TEST) && \
	$(XRUN) -R $(XRUN_RUN_FLAGS) \
		-xceligen rand_struct \
		-l $(TEST)_$(GEN_START_INDEX)_$(GEN_NUM_TESTS).log \
		+start_idx=$(GEN_START_INDEX) \
		+num_of_tests=$(GEN_NUM_TESTS) \
		+UVM_TESTNAME=$(GEN_UVM_TEST) \
		+asm_file_name_opts=$(TEST) \
		$(GEN_PLUSARGS)
	# Copy out final assembler files to test directory
	for (( idx=${GEN_START_INDEX}; idx < $$((${GEN_START_INDEX} + ${GEN_NUM_TESTS})); idx++ )); do \
		ls -l ${XRUN_COREVDV_RESULTS}/${TEST} > /dev/null; \
		cp ${XRUN_COREVDV_RESULTS}/${TEST}/${TEST}_$$idx.S ${GEN_TEST_DIR}; \
	done

################################################################################
# Invoke post-process waveform viewer
waves:
	$(WAVES_CMD)

################################################################################
# Invoke post-process coverage viewer
cov_merge:
	$(MKDIR_P) $(XRUN_RESULTS)/$(MERGED_COV_DIR)
	rm -rf $(XRUN_RESULTS)/$(MERGED_COV_DIR)/*
	$(COV_MERGE_FIND) > $(XRUN_RESULTS)/$(MERGED_COV_DIR)/ucd.list
	cd $(XRUN_RESULTS)/$(MERGED_COV_DIR) && \
	$(IMC) -execcmd "$(IMC_MERGE_ARGS) -list ucd.list -out merged; exit"

cov: $(COV_MERGE)
	cd $(XRUN_RESULTS)/$(TEST_NAME) && $(IMC) $(COV_ARGS)

###############################################################################
# Clean up your mess!

clean:	
	rm -rf $(XRUN_RESULTS)	

# Files created by Eclipse when using the Imperas ISS + debugger
clean_eclipse:
	rm  -f eguieclipse.log
	rm  -f idebug.log
	rm  -f stdout.txt
	rm  -rf workspace

# All generated files plus the clone of the RTL
clean_all: clean clean_eclipse clean_riscv-dv clean_test_programs clean-bsp clean_compliance
	rm -rf $(CV32E40P_PKG)
