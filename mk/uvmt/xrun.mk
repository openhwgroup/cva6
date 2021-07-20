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
# XRUN-specific Makefile for any uvmt testbench.
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
XRUN_RESULTS         ?= $(if $(CV_RESULTS),$(CV_RESULTS)/xrun_results,$(MAKE_PATH)/xrun_results)
XRUN_COREVDV_RESULTS ?= $(XRUN_RESULTS)/corev-dv
XRUN_DIR             ?= $(XRUN_RESULTS)/$(CFG)/xcelium.d
XRUN_UVMHOME_ARG     ?= CDNS-1.2-ML

# Flags
XRUN_COMP_FLAGS  ?= -64bit -disable_sem2009 -access +rwc \
                    -nowarn UEXPSC \
                    -sv -uvm -uvmhome $(XRUN_UVMHOME_ARG) \
                    $(TIMESCALE) $(SV_CMP_FLAGS)
XRUN_RUN_BASE_FLAGS ?= -64bit $(XRUN_GUI) -licqueue +UVM_VERBOSITY=$(XRUN_UVM_VERBOSITY) \
                       $(XRUN_PLUSARGS) -svseed $(RNDSEED) -sv_lib $(OVP_MODEL_DPI)
XRUN_GUI         ?=
XRUN_SINGLE_STEP ?=
XRUN_ELAB_COV     = -covdut uvmt_$(CV_CORE_LC)_tb -coverage b:e:f:u
XRUN_ELAB_COVFILE = -covfile $(abspath $(MAKE_PATH)/../tools/xrun/covfile.tcl)
XRUN_RUN_COV      = -covscope uvmt_$(CV_CORE_LC)_tb \
					-nowarn CGDEFN
XRUN_RUN_BASE_FLAGS += -sv_lib $(DPI_DASM_LIB)

XRUN_UVM_VERBOSITY ?= UVM_MEDIUM
DPI_INCLUDE        ?= $(shell dirname $(shell which xrun))/../include

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
# WAVES_MEM=YES enables tracing memories and large vectors
# ADV_DEBUG=YES will enable Indago waves, default is to generate SimVision waves
ifeq ($(call IS_YES,$(WAVES_MEM)),YES)
  ifeq ($(call IS_YES,$(ADV_DEBUG)),YES)
    XRUN_RUN_WAVES_FLAGS = -input $(abspath $(MAKE_PATH)/../tools/xrun/indago_mem.tcl)
  else
    XRUN_RUN_WAVES_FLAGS = -input $(abspath $(MAKE_PATH)/../tools/xrun/probe_mem.tcl)
  endif
else
  ifeq ($(call IS_YES,$(WAVES)),YES)
    ifeq ($(call IS_YES,$(ADV_DEBUG)),YES)
      XRUN_RUN_WAVES_FLAGS = -input $(abspath $(MAKE_PATH)/../tools/xrun/indago.tcl)
    else
      XRUN_RUN_WAVES_FLAGS = -input $(abspath $(MAKE_PATH)/../tools/xrun/probe.tcl)
    endif
  endif
endif

################################################################################
# Waveform (post-process) command line
ifeq ($(call IS_YES,$(ADV_DEBUG)),YES)

WAVES_CMD = cd $(XRUN_RESULTS)/$(CFG)/$(TEST_NAME)_$(RUN_INDEX) && $(INDAGO) -db ida.db
else
WAVES_CMD = cd $(XRUN_RESULTS)/$(CFG)/$(TEST_NAME)_$(RUN_INDEX) && $(SIMVISION) waves.shm

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
COV_MERGE_FIND = find "$(XRUN_RESULTS)" -type f -name "*.ucd" | grep -v d_cov | xargs dirname

ifeq ($(call IS_YES,$(MERGE)),YES)
COV_MERGE = cov_merge
TEST = $(MERGED_COV_DIR)
else
COV_MERGE =
endif

ifeq ($(call IS_YES,$(MERGE)),YES)
COV_ARGS = -load $(XRUN_RESULTS)/$(CFG)/$(MERGED_COV_DIR)/cov_work/scope/merged
else
COV_ARGS = -load cov_work/uvmt_$(CV_CORE_LC)_tb/$(TEST_NAME)
endif

ifeq ($(call IS_YES,$(GUI)),YES)
COV_ARGS += -gui
else
COV_ARGS += -execcmd "$(IMC_REPORT_ARGS)"
endif

################################################################################

# File to `include "uvm_macros.svh" since Xcelium automatic UVM compilation
# does not source the macros file. 
XRUN_UVM_MACROS_INC_FILE = $(DV_UVMT_PATH)/uvmt_$(CV_CORE_LC)_uvm_macros_inc.sv

XRUN_FILE_LIST ?= -f $(DV_UVMT_PATH)/uvmt_$(CV_CORE_LC).flist
XRUN_FILE_LIST += -f $(DV_UVMT_PATH)/imperas_iss.flist
XRUN_USER_COMPILE_ARGS += +define+$(CV_CORE_UC)_TRACE_EXECUTION
XRUN_USER_COMPILE_ARGS += +define+UVM
ifeq ($(call IS_YES,$(USE_ISS)),YES)
	XRUN_PLUSARGS += +USE_ISS
else
    XRUN_PLUSARGS += +DISABLE_OVPSIM
endif
ifeq ($(call IS_YES,$(USE_RVVI)),YES)
    XRUN_PLUSARGS +="+USE_RVVI"
endif
ifeq ($(call IS_YES,$(TEST_DISABLE_ALL_CSR_CHECKS)),YES)
    XRUN_PLUSARGS +="+DISABLE_ALL_CSR_CHECKS"
endif
ifneq ($(TEST_DISABLE_CSR_CHECK),)
	XRUN_PLUSARGS += +DISABLE_CSR_CHECK=$(TEST_DISABLE_CSR_CHECK)
endif

# Simulate using latest elab
XRUN_RUN_FLAGS        ?= 
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

# Warning on adding _T suffix to named block scoped assertion coverage
XRUN_RUN_FLAGS  += -nowarn COVNBT

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

# deselect_coverage -all warnings
XRUN_COMP_COREV_DV_FLAGS += -nowarn BNDWRN

# instance reporting warings for covergroups
XRUN_RUN_COV    += -nowarn COVCGN
XRUN_RUN_COV    += -nowarn CGPIZE

# Empty overgroup warnings (we purposely empty covergroups as part of filtering w/ configuration variables)
XRUN_RUN_COV    += -nowarn WCRTUP
XRUN_RUN_COV    += -nowarn WCOVPT
XRUN_RUN_COV    += -nowarn WCROSS

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
		+incdir+$(DV_UVME_PATH) \
		+incdir+$(DV_UVMT_PATH) \
		$(XRUN_UVM_MACROS_INC_FILE) \
		-f $(CV_CORE_MANIFEST) \
		$(XRUN_FILE_LIST) \
		$(UVM_PLUSARGS)

comp: mk_xrun_dir $(CV_CORE_PKG)
	@echo "$(BANNER)"
	@echo "* Compiling xrun in $(XRUN_RESULTS)/$(CFG)"
	@echo "* Log: $(XRUN_RESULTS)/$(CFG)/xrun.log"
	@echo "$(BANNER)"
	cd $(XRUN_RESULTS)/$(CFG) && $(XRUN) \
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
	XRUN_SIM_PREREQ = mk_xrun_dir $(CV_CORE_PKG)
	XRUN_COMP_RUN = $(XRUN_COMP) $(XRUN_RUN_BASE_FLAGS)
endif

################################################################################
# If the configuration specified OVPSIM arguments, generate an ovpsim.ic file and
# set IMPERAS_TOOLS to point to it
gen_ovpsim_ic:
	@if [ ! -z "$(CFG_OVPSIM)" ]; then \
		mkdir -p $(XRUN_RESULTS)/$(CFG)/$(TEST_NAME)_$(RUN_INDEX); \
		echo "$(CFG_OVPSIM)" > $(XRUN_RESULTS)/$(CFG)/$(TEST_NAME)_$(RUN_INDEX)/ovpsim.ic; \
	fi
ifneq ($(CFG_OVPSIM),)
export IMPERAS_TOOLS=ovpsim.ic
endif

################################################################################
# The new general test target

# corev-dv tests needs an added run_index_suffix, blank for other tests
ifeq ($(shell echo $(TEST) | head -c 6),corev_)
	OPT_RUN_INDEX_SUFFIX=_$(RUN_INDEX)
endif

test: $(XRUN_SIM_PREREQ) $(TEST_TEST_DIR)/$(TEST_PROGRAM)$(OPT_RUN_INDEX_SUFFIX).hex gen_ovpsim_ic
	mkdir -p $(XRUN_RESULTS)/$(CFG)/$(TEST_NAME)_$(RUN_INDEX) && \
	cd $(XRUN_RESULTS)/$(CFG)/$(TEST_NAME)_$(RUN_INDEX) && \
		$(XRUN) \
			-R -xmlibdirname ../xcelium.d \
			-l xrun-$(TEST_NAME).log \
			$(XRUN_COMP_RUN) \
			$(XRUN_RUN_WAVES_FLAGS) \
			-covtest $(TEST_NAME) \
			$(TEST_PLUSARGS) \
			+UVM_TESTNAME=$(TEST_UVM_TEST) \
			+elf_file=$(TEST_TEST_DIR)/$(TEST_PROGRAM)$(OPT_RUN_INDEX_SUFFIX).elf \
			+nm_file=$(TEST_TEST_DIR)/$(TEST_PROGRAM)$(OPT_RUN_INDEX_SUFFIX).nm \
			+firmware=$(TEST_TEST_DIR)/$(TEST_PROGRAM)$(OPT_RUN_INDEX_SUFFIX).hex
	$(POST_TEST)

################################################################################
# Custom test-programs.  See comment in dsim.mk for more info
custom: $(XRUN_SIM_PREREQ) $(CUSTOM_DIR)/$(CUSTOM_PROG).hex
	mkdir -p $(XRUN_RESULTS)/$(CFG)/$(CUSTOM_PROG)_$(RUN_INDEX) && cd $(XRUN_RESULTS)/$(CFG)/$(CUSTOM_PROG)_$(RUN_INDEX) && \
	$(XRUN) -R ../xcelium.d -l xrun-$(CUSTOM_PROG).log -covtest $(CUSTOM_PROG) $(XRUN_COMP_RUN) \
		+elf_file=$(CUSTOM_DIR)/$(CUSTOM_PROG).elf \
		+nm_file=$(CUSTOM_DIR)/$(CUSTOM_PROG).nm \
		+UVM_TESTNAME=uvmt_$(CV_CORE_LC)_firmware_test_c \
		+firmware=$(CUSTOM_DIR)/$(CUSTOM_PROG).hex

###############################################################################
# Run a single test-program from the RISC-V Compliance Test-suite. The parent
# Makefile of this <sim>.mk implements "all_compliance", the target that
# compiles the test-programs.
#
# There is a dependancy between RISCV_ISA and COMPLIANCE_PROG which *you* are
# required to know.  For example, the I-ADD-01 test-program is part of the rv32i
# testsuite.
# So this works:
#                make compliance RISCV_ISA=rv32i COMPLIANCE_PROG=I-ADD-01
# But this does not:
#                make compliance RISCV_ISA=rv32imc COMPLIANCE_PROG=I-ADD-01
# 
RISCV_ISA       ?= rv32i
COMPLIANCE_PROG ?= I-ADD-01

SIG_ROOT      ?= $(XRUN_RESULTS)/$(CFG)/$(RISCV_ISA)
SIG           ?= $(XRUN_RESULTS)/$(CFG)/$(RISCV_ISA)/$(COMPLIANCE_PROG)_$(RUN_INDEX)/$(COMPLIANCE_PROG).signature_output
REF           ?= $(COMPLIANCE_PKG)/riscv-test-suite/$(RISCV_ISA)/references/$(COMPLIANCE_PROG).reference_output
TEST_PLUSARGS ?= +signature=$(COMPLIANCE_PROG).signature_output

ifneq ($(call IS_NO,$(COMP)),NO)
XRUN_COMPLIANCE_PREREQ = comp build_compliance
endif

compliance: $(XRUN_COMPLIANCE_PREREQ)
	mkdir -p $(XRUN_RESULTS)/$(CFG)/$(RISCV_ISA)/$(COMPLIANCE_PROG)_$(RUN_INDEX) && \
    cd $(XRUN_RESULTS)/$(CFG)/$(RISCV_ISA)/$(COMPLIANCE_PROG)_$(RUN_INDEX)  && \
	export IMPERAS_TOOLS=$(CORE_V_VERIF)/$(CV_CORE_LC)/tests/cfg/ovpsim_no_pulp.ic && \
	$(XRUN) -R -xmlibdirname ../../xcelium.d -l xrun-$(COMPLIANCE_PROG).log -covtest riscv-compliance $(XRUN_COMP_RUN) $(TEST_PLUSARGS) \
		+UVM_TESTNAME=uvmt_$(CV_CORE_LC)_firmware_test_c \
		+firmware=$(COMPLIANCE_PKG)/work/$(RISCV_ISA)/$(COMPLIANCE_PROG).hex \
		+elf_file=$(COMPLIANCE_PKG)/work/$(RISCV_ISA)/$(COMPLIANCE_PROG).elf



###############################################################################
# Use Google instruction stream generator (RISCV-DV) to create new test-programs
comp_corev-dv: $(RISCVDV_PKG)
	mkdir -p $(XRUN_COREVDV_RESULTS)
	cd $(XRUN_COREVDV_RESULTS) && \
	$(XRUN) $(XRUN_COMP_FLAGS) \
		-xmlibdirname ./xcelium.d \
		$(QUIET) \
		$(XRUN_USER_COMPILE_ARGS) \
		$(XRUN_COMP_COREV_DV_FLAGS) \
		-elaborate \
		+incdir+$(CV_CORE_COREVDV_PKG)/target/$(CV_CORE_LC) \
		+incdir+$(RISCVDV_PKG)/user_extension \
		+incdir+$(COREVDV_PKG) \
		+incdir+$(CV_CORE_COREVDV_PKG) \
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
	$(XRUN) -R -xmlibdirname ../xcelium.d \
		$(XRUN_RUN_FLAGS) \
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
	$(MKDIR_P) $(XRUN_RESULTS)/$(CFG)/$(MERGED_COV_DIR)
	rm -rf $(XRUN_RESULTS)/$(CFG)/$(MERGED_COV_DIR)/*
	$(COV_MERGE_FIND) > $(XRUN_RESULTS)/$(CFG)/$(MERGED_COV_DIR)/ucd.list
	cd $(XRUN_RESULTS)/$(CFG)/$(MERGED_COV_DIR) && \
	$(IMC) -execcmd "$(IMC_MERGE_ARGS) -runfile ucd.list -out merged; exit"

ifeq ($(call IS_YES,$(MERGE)),YES)
  COVERAGE_TARGET_DIR=$(XRUN_RESULTS)/$(CFG)/$(MERGED_COV_DIR)
else
  COVERAGE_TARGET_DIR=$(XRUN_RESULTS)/$(CFG)/$(TEST_NAME)_$(RUN_INDEX)
endif

cov: $(COV_MERGE)
	cd $(COVERAGE_TARGET_DIR) && $(IMC) $(COV_ARGS)

###############################################################################
# Clean up your mess!

clean:	
	@echo "$(MAKEFILE_LIST)"
	rm -rf $(XRUN_RESULTS)	

# Files created by Eclipse when using the Imperas ISS + debugger
clean_eclipse:
	rm  -f eguieclipse.log
	rm  -f idebug.log
	rm  -f stdout.txt
	rm  -rf workspace

# All generated files plus the clone of the RTL
clean_all: clean clean_eclipse clean_riscv-dv clean_test_programs clean-bsp clean_compliance clean_embench clean_dpi_dasm_spike
	rm -rf $(CV_CORE_PKG)
