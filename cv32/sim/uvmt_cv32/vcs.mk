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
# VCS-specific Makefile for the CV32E40P "uvmt_cv32" testbench.
#
###############################################################################

# Executables
VCS              = $(CV_SIM_PREFIX)vcs
SIMV             = $(CV_TOOL_PREFIX)simv
DVE              = $(CV_TOOL_PREFIX)dve
#VERDI            = $(CV_TOOL_PREFIX)verdi
URG               = $(CV_SIM_PREFIX)urg

# Paths
VCS_RESULTS     ?= $(PWD)/vcs_results
VCS_COREVDV_RESULTS ?= $(VCS_RESULTS)/corev-dv
VCS_DIR         ?= $(VCS_RESULTS)/vcs.d
VCS_ELAB_COV     = -cm line+cond+tgl+fsm+branch+assert  -cm_dir $(MAKECMDGOALS)/$(MAKECMDGOALS).vdb

# modifications to already defined variables to take into account VCS
VCS_OVP_MODEL_DPI = $(OVP_MODEL_DPI:.so=)                    # remove extension as VCS adds it
VCS_TIMESCALE = $(shell echo "$(TIMESCALE)" | tr ' ' '=')    # -timescale=1ns/1ps

VCS_UVM_VERBOSITY ?= UVM_MEDIUM

# Flags
#VCS_UVMHOME_ARG ?= /opt/uvm/1800.2-2017-0.9/
VCS_UVMHOME_ARG ?= /opt/synopsys/vcs-mx/O-2018.09-SP1-1/etc/uvm
VCS_UVM_ARGS          ?= +incdir+$(VCS_UVMHOME_ARG)/src $(VCS_UVMHOME_ARG)/src/uvm_pkg.sv +UVM_VERBOSITY=$(VCS_UVM_VERBOSITY) -ntb_opts uvm-1.2

VCS_COMP_FLAGS  ?= -lca -sverilog \
										$(SV_CMP_FLAGS) $(VCS_UVM_ARGS) $(VCS_TIMESCALE) \
										-assert svaext -race=all -ignore unique_checks -full64
VCS_GUI         ?=
VCS_RUN_COV      = -cm line+cond+tgl+fsm+branch+assert -cm_dir $(MAKECMDGOALS).vdb

###############################################################################
# Common QUIET flag defaults to -quiet unless VERBOSE is set
ifeq ($(call IS_YES,$(VERBOSE)),YES)
QUIET=
else
QUIET=-q
endif

################################################################################
# GUI interactive simulation
# GUI=YES enables interactive mode
# ADV_DEBUG=YES currently not supported
ifeq ($(call IS_YES,$(GUI)),YES)
VCS_GUI += -gui
VCS_USER_COMPILE_ARGS += -debug_access+r
ifeq ($(call IS_YES,$(ADV_DEBUG)),YES)
$(error ADV_DEBUG not yet supported by VCS )
endif
endif

################################################################################
# Waveform generation
# WAVES=YES enables waveform generation for entire testbench
# ADV_DEBUG=YES currently not supported
ifeq ($(call IS_YES,$(WAVES)),YES)
ifeq ($(call IS_YES,$(ADV_DEBUG)),YES)
$(error ADV_DEBUG not yet supported by VCS )
VCS_USER_COMPILE_ARGS = +vcs+vcdpluson
else
VCS_USER_COMPILE_ARGS = +vcs+vcdpluson
endif
endif

################################################################################
# Waveform (post-process) command line
ifeq ($(call IS_YES,$(ADV_DEBUG)),YES)
$(error ADV_DEBUG not yet supported by VCS )
WAVES_CMD = cd $(VCS_RESULTS)/$(TEST_NAME) && $(DVE) -vpd vcdplus.vpd 
else
WAVES_CMD = cd $(VCS_RESULTS)/$(TEST_NAME) && $(DVE) -vpd vcdplus.vpd 
endif

################################################################################
# Coverage options
# COV=YES generates coverage database, must be specified for comp and run
URG_MERGE_ARGS = -dbname merged.vdb -group lrm_bin_name -flex_merge union
MERGED_COV_DIR ?= merged_cov

ifeq ($(call IS_YES,$(COV)),YES)
VCS_USER_COMPILE_ARGS += $(VCS_ELAB_COV)
VCS_RUN_COV_FLAGS += $(VCS_RUN_COV)
endif

# list all vbd files
COV_RESULTS_LIST = $(wildcard $(VCS_RESULTS)/*/*.vdb)

ifeq ($(call IS_YES,$(MERGE)),YES)
COV_MERGE = cov_merge
TEST = $(MERGED_COV_DIR)
else
COV_MERGE =
endif

ifeq ($(call IS_YES,$(MERGE)),YES)
COV_ARGS = -dir cov_work/scope/merged
else
COV_ARGS = -dir $(TEST_NAME).vdb
endif

################################################################################

VCS_FILE_LIST ?= -f $(DV_UVMT_CV32_PATH)/uvmt_cv32.flist
ifeq ($(call IS_YES,$(USE_ISS)),YES)
    VCS_FILE_LIST += -f $(DV_UVMT_CV32_PATH)/imperas_iss.flist
    VCS_USER_COMPILE_ARGS += "+define+ISS +define+CV32E40P_TRACE_EXECUTION"
    VCS_PLUSARGS +="+USE_ISS"
endif

VCS_RUN_BASE_FLAGS   ?= $(VCS_GUI) \
                         $(VCS_PLUSARGS) +ntb_random_seed=$(RNDSEED) -sv_lib $(VCS_OVP_MODEL_DPI)
# Simulate using latest elab
VCS_RUN_FLAGS        ?= 
VCS_RUN_FLAGS        += $(VCS_RUN_BASE_FLAGS)
VCS_RUN_FLAGS        += $(VCS_RUN_WAVES_FLAGS)
VCS_RUN_FLAGS        += $(VCS_RUN_COV_FLAGS)
VCS_RUN_FLAGS        += $(USER_RUN_FLAGS)

no_rule:
	@echo 'makefile: SIMULATOR is set to $(SIMULATOR), but no rule/target specified.'
	@echo 'try "make SIMULATOR=vcs sanity" (or just "make sanity" if shell ENV variable SIMULATOR is already set).'

.PHONY: comp test waves cov

mk_vcs_dir:
	$(MKDIR_P) $(VCS_DIR)

# This special target is to support the special sanity target in the Common Makefile
hello-world:
	$(MAKE) test TEST=hello-world

cv32_riscv_tests: cv32-riscv-tests

cv32_riscv_compliance_tests: cv32-riscv-compliance-tests

VCS_COMP = $(VCS_COMP_FLAGS) \
		$(QUIET) \
		$(VCS_UVM_ARGS) \
		$(VCS_USER_COMPILE_ARGS) \
		+incdir+$(DV_UVME_CV32_PATH) \
		+incdir+$(DV_UVMT_CV32_PATH) \
		-f $(CV32E40P_MANIFEST) \
		$(VCS_FILE_LIST) \
		$(UVM_PLUSARGS)

comp: mk_vcs_dir $(CV32E40P_PKG) $(OVP_MODEL_DPI)
	cd $(VCS_RESULTS) && $(VCS) $(VCS_COMP) -top uvmt_cv32_tb
	@echo "$(BANNER)"
	@echo "* $(,maSIMULATOR) compile complete"
	@echo "* Log: $(VCS_RESULTS)/vcs.log"
	@echo "$(BANNER)"

ifneq ($(call IS_NO,$(COMP)),NO)
VCS_SIM_PREREQ = comp
endif

ifeq ($(call IS_YES,$(VCS_SINGLE_STEP)), YES)
	VCS_SIM_PREREQ = mk_vcs_dir $(CV32E40P_PKG) $(OVP_MODEL_DPI)
	VCS_COMP_RUN = $(VCS_COMP) $(VCS_RUN_BASE_FLAGS)
endif

################################################################################
# If the configuration specified OVPSIM arguments, generate an ovpsim.ic file and
# set IMPERAS_TOOLS to point to it
gen_ovpsim_ic:
	@if [ ! -z "$(CFG_OVPSIM)" ]; then \
		mkdir -p $(VCS_RESULTS)/$(TEST_NAME); \
		echo "$(CFG_OVPSIM)" > $(VCS_RESULTS)/$(TEST_NAME)/ovpsim.ic; \
	fi
ifneq ($(CFG_OVPSIM),)
export IMPERAS_TOOLS=$(VCS_RESULTS)/$(TEST_NAME)/ovpsim.ic
endif

################################################################################
# The new general test target
test: $(VCS_SIM_PREREQ) $(TEST_TEST_DIR)/$(TEST_PROGRAM).hex gen_ovpsim_ic
	echo $(IMPERAS_TOOLS)
	mkdir -p $(VCS_RESULTS)/$(TEST_NAME) && \
	cd $(VCS_RESULTS)/$(TEST_NAME) && \
		$(VCS_RESULTS)/$(SIMV) \
			-l vcs-$(TEST_NAME).log \
			-cm_name $(TEST_NAME) $(VCS_RUN_FLAGS) \
			$(TEST_PLUSARGS) \
			+UVM_TESTNAME=$(TEST_UVM_TEST) \
			+elf_file=$(TEST_TEST_DIR)/$(TEST_PROGRAM).elf \
			+firmware=$(TEST_TEST_DIR)/$(TEST_PROGRAM).hex

################################################################################
# Custom test-programs.  See comment in dsim.mk for more info
custom: $(VCS_SIM_PREREQ) $(CUSTOM_DIR)/$(CUSTOM_PROG).hex
	mkdir -p $(VCS_RESULTS)/$(CUSTOM_PROG) && cd $(VCS_RESULTS)/$(CUSTOM_PROG) && \
	$(VCS_RESULTS)/$(SIMV) -l vcs-$(CUSTOM_PROG).log -cm_test $(CUSTOM_PROG) $(VCS_RUN_FLAGS) \
		+UVM_TESTNAME=uvmt_cv32_firmware_test_c \
		+elf_file=$(CUSTOM_DIR)/$(CUSTOM_PROG).elf \
		+firmware=$(CUSTOM_DIR)/$(CUSTOM_PROG).hex

################################################################################
# Explicit target tests

# Runs tests in cv32_riscv_tests/ only
cv32-riscv-tests: $(VCS_SIM_PREREQ) $(CV32_RISCV_TESTS_FIRMWARE)/cv32_riscv_tests_firmware.hex
	mkdir -p $(VCS_RESULTS)/cv32-riscv-tests && cd $(VCS_RESULTS)/cv32-riscv-tests && \
	$(VCS_RESULTS)/$(SIMV) -l vcs-cv32-riscv-tests.log $(VCS_RUN_FLAGS) \
		+elf_file=$(CV32_RISCV_TESTS_FIRMWARE)/cv32_riscv_tests_firmware.elf \
		+UVM_TESTNAME=uvmt_cv32_firmware_test_c \
		+firmware=$(CV32_RISCV_TESTS_FIRMWARE)/cv32_riscv_tests_firmware.hex

# Runs tests in cv32_riscv_compliance_tests/ only
cv32-riscv-compliance-tests: $(VCS_SIM_PREREQ)  $(CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE)/cv32_riscv_compliance_tests_firmware.hex
	mkdir -p $(VCS_RESULTS)/cv32-riscv-compliance-tests && cd $(VCS_RESULTS)/cv32-riscv-compliance-tests && \
	$(VCS_RESULTS)/$(SIMV) -l vcs-cv32-riscv_compliance_tests.log -cm_name cv32-riscv-compliance-tests $(VCS_RUN_FLAGS) \
		+elf_file=$(CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE)/cv32_riscv_compliance_tests_firmware.elf \
		+UVM_TESTNAME=uvmt_cv32_firmware_test_c \
		+firmware=$(CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE)/cv32_riscv_compliance_tests_firmware.hex

unit-test:  firmware-unit-test-clean
unit-test:  $(FIRMWARE)/firmware_unit_test.hex
unit-test: ALL_VSIM_FLAGS += "+firmware=$(FIRMWARE)/firmware_unit_test.hex"
unit-test: vcs-firmware-unit-test


# Runs all tests in riscv_tests/ and riscv_compliance_tests/
cv32-firmware: comp $(FIRMWARE)/firmware.hex
	$(VCS_RESULTS)/$(SIMV) -l vcs-firmware.log \
		+UVM_TESTNAME=uvmt_cv32_firmware_test_c \
		+firmware=$(FIRMWARE)/firmware.hex

################################################################################
# Called from external compliance framework providing ELF, HEX, NM
COMPLIANCE ?= missing
riscv-compliance: $(VCS_SIM_PREREQ) $(COMPLIANCE).elf
	mkdir -p $(VCS_RESULTS)/$(@) && cd $(VCS_RESULTS)/$(@) && \
	$(VCS_RESULTS)/$(SIMV) -l vcs-$(@).log -cm_name riscv-compliance $(VCS_RUN_FLAGS) \
		+UVM_TESTNAME=uvmt_cv32_firmware_test_c \
		+elf_file=$(COMPLIANCE).elf \
		+firmware=$(COMPLIANCE).hex \
		+signature=$(COMPLIANCE).signature.output

# VCS UNIT TESTS: run each test individually. See comment header for dsim-unit-test for more info.
# TODO: update ../Common.mk to create "vcs-firmware-unit-test" target.
# Example: to run the ADDI test `make vcs-unit-test addi`
#vcs-unit-test: comp
#	$(VCS) -R -l vcs-$(UNIT_TEST).log \
#		+UVM_TESTNAME=uvmt_cv32_firmware_test_c \
#		+firmware=$(FIRMWARE)/firmware_unit_test.hex

###############################################################################
# Use Google instruction stream generator (RISCV-DV) to create new test-programs
comp_corev-dv: $(RISCVDV_PKG)
	mkdir -p $(COREVDV_PKG)/out_$(DATE)/run
	cd $(VCS_COREVDV_RESULTS) && \
	$(VCS) $(VCS_COMP_FLAGS) \
		$(QUIET) $(VCS_USER_COMPILE_ARGS) \
		+incdir+$(COREVDV_PKG)/target/cv32e40p \
		+incdir+$(RISCVDV_PKG)/user_extension \
		+incdir+$(RISCVDV_PKG)/tests \
		+incdir+$(COREVDV_PKG) \
		-f $(COREVDV_PKG)/manifest.f \
		-l vcs.log 

corev-dv: clean_riscv-dv \
          clone_riscv-dv \
		  comp_corev-dv

gen_corev-dv: 
	mkdir -p $(VCS_COREVDV_RESULTS)/$(TEST)
	# Clean old assembler generated tests in results
	for (( idx=${GEN_START_INDEX}; idx < $$((${GEN_START_INDEX} + ${GEN_NUM_TESTS})); idx++ )); do \
		rm -f ${VCS_COREVDV_RESULTS}/${TEST}/${TEST}_$$idx.S; \
	done
	cd  $(VCS_COREVDV_RESULTS)/$(TEST) && \
	../$(SIMV) -R $(VCS_RUN_FLAGS) \
		-l $(TEST)_$(GEN_START_INDEX)_$(GEN_NUM_TESTS).log \
		+start_idx=$(GEN_START_INDEX) \
		+num_of_tests=$(GEN_NUM_TESTS) \
		+UVM_TESTNAME=$(GEN_UVM_TEST) \
		+asm_file_name_opts=$(TEST) \
		$(GEN_PLUSARGS)
	# Copy out final assembler files to test directory
	for (( idx=${GEN_START_INDEX}; idx < $$((${GEN_START_INDEX} + ${GEN_NUM_TESTS})); idx++ )); do \
		ls -l ${VCS_COREVDV_RESULTS}/${TEST} > /dev/null; \
		cp ${VCS_COREVDV_RESULTS}/${TEST}/${TEST}_$$idx.S ${GEN_TEST_DIR}; \
	done

################################################################################
# Invoke post-process waveform viewer
waves:
	$(WAVES_CMD)

################################################################################
# Invoke post-process coverage viewer
cov_merge:
	$(MKDIR_P) $(VCS_RESULTS)/$(MERGED_COV_DIR)
	rm -rf $(VCS_RESULTS)/$(MERGED_COV_DIR)/*
	cd $(VCS_RESULTS)/$(MERGED_COV_DIR)

# the report is in html format: use a browser to access it when GUI mode is selected
ifeq ($(call IS_YES,$(GUI)),YES)
cov: $(COV_MERGE)
	cd $(VCS_RESULTS)/$(TEST_NAME) && browse urgReport/dashboard.html
else
cov: $(COV_MERGE)
	cd $(VCS_RESULTS)/$(TEST_NAME) && $(URG) $(COV_ARGS)
endif

###############################################################################
# Clean up your mess!

clean:
	rm -f simv
	rm -rf simv.*
	rm -rf csrc
	rm -f vc_hdrs.h
	rm -rf $(VCS_RESULTS)

# All generated files plus the clone of the RTL
clean_all: clean clean_core_tests clean_riscv-dv clean_test_programs clean-bsp
	rm -rf $(CV32E40P_PKG)
