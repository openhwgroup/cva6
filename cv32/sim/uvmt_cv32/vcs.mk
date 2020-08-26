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
VCS_RISCVDV_RESULTS ?= $(VCS_RESULTS)/riscv-dv
VCS_DIR         ?= $(VCS_RESULTS)/vcs.d
VCS_ELAB_COV     = -cm line+cond+tgl+fsm+branch+assert  -cm_dir $(MAKECMDGOALS)/$(MAKECMDGOALS).vdb

# modifications to already defined variables to take into account VCS
VCS_OVP_MODEL_DPI = $(OVP_MODEL_DPI:.so=)                    # remove extension as VCS adds it
VCS_TIMESCALE = $(shell echo "$(TIMESCALE)" | tr ' ' '=')    # -timescale=1ns/1ps

# Flags
#VCS_UVMHOME_ARG ?= /opt/uvm/1800.2-2017-0.9/
VCS_UVMHOME_ARG ?= /opt/synopsys/vcs-mx/O-2018.09-SP1-1/etc/uvm
VCS_UVM_ARGS          ?= +incdir+$(VCS_UVMHOME_ARG)/src $(VCS_UVMHOME_ARG)/src/uvm_pkg.sv -ntb_opts uvm-1.2

VCS_COMP_FLAGS  ?= -lca -sverilog -top uvmt_cv32_tb \
										$(SV_CMP_FLAGS) $(VCS_UVM_ARGS) $(VCS_TIMESCALE) \
										-assert svaext -race=all -ignore unique_checks -full64
VCS_GUI         ?=
VCS_RUN_COV      = -cm line+cond+tgl+fsm+branch+assert -cm_dir $(MAKECMDGOALS).vdb
NUM_TEST         ?= 2

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
WAVES_CMD = cd $(VCS_RESULTS)/$(TEST) && $(DVE) -vpd vcdplus.vpd 
else
WAVES_CMD = cd $(VCS_RESULTS)/$(TEST) && $(DVE) -vpd vcdplus.vpd 
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
COV_ARGS = -dir $(TEST).vdb
endif

################################################################################

VCS_FILE_LIST ?= -f $(DV_UVMT_CV32_PATH)/uvmt_cv32.flist
ifeq ($(call IS_YES,$(USE_ISS)),YES)
    VCS_FILE_LIST += -f $(DV_UVMT_CV32_PATH)/imperas_iss.flist
    VCS_USER_COMPILE_ARGS += "+define+ISS+CV32E40P_TRACE_EXECUTION"
    VCS_PLUSARGS +="+USE_ISS"
endif

VCS_RUN_BASE_FLAGS   ?= $(VCS_GUI) +UVM_VERBOSITY=$(VCS_UVM_VERBOSITY) \
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

.PHONY: comp hello_world hello-world

mk_vcs_dir:
	$(MKDIR_P) $(VCS_DIR)

hello_world: hello-world

cv32_riscv_tests: cv32-riscv-tests

cv32_riscv_compliance_tests: cv32-riscv-compliance-tests

VCS_COMP = $(VCS_COMP_FLAGS) \
		$(VCS_UVM_ARGS) \
		$(VCS_USER_COMPILE_ARGS) \
		+incdir+$(DV_UVME_CV32_PATH) \
		+incdir+$(DV_UVMT_CV32_PATH) \
		-f $(CV32E40P_MANIFEST) \
		$(VCS_FILE_LIST) \
		$(UVM_PLUSARGS)

comp: mk_vcs_dir $(CV32E40P_PKG) $(OVP_MODEL_DPI)
	cd $(VCS_RESULTS) && $(VCS) $(VCS_COMP)
	@echo "$(BANNER)"
	@echo "* $(,maSIMULATOR) compile complete"
	@echo "* Log: $(VCS_RESULTS)/vcs.log"
	@echo "$(BANNER)"

ifneq ($(call IS_NO,$(COMP)),NO)
VCS_SIM_PREREQ = comp
endif
VCS_COMP_RUN = $(VCS_RUN_FLAGS)

ifeq ($(call IS_YES,$(XRUN_SINGLE_STEP)), YES)
	XRUN_SIM_PREREQ = mk_xrun_dir $(CV32E40P_PKG) $(OVP_MODEL_DPI)
	XRUN_COMP_RUN = $(XRUN_COMP) $(XRUN_RUN_BASE_FLAGS)
endif

################################################################################
# Custom test-programs.  See comment in dsim.mk for more info
custom: $(VCS_SIM_PREREQ) $(CUSTOM_DIR)/$(CUSTOM_PROG).hex
	mkdir -p $(VCS_RESULTS)/$(CUSTOM_PROG) && cd $(VCS_RESULTS)/$(CUSTOM_PROG) && \
	$(VCS_RESULTS)/$(SIMV) -l vcs-$(CUSTOM_PROG).log -cm_test $(CUSTOM_PROG) $(VCS_COMP_RUN) \
		+UVM_TESTNAME=uvmt_cv32_firmware_test_c \
		+elf_file=$(CUSTOM_DIR)/$(CUSTOM_PROG).elf \
		+firmware=$(CUSTOM_DIR)/$(CUSTOM_PROG).hex

################################################################################
# Explicit target tests
hello-world:  $(VCS_SIM_PREREQ) $(CUSTOM)/hello_world.hex
	mkdir -p $(VCS_RESULTS)/hello-world && cd $(VCS_RESULTS)/hello-world && \
	$(VCS_RESULTS)/$(SIMV) -l vcs-hello-world.log -cm_name hello-world $(VCS_COMP_RUN) \
		+elf_file=$(CUSTOM)/hello_world.elf \
		+UVM_TESTNAME=uvmt_cv32_firmware_test_c \
		+firmware=$(CUSTOM)/hello_world.hex

misalign: $(VCS_SIM_PREREQ) $(CUSTOM)/misalign.hex
	mkdir -p $(VCS_RESULTS)/misalign && cd $(VCS_RESULTS)/misalign && \
	$(VCS_RESULTS)/$(SIMV) -l vcs-misalign.log -cm_name misalign $(VCS_COMP_RUN) \
		+elf_file=$(CUSTOM)/misalign.elf \
		+UVM_TESTNAME=uvmt_cv32_firmware_test_c \
		+firmware=$(CUSTOM)/misalign.hex

illegal: $(VCS_SIM_PREREQ) $(CUSTOM)/illegal.hex
	mkdir -p $(VCS_RESULTS)/illegal && cd $(VCS_RESULTS)/illegal && \
	$(VCS_RESULTS)/$(SIMV) -l vcs-illegal.log -cm_name illegal $(VCS_COMP_RUN) \
		+elf_file=$(CUSTOM)/illegal.elf \
		+UVM_TESTNAME=uvmt_cv32_firmware_test_c \
		+firmware=$(CUSTOM)/illegal.hex

fibonacci: $(VCS_SIM_PREREQ) $(CUSTOM)/fibonacci.hex
	mkdir -p $(VCS_RESULTS)/fibonacci && cd $(VCS_RESULTS)/fibonacci && \
	$(VCS_RESULTS)/$(SIMV) -l vcs-fibonacci.log -cm_name fibonacci $(VCS_COMP_RUN) \
		+elf_file=$(CUSTOM)/fibonacci.elf \
		+UVM_TESTNAME=uvmt_cv32_firmware_test_c \
		+firmware=$(CUSTOM)/fibonacci.hex

dhrystone: $(VCS_SIM_PREREQ) $(CUSTOM)/dhrystone.hex
	mkdir -p $(VCS_RESULTS)/dhrystone && cd $(VCS_RESULTS)/dhrystone && \
	$(VCS_RESULTS)/$(SIMV) -l vcs-dhrystonelog -cm_name dhrystone $(VCS_COMP_RUN) \
		+elf_file=$(CUSTOM)/dhrystone.elf \
		+UVM_TESTNAME=uvmt_cv32_firmware_test_c \
		+firmware=$(CUSTOM)/dhrystone.hex

riscv_ebreak_test_0: $(VCS_SIM_PREREQ) $(CUSTOM)/riscv_ebreak_test_0.hex
	mkdir -p $(VCS_RESULTS)/riscv_ebreak_test_0 && cd $(VCS_RESULTS)/riscv_ebreak_test_0 && \
	$(VCS_RESULTS)/$(SIMV) -l vcs-riscv_ebreak_test_0log -cm_name riscv_ebreak_test_0 $(VCS_COMP_RUN) \
                +elf_file=$(CUSTOM)/riscv_ebreak_test_0.elf \
                +UVM_TESTNAME=uvmt_cv32_firmware_test_c \
                +firmware=$(CUSTOM)/riscv_ebreak_test_0.hex

debug_test: $(VCS_SIM_PREREQ) $(CORE_TEST_DIR)/debug_test/debug_test.hex
	mkdir -p $(VCS_RESULTS)/debug_test && cd $(VCS_RESULTS)/debug_test && \
	$(VCS_RESULTS)/$(SIMV) -l vcs-riscv_debug_test.log -cm_name debug_test $(VCS_COMP_RUN) \
                +elf_file=$(CORE_TEST_DIR)/debug_test/debug_test.elf \
                +UVM_TESTNAME=uvmt_cv32_firmware_test_c \
                +firmware=$(CORE_TEST_DIR)/debug_test/debug_test.hex

# Runs tests in cv32_riscv_tests/ only
cv32-riscv-tests: $(VCS_SIM_PREREQ) $(CV32_RISCV_TESTS_FIRMWARE)/cv32_riscv_tests_firmware.hex
	mkdir -p $(VCS_RESULTS)/cv32-riscv-tests && cd $(VCS_RESULTS)/cv32-riscv-tests && \
	$(VCS_RESULTS)/$(SIMV) -l vcs-cv32-riscv-tests.log $(VCS_COMP_RUN) \
		+elf_file=$(CV32_RISCV_TESTS_FIRMWARE)/cv32_riscv_tests_firmware.elf \
		+UVM_TESTNAME=uvmt_cv32_firmware_test_c \
		+firmware=$(CV32_RISCV_TESTS_FIRMWARE)/cv32_riscv_tests_firmware.hex

# Runs tests in cv32_riscv_compliance_tests/ only
cv32-riscv-compliance-tests: $(VCS_SIM_PREREQ)  $(CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE)/cv32_riscv_compliance_tests_firmware.hex
	mkdir -p $(VCS_RESULTS)/cv32-riscv-compliance-tests && cd $(VCS_RESULTS)/cv32-riscv-compliance-tests && \
	$(VCS) -l vcs-cv32-riscv_compliance_tests.log -cm_name cv32-riscv-compliance-tests $(VCS_RUN_FLAGS) \
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

# VCS UNIT TESTS: run each test individually. See comment header for dsim-unit-test for more info.
# TODO: update ../Common.mk to create "vcs-firmware-unit-test" target.
# Example: to run the ADDI test `make vcs-unit-test addi`
#vcs-unit-test: comp
#	$(VCS) -R -l vcs-$(UNIT_TEST).log \
#		+UVM_TESTNAME=uvmt_cv32_firmware_test_c \
#		+firmware=$(FIRMWARE)/firmware_unit_test.hex

###############################################################################
# Use Google instruction stream generator (RISCV-DV) to create new test-programs
comp_riscv-dv:
	mkdir -p $(VCS_RISCVDV_RESULTS)
	mkdir -p $(COREVDV_PKG)/out_$(DATE)/run
	cd $(VCS_RISCVDV_RESULTS) && \
	$(VCS) $(VCS_COMP_FLAGS) \
		$(VCS_USER_COMPILE_ARGS) \
		+incdir+$(RISCVDV_PKG)/target/rv32imc \
		+incdir+$(RISCVDV_PKG)/user_extension \
		+incdir+$(RISCVDV_PKG)/tests \
		+incdir+$(COREVDV_PKG) \
		-f $(COREVDV_PKG)/manifest.f \
		-l $(COREVDV_PKG)/out_$(DATE)/run/compile.log 

gen_corev_arithmetic_base_test:
	mkdir -p $(VCS_RISCVDV_RESULTS)/corev_arithmetic_base_test	
	cd $(VCS_RISCVDV_RESULTS)/corev_arithmetic_base_test && \
	$(VCS_RESULTS)/$(SIMV) $(VCS_RUN_FLAGS) \
		+UVM_TESTNAME=corev_instr_base_test  \
		+num_of_tests=2  \
		+start_idx=0  \
		+asm_file_name_opts=riscv_arithmetic_basic_test  \
		-l $(COREVDV_PKG)/out_$(DATE)/sim_riscv_arithmetic_basic_test_0.log \
		+instr_cnt=10000 \
		+num_of_sub_program=0 \
		+directed_instr_0=riscv_int_numeric_corner_stream,4 \
		+no_fence=1 \
		+no_data_page=1 \
		+no_branch_jump=1 \
		+boot_mode=m \
		+no_csr_instr=1
	cp $(VCS_RISCVDV_RESULTS)/corev_arithmetic_base_test/*.S $(CORE_TEST_DIR)/custom

gen_corev_rand_instr_test:
	mkdir -p $(VCS_RISCVDV_RESULTS)/corev_rand_instr_test	
	cd $(VCS_RISCVDV_RESULTS)/corev_rand_instr_test && \
	$(VCS_RESULTS)/$(SIMV) $(VCS_RUN_FLAGS) \
	 	+UVM_TESTNAME=corev_instr_base_test \
		+num_of_tests=$(NUM_TESTS) \
		+start_idx=0  \
		+asm_file_name_opts=corev_rand_instr_test  \
		-l $(COREVDV_PKG)/out_$(DATE)/sim_riscv_rand_instr_test_0.log \
    +instr_cnt=10000 \
    +num_of_sub_program=5 \
    +directed_instr_0=riscv_load_store_rand_instr_stream,4 \
    +directed_instr_1=riscv_loop_instr,4 \
    +directed_instr_2=riscv_hazard_instr_stream,4 \
    +directed_instr_3=riscv_load_store_hazard_instr_stream,4 \
    +directed_instr_4=riscv_multi_page_load_store_instr_stream,4 \
    +directed_instr_5=riscv_mem_region_stress_test,4 \
    +directed_instr_6=riscv_jal_instr,4
	cp $(VCS_RISCVDV_RESULTS)/corev_rand_instr_test/*.S $(CORE_TEST_DIR)/custom

corev-dv: clean_riscv-dv \
	clone_riscv-dv \
	comp_riscv-dv \
	gen_corev_arithmetic_base_test

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
	cd $(VCS_RESULTS)/$(TEST) && browse urgReport/dashboard.html
else
cov: $(COV_MERGE)
	cd $(VCS_RESULTS)/$(TEST) && $(URG) $(COV_ARGS)
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
clean_all: clean clean_core_tests clean_riscv-dv clean_test_programs
	rm -rf $(CV32E40P_PKG)
