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

# modifications to already defined variables to take into account VCS
VCS_OVP_MODEL_DPI = $(OVP_MODEL_DPI:.so=)                    # remove extension as VCS adds it
VCS_TIMESCALE = $(shell echo "$(TIMESCALE)" | tr ' ' '=')    # -timescale=1ns/1ps

UVM_HOME ?= /opt/uvm/1800.2-2017-0.9/

VCS_VERSION           ?= O-2018.09-SP1-1
VCS_HOME              ?= /opt/synopsys/vcs-mx/$(VCS_VERSION)
VCS                   ?= vcs
VCS_CMP_FLAGS         ?= $(VCS_TIMESCALE) $(SV_CMP_FLAGS) -sverilog -top uvmt_cv32_tb
VCS_UVM_ARGS          ?= +incdir+$(UVM_HOME)/src $(UVM_HOME)/src/uvm_pkg.sv -ntb_opts uvm-1.2
VCS_RESULTS           ?= $(PWD)/vcs_results
VCS_WORK              ?= $(VCS_RESULTS)/vcs_work
VCS_USE_ISS           ?= YES

VCS_FILE_LIST ?= -f $(DV_UVMT_CV32_PATH)/uvmt_cv32.flist
ifeq ($(VCS_USE_ISS),YES)
    VCS_FILE_LIST         += -f $(DV_UVMT_CV32_PATH)/imperas_iss.flist
    VCS_USER_COMPILE_ARGS += "+define+ISS+CV32E40P_TRACE_EXECUTION"
    VCS_RUN_FLAGS         +="+USE_ISS"
endif


.PHONY: sim
		+elf_file=$(CUSTOM)/$(TYPE1_TEST_PROGRAM).elf

no_rule:
	@echo 'makefile: SIMULATOR is set to $(SIMULATOR), but no rule/target specified.'
	@echo 'try "make SIMULATOR=vcs sanity" (or just "make sanity" if shell ENV variable SIMULATOR is already set).'

# The sanity test is defined in ../Common.mk and will change over time
#sanity: hello-world

all: clean_all sanity

help:
	vcs -help

mk_results:
	$(MKDIR_P) $(VCS_RESULTS)
	$(MKDIR_P) $(VCS_WORK)

# VCS compile target
comp: mk_results $(CV32E40P_PKG) $(OVPM_DIR)
	$(VCS) \
		$(VCS_CMP_FLAGS) \
		$(VCS_UVM_ARGS) \
		-assert svaext -race=all -ignore unique_checks -full64 \
		+incdir+$(DV_UVME_CV32_PATH) \
		+incdir+$(DV_UVMT_CV32_PATH) \
		-f $(CV32E40P_MANIFEST) \
		$(VCS_FILE_LIST)


################################################################################
# Running custom test-programs':
#   The "custom" target provides the ability to specify both the testcase run by
#   the UVM environment and a C or assembly test-program to be executed by the
#   core. Note that the UVM testcase is required to load the compiled program
#   into the core's memory.
#
# User defined variables used by this target:
#   CUSTOM_DIR:   Absolute, not relative, path to the custom C program. Default
#                 is `pwd`/../../tests/core/custom.
#   CUSTOM_PROG:  C or assembler test-program that executes on the core. Default
#                 is hello_world.c.
#   UVM_TESTNAME: Class identifer (not file path) of the UVM testcase run by
#                 environment. Default is uvmt_cv32_firmware_test_c.
#
# Use cases:
#   1: Full specification of the hello-world test:
#      $ make custom SIMULATOR=vcs CUSTOM_DIR=`pwd`/../../tests/core/custom CUSTOM_PROG=hello_world UVM_TESTNAME=uvmt_cv32_firmware_test_c
#
#   2: Same thing, using the defaults in these Makefiles:
#      $ make custom
#
#   3: Run ../../tests/core/custom/fibonacci.c
#      $ make custom CUSTOM_PROG=fibonacci
#
#   4: Run your own "custom program" located in ../../tests/core/custom
#      $ make custom CUSTOM_PROG=<my_custom_test_program>
#
custom: comp $(CUSTOM_DIR)/$(CUSTOM_PROG).hex $(CUSTOM_DIR)/$(CUSTOM_PROG).elf
	mkdir -p $(VCS_RESULTS)/$(CUSTOM_PROG) && cd $(VCS_RESULTS)/$(CUSTOM_PROG)  && \
	$(VCS_RESULTS)/../simv -l vcs-$(CUSTOM_PROG).log \
		-sv_lib $(VCS_OVP_MODEL_DPI) \
		+UVM_TESTNAME=$(UVM_TESTNAME) \
		+firmware=$(CUSTOM_DIR)/$(CUSTOM_PROG).hex \
		+elf_file=$(CUSTOM_DIR)/$(CUSTOM_PROG).elf

# Similar to above, but for the ASM directory.
asm: comp $(ASM_DIR)/$(ASM_PROG).hex $(ASM_DIR)/$(ASM_PROG).elf
	mkdir -p $(VCS_RESULTS)/$(ASM_PROG) && cd $(VCS_RESULTS)/$(ASM_PROG)  && \
	$(VCS_RESULTS)/../simv -l vcs-$(CUSTOM_PROG).log \
		-sv_lib $(VCS_OVP_MODEL_DPI) \
		+UVM_TESTNAME=$(UVM_TESTNAME) \
		+firmware=$(ASM_DIR)/$(ASM_PROG).hex \
		+elf_file=$(ASM_DIR)/$(ASM_PROG).elf

################################################################################
# Commonly used targets:
#      Here for historical reasons - mostly (completely?) superceeded by the
#      custom target.
#
hello-world: comp $(CUSTOM)/hello_world.hex $(CUSTOM)/hello_world.elf
	mkdir -p $(VCS_RESULTS)/hello-world && cd $(VCS_RESULTS)/hello-world  && \
	$(VCS_RESULTS)/../simv -l vcs-hello-world.log \
		-sv_lib $(VCS_OVP_MODEL_DPI) \
		+UVM_TESTNAME=uvmt_cv32_firmware_test_c \
		+firmware=$(CUSTOM)/hello_world.hex \
		+elf_file=$(CUSTOM)/hello_world.elf

# Runs tests in riscv_tests/ only
cv32-riscv-tests: comp $(CV32_RISCV_TESTS_FIRMWARE)/cv32_riscv_tests_firmware.hex $(CV32_RISCV_TESTS_FIRMWARE)/cv32_riscv_tests_firmware.elf
	mkdir -p $(VCS_RESULTS)/cv32-riscv-tests && cd $(VCS_RESULTS)/cv32-riscv-tests && \
	$(VCS_RESULTS)/../simv -l vcs-riscv_tests.log \
		-sv_lib $(VCS_OVP_MODEL_DPI) \
		+UVM_TESTNAME=uvmt_cv32_firmware_test_c \
		+firmware=$(CV32_RISCV_TESTS_FIRMWARE)/cv32_riscv_tests_firmware.hex \
		+elf_file=$(CV32_RISCV_TESTS_FIRMWARE)/cv32_riscv_tests_firmware.elf

# Runs tests in riscv_compliance_tests/ only
cv32-riscv-compliance-tests: comp $(CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE)/cv32_riscv_compliance_tests_firmware.hex $(CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE)/cv32_riscv_compliance_tests_firmware.elf
	mkdir -p $(VCS_RESULTS)/cv32-riscv-compliance-tests && cd $(VCS_RESULTS)/cv32-riscv-compliance-tests && \
	$(VCS_RESULTS)/../simv -l vcs-riscv_compliance_tests.log \
		-sv_lib $(VCS_OVP_MODEL_DPI) \
		+UVM_TESTNAME=uvmt_cv32_firmware_test_c \
		+firmware=$(CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE)/cv32_riscv_compliance_tests_firmware.hex \
		+elf_file=$(CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE)/cv32_riscv_compliance_tests_firmware.elf

# Runs all tests in riscv_tests/ and riscv_compliance_tests/
cv32-firmware: comp $(FIRMWARE)/firmware.hex $(FIRMWARE)/firmware.elf
	mkdir -p $(VCS_RESULTS)/firmware && cd $(VCS_RESULTS)/firmware && \
	$(VCS_RESULTS)/../simv -l vcs-firmware.log \
		-sv_lib $(VCS_OVP_MODEL_DPI) \
		+UVM_TESTNAME=uvmt_cv32_firmware_test_c \
		+firmware=$(FIRMWARE)/firmware.hex \
		+elf_file=$(FIRMWARE)/firmware.elf

# Placeholder for future testing via Google ISG (riscv-dv)
# These targets are defined in ./Makefile
corev-dv: clean_riscv-dv \
	  clone_riscv-dv

clean:
	rm -f simv
	rm -rf simv.*
	rm -rf csrc
	rm -f vc_hdrs.h
	rm -rf $(VCS_RESULTS)

# All generated files plus the clone of the RTL
clean_all: clean clean_core_tests clean_riscvdv clean_test_programs
	rm -rf $(CV32E40P_PKG)
