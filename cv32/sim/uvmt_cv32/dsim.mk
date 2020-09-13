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
# DSIM-specific Makefile for the CV32E40P "uvmt_cv32" testbench.
# DSIM is the Metrics Technologies SystemVerilog simulator  (https://metrics.ca/)
#
###############################################################################

DSIM                    = dsim
DSIM_HOME              ?= /tools/Metrics/dsim
DSIM_CMP_FLAGS         ?= $(TIMESCALE) $(SV_CMP_FLAGS) -top uvmt_cv32_tb
DSIM_UVM_ARGS          ?= +incdir+$(UVM_HOME)/src $(UVM_HOME)/src/uvm_pkg.sv
DSIM_RESULTS           ?= $(PWD)/dsim_results
DSIM_COREVDV_RESULTS   ?= $(PWD)/dsim_results/corev-dv
DSIM_WORK              ?= $(DSIM_RESULTS)/dsim_work
DSIM_IMAGE             ?= dsim.out
DSIM_RUN_FLAGS         ?=
DSIM_CODE_COV_SCOPE    ?= $(PWD)/../tools/dsim/ccov_scopes.txt
DSIM_USE_ISS           ?= YES

DSIM_FILE_LIST ?= -f $(DV_UVMT_CV32_PATH)/uvmt_cv32.flist
ifeq ($(USE_ISS),YES)
    DSIM_FILE_LIST         += -f $(DV_UVMT_CV32_PATH)/imperas_iss.flist
    DSIM_USER_COMPILE_ARGS += "+define+ISS+CV32E40P_TRACE_EXECUTION"
#    DSIM_USER_COMPILE_ARGS += "+define+CV32E40P_ASSERT_ON+ISS+CV32E40P_TRACE_EXECUTION"
#    DSIM_RUN_FLAGS         += +ovpcfg="--controlfile $(OVP_CTRL_FILE)"
endif
DSIM_RUN_FLAGS         += $(USER_RUN_FLAGS)


# Variables to control wave dumping from command the line
# Humans _always_ forget the "S", so you can have it both ways...
WAVES                  ?= 0
WAVE                   ?= 0
DUMP_WAVES             := 0
# Code Coverage collected by default
CCOV                   ?= 1

ifneq ($(WAVES), 0)
DUMP_WAVES = 1
endif

ifneq ($(WAVE), 0)
DUMP_WAVES = 1
endif

ifneq ($(DUMP_WAVES), 0)
DSIM_ACC_FLAGS ?= +acc
DSIM_DMP_FILE  ?= dsim.fst
DSIM_DMP_FLAGS ?= -waves $(DSIM_DMP_FILE)
endif

ifneq ($(CCOV), 0)
	DSIM_USER_COMPILE_ARGS += -code-cov block -code-cov-scope-specs $(DSIM_CODE_COV_SCOPE)
	DSIM_RUN_FLAGS         += -code-cov block -code-cov-scope-specs $(DSIM_CODE_COV_SCOPE)
endif

.PHONY: sim
		+elf_file=$(CUSTOM)/$(TYPE1_TEST_PROGRAM).elf

no_rule:
	@echo 'makefile: SIMULATOR is set to $(SIMULATOR), but no rule/target specified.'
	@echo 'try "make SIMULATOR=dsim sanity" (or just "make sanity" if shell ENV variable SIMULATOR is already set).'
#	@echo 'DUMP_WAVES=$(DUMP_WAVES)   DSIM_ACC_FLAGS=$(DSIM_ACC_FLAGS)   DSIM_DMP_FLAGS=$(DSIM_DMP_FLAGS)'

all: clean_all hello-world

# This special target is to support the special sanity target in the Common Makefile
hello-world:
	$(MAKE) test TEST=hello-world

help:
	dsim -help

mk_results: 
	$(MKDIR_P) $(DSIM_RESULTS)
	$(MKDIR_P) $(DSIM_WORK)

################################################################################
# DSIM compile target
#      - TODO: cd $(DSIM_RESULTS) - incompatible with pkg file
comp: mk_results $(CV32E40P_PKG) $(OVP_MODEL_DPI)
	$(DSIM) \
		$(DSIM_CMP_FLAGS) \
		$(DSIM_UVM_ARGS) \
		$(DSIM_ACC_FLAGS) \
		$(CFG_COMPILE_FLAGS) \
		$(DSIM_USER_COMPILE_ARGS) \
		+incdir+$(DV_UVME_CV32_PATH) \
		+incdir+$(DV_UVMT_CV32_PATH) \
		-f $(CV32E40P_MANIFEST) \
		$(DSIM_FILE_LIST) \
		-work $(DSIM_WORK) \
		+$(UVM_PLUSARGS) \
		-genimage $(DSIM_IMAGE)


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
#                 is hello-world.c.
#   UVM_TESTNAME: Class identifer (not file path) of the UVM testcase run by
#                 environment. Default is uvmt_cv32_firmware_test_c.
#
# Use cases:
#   1: Full specification of the hello-world test:
#      $ make custom SIMULATOR=dsim CUSTOM_DIR=`pwd`/../../tests/core/custom CUSTOM_PROG=hello-world UVM_TESTNAME=uvmt_cv32_firmware_test_c
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
	mkdir -p $(DSIM_RESULTS)/$(CUSTOM_PROG) && cd $(DSIM_RESULTS)/$(CUSTOM_PROG)  && \
	$(DSIM) -l dsim-$(CUSTOM_PROG).log -image $(DSIM_IMAGE) \
		-work $(DSIM_WORK) $(DSIM_RUN_FLAGS) $(DSIM_DMP_FLAGS) \
		-sv_lib $(UVM_HOME)/src/dpi/libuvm_dpi.so \
		-sv_lib $(OVP_MODEL_DPI) \
		+UVM_TESTNAME=$(UVM_TESTNAME) \
		+firmware=$(CUSTOM_DIR)/$(CUSTOM_PROG).hex \
		+elf_file=$(CUSTOM_DIR)/$(CUSTOM_PROG).elf

################################################################################
# General test execution target "test"
# 

################################################################################
# If the configuration specified OVPSIM arguments, generate an ovpsim.ic file and
# set IMPERAS_TOOLS to point to it
gen_ovpsim_ic:
	@if [ ! -z "$(CFG_OVPSIM)" ]; then \
		mkdir -p $(DSIM_RESULTS)/$(TEST_NAME); \
		echo "$(CFG_OVPSIM)" > $(DSIM_RESULTS)/$(TEST_NAME)/ovpsim.ic; \
	fi
ifneq ($(CFG_OVPSIM),)
export IMPERAS_TOOLS=$(DSIM_RESULTS)/$(TEST_NAME)/ovpsim.ic
endif

# Skip compile if COMP is specified and negative
ifneq ($(call IS_NO,$(COMP)),NO)
DSIM_SIM_PREREQ = comp
endif

test: $(DSIM_SIM_PREREQ) $(TEST_TEST_DIR)/$(TEST_NAME).hex gen_ovpsim_ic
	mkdir -p $(DSIM_RESULTS)/$(TEST_NAME) && \
	cd $(DSIM_RESULTS)/$(TEST_NAME) && \
		$(DSIM) \
			-l dsim-$(TEST_NAME).log \
			-image $(DSIM_IMAGE) \
			-work $(DSIM_WORK) \
			$(DSIM_RUN_FLAGS) \
			$(DSIM_DMP_FLAGS) \
			$(TEST_PLUSARGS) \
			-sv_lib $(UVM_HOME)/src/dpi/libuvm_dpi.so \
			-sv_lib $(OVP_MODEL_DPI) \
			+UVM_TESTNAME=$(TEST_UVM_TEST) \
			+firmware=$(TEST_TEST_DIR)/$(TEST_NAME).hex \
			+elf_file=$(TEST_TEST_DIR)/$(TEST_NAME).elf

# Similar to above, but for the ASM directory.
asm: comp $(ASM_DIR)/$(ASM_PROG).hex $(ASM_DIR)/$(ASM_PROG).elf
	mkdir -p $(DSIM_RESULTS)/$(ASM_PROG) && cd $(DSIM_RESULTS)/$(ASM_PROG)  && \
	$(DSIM) -l dsim-$(ASM_PROG).log -image $(DSIM_IMAGE) \
		-work $(DSIM_WORK) $(DSIM_RUN_FLAGS) $(DSIM_DMP_FLAGS) \
		-sv_lib $(UVM_HOME)/src/dpi/libuvm_dpi.so \
		-sv_lib $(OVP_MODEL_DPI) \
		+UVM_TESTNAME=$(UVM_TESTNAME) \
		+firmware=$(ASM_DIR)/$(ASM_PROG).hex \
		+elf_file=$(ASM_DIR)/$(ASM_PROG).elf

###############################################################################
# Run a test-program from the RISC-V Compliance Test-suite. The parent Makefile
# of this <sim>.mk implements "build_compliance", the target that compiles the
# test-programs.
#
# There is a dependancy between RISCV_ISA and COMPLIANCE_PROG which *you* are
# required to know.  For example, the I-ADD-01 test-program is part of the rv32i
# testsuite.
# So this works:
#                make compliance RISCV_ISA=rv32i COMPLIANCE_PROG=I-ADD-01
# But this does not:
#                make compliance RISCV_ISA=rv32imc COMPLIANCE_PROG=I-ADD-01
# 
COMPLIANCE_PROG ?= I-ADD-01
#compliance: comp
compliance: comp build_compliance
	mkdir -p $(DSIM_RESULTS)/$(COMPLIANCE_PROG) && cd $(DSIM_RESULTS)/$(COMPLIANCE_PROG)  && \
	$(DSIM) -l dsim-$(COMPLIANCE_PROG).log -image $(DSIM_IMAGE) \
		-work $(DSIM_WORK) $(DSIM_RUN_FLAGS) $(DSIM_DMP_FLAGS) \
		-sv_lib $(UVM_HOME)/src/dpi/libuvm_dpi.so \
		-sv_lib $(OVP_MODEL_DPI) \
		+UVM_TESTNAME=$(UVM_TESTNAME) \
		+firmware=$(COMPLIANCE_PKG)/work/$(RISCV_ISA)/$(COMPLIANCE_PROG).hex \
		+elf_file=$(COMPLIANCE_PKG)/work/$(RISCV_ISA)/$(COMPLIANCE_PROG).elf

################################################################################
# Commonly used targets:
#      Here for historical reasons - mostly (completely?) superceeded by the
#      custom target.
#

debug_test: comp $(CORE_TEST_DIR)/debug_test/debug_test.hex
	mkdir -p $(DSIM_RESULTS)/debug_test && cd $(DSIM_RESULTS)/debug_test  && \
	$(DSIM) -l dsim-debug_test.log -image $(DSIM_IMAGE) \
		-work $(DSIM_WORK) $(DSIM_RUN_FLAGS) $(DSIM_DMP_FLAGS) \
		-sv_lib $(UVM_HOME)/src/dpi/libuvm_dpi.so \
		-sv_lib $(OVP_MODEL_DPI) \
    +UVM_TESTNAME=uvmt_cv32_firmware_test_c \
    +firmware=$(CORE_TEST_DIR)/debug_test/debug_test.hex \
    +elf_file=$(CORE_TEST_DIR)/debug_test/debug_test.elf

# Runs tests in riscv_tests/ only
cv32-riscv-tests: comp $(CV32_RISCV_TESTS_FIRMWARE)/cv32_riscv_tests_firmware.hex $(CV32_RISCV_TESTS_FIRMWARE)/cv32_riscv_tests_firmware.elf
	mkdir -p $(DSIM_RESULTS)/cv32-riscv-tests && cd $(DSIM_RESULTS)/cv32-riscv-tests && \
	$(DSIM) -l dsim-riscv_tests.log -image $(DSIM_IMAGE) \
		-work $(DSIM_WORK) $(DSIM_RUN_FLAGS) $(DSIM_DMP_FLAGS) \
		-sv_lib $(UVM_HOME)/src/dpi/libuvm_dpi.so \
		-sv_lib $(OVP_MODEL_DPI) \
		+UVM_TESTNAME=uvmt_cv32_firmware_test_c \
		+firmware=$(CV32_RISCV_TESTS_FIRMWARE)/cv32_riscv_tests_firmware.hex \
		+elf_file=$(CV32_RISCV_TESTS_FIRMWARE)/cv32_riscv_tests_firmware.elf

# Runs tests in riscv_compliance_tests/ only
cv32-riscv-compliance-tests: comp $(CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE)/cv32_riscv_compliance_tests_firmware.hex $(CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE)/cv32_riscv_compliance_tests_firmware.elf
	mkdir -p $(DSIM_RESULTS)/cv32-riscv-compliance-tests && cd $(DSIM_RESULTS)/cv32-riscv-compliance-tests && \
	$(DSIM) -l dsim-riscv_compliance_tests.log -image $(DSIM_IMAGE) \
		-work $(DSIM_WORK) $(DSIM_RUN_FLAGS) $(DSIM_DMP_FLAGS) \
		-sv_lib $(UVM_HOME)/src/dpi/libuvm_dpi.so \
		-sv_lib $(OVP_MODEL_DPI) \
		+UVM_TESTNAME=uvmt_cv32_firmware_test_c \
		+firmware=$(CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE)/cv32_riscv_compliance_tests_firmware.hex \
		+elf_file=$(CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE)/cv32_riscv_compliance_tests_firmware.elf

# Runs all tests in riscv_tests/ and riscv_compliance_tests/
cv32-firmware: comp $(FIRMWARE)/firmware.hex $(FIRMWARE)/firmware.elf
	mkdir -p $(DSIM_RESULTS)/firmware && cd $(DSIM_RESULTS)/firmware && \
	$(DSIM) -l dsim-firmware.log -image $(DSIM_IMAGE) \
		-work $(DSIM_WORK) $(DSIM_RUN_FLAGS) $(DSIM_DMP_FLAGS) \
		-sv_lib $(UVM_HOME)/src/dpi/libuvm_dpi.so \
		-sv_lib $(OVP_MODEL_DPI) \
		+UVM_TESTNAME=uvmt_cv32_firmware_test_c \
		+firmware=$(FIRMWARE)/firmware.hex \
		+elf_file=$(FIRMWARE)/firmware.elf

# Mythical no-test-program testcase.  Might never be used.  Not known tow work
no-test-program: comp
	mkdir -p $(DSIM_RESULTS)/hello-world && cd $(DSIM_RESULTS)/hello-world  && \
	$(DSIM) -l dsim-$(UVM_TESTNAME).log -image $(DSIM_IMAGE) \
		-work $(DSIM_WORK) $(DSIM_RUN_FLAGS) $(DSIM_DMP_FLAGS) \
		-sv_lib $(UVM_HOME)/src/dpi/libuvm_dpi.so \
		-sv_lib $(OVP_MODEL_DPI) \
		+UVM_TESTNAME=$(UVM_TESTNAME)
#		+firmware=$(CUSTOM_DIR)/$(CUSTOM_PROG).hex \
#		+elf_file=$(CUSTOM_DIR)/$(CUSTOM_PROG).elf


################################################################################
# DSIM UNIT TESTS: run each test individually.
#                  Example: to run the ADDI test `make dsim-unit-test addi`
# DO NOT INVOKE rule "dsim-firmware-unit-test" directly.   It is a support
# rule for rule "dsim-unit-test" (in included ../Firmware.mk).
dsim-firmware-unit-test: comp
	mkdir -p $(DSIM_RESULTS)/firmware && cd $(DSIM_RESULTS)/firmware && \
	$(DSIM) -l dsim-$(UNIT_TEST).log -image $(DSIM_IMAGE) \
		-work $(DSIM_WORK) $(DSIM_RUN_FLAGS) $(DSIM_DMP_FLAGS) \
		-sv_lib $(UVM_HOME)/src/dpi/libuvm_dpi.so \
		-sv_lib $(OVP_MODEL_DPI) \
		+UVM_TESTNAME=uvmt_cv32_firmware_test_c \
		+firmware=$(FIRMWARE)/firmware_unit_test.hex \
		+elf_file=$(FIRMWARE)/firmware_unit_test.elf

# Aliases for 'dsim-unit-test' (defined in ../Common.mk)
.PHONY: unit-test
unit-test: dsim-unit-test

###############################################################################
# Use Google instruction stream generator (RISCV-DV) to create new test-programs
#riscv-dv: clone_riscv-dv
comp_corev-dv:
	# FIXME:strichmo:Please remove this!
	mkdir -p $(COREVDV_PKG)/out_$(DATE)/dsim
	mkdir -p $(DSIM_COREVDV_RESULTS)
	dsim -sv \
		-work $(DSIM_COREVDV_RESULTS)/dsim \
		-genimage image \
		+incdir+$(UVM_HOME)/src \
		$(UVM_HOME)/src/uvm_pkg.sv \
		+define+DSIM \
		-suppress EnumMustBePositive \
		-suppress SliceOOB \
		+incdir+$(COREVDV_PKG)/target/cv32e40p \
		+incdir+$(RISCVDV_PKG)/user_extension \
		+incdir+$(RISCVDV_PKG)/tests \
		+incdir+$(COREVDV_PKG) \
		-f $(COREVDV_PKG)/manifest.f \
		-l $(DSIM_COREVDV_RESULTS)/compile.log

#riscv-test: riscv-dv
#		+asm_file_name=$(RISCVDV_PKG)/out_2020-06-24/asm_tests/riscv_arithmetic_basic_test  \

gen_corev-dv: 
	mkdir -p $(DSIM_COREVDV_RESULTS)/$(TEST)
	# Clean old assembler generated tests in results
	idx=$(GEN_START_INDEX); sum=$$(($(GEN_START_INDEX) + $(GEN_NUM_TESTS))); \
	while [ $$idx -lt $${sum} ]; do \
		rm -f ${DSIM_COREVDV_RESULTS}/${TEST}/${TEST}_$$idx.S; \
		echo "idx = $$idx"; \
		idx=$$((idx + 1)); \
	done
	cd  $(DSIM_COREVDV_RESULTS)/$(TEST) && \
	dsim  -sv_seed $(RNDSEED) \
		-sv_lib $(UVM_HOME)/src/dpi/libuvm_dpi.so \
		+acc+rwb \
		-image image \
		-work $(DSIM_COREVDV_RESULTS)/dsim \
	 	+UVM_TESTNAME=$(GEN_UVM_TEST) \
		+num_of_tests=$(GEN_NUM_TESTS) \
		+start_idx=$(GEN_START_INDEX)  \
		+asm_file_name_opts=$(TEST) \
		-l $(TEST)_$(GEN_START_INDEX)_$(GEN_NUM_TESTS).log \
		$(GEN_PLUSARGS)
	# Copy out final assembler files to test directory
	idx=$(GEN_START_INDEX); sum=$$(($(GEN_START_INDEX) + $(GEN_NUM_TESTS))); \
	while [ $$idx -lt $${sum} ]; do \
		cp ${DSIM_COREVDV_RESULTS}/${TEST}/${TEST}_$$idx.S ${GEN_TEST_DIR}; \
		idx=$$((idx + 1)); \
	done

corev-dv: clean_riscv-dv \
	  clone_riscv-dv \
	  comp_corev-dv

###############################################################################
# Clean up your mess!

# Metrics dsim cleanup
clean:
	rm -f dsim.log
	rm -f dsim-*.log
	rm -f metrics_history.db
	rm -f metrics.db
	rm -f metrics.xml
	rm -f trace_core_00_0.log
	rm -rf dsim_work
	rm -f dsim.env
	rm -f $(DSIM_IMAGE)
	rm -rf $(DSIM_RESULTS)

# All generated files plus the clone of the RTL
clean_all: clean clean_core_tests clean_riscv-dv clean_test_programs clean-bsp clean_compliance
	rm -rf $(CV32E40P_PKG)

