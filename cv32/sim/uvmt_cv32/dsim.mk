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
DSIM_WORK              ?= $(DSIM_RESULTS)/dsim_work
DSIM_IMAGE             ?= dsim.out
DSIM_RUN_FLAGS         ?=
DSIM_USE_ISS           ?= YES

DSIM_FILE_LIST ?= -f $(DV_UVMT_CV32_PATH)/uvmt_cv32.flist
ifeq ($(USE_ISS),YES)
    DSIM_FILE_LIST         += -f $(DV_UVMT_CV32_PATH)/imperas_iss.flist
    DSIM_USER_COMPILE_ARGS += "+define+ISS"
    DSIM_RUN_FLAGS         += +ovpcfg="--controlfile $(OVP_CTRL_FILE)"
endif


# Variables to control wave dumping from command the line
# Humans _always_ forget the "S", so you can have it both ways...
WAVES                  ?= 0
WAVE                   ?= 0
DUMP_WAVES             := 0

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

.PHONY: sim
		+elf_file=$(CUSTOM)/$(TYPE1_TEST_PROGRAM).elf

no_rule:
	@echo 'makefile: SIMULATOR is set to $(SIMULATOR), but no rule/target specified.'
	@echo 'try "make SIMULATOR=dsim sanity" (or just "make sanity" if shell ENV variable SIMULATOR is already set).'
#	@echo 'DUMP_WAVES=$(DUMP_WAVES)   DSIM_ACC_FLAGS=$(DSIM_ACC_FLAGS)   DSIM_DMP_FLAGS=$(DSIM_DMP_FLAGS)'

# The sanity test is defined in ../Common.mk and will change over time
#sanity: hello-world

all: clean_all sanity

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
#                 is hello_world.c.
#   UVM_TESTNAME: Class identifer (not file path) of the UVM testcase run by
#                 environment. Default is uvmt_cv32_firmware_test_c.
#
# Use cases:
#   1: Full specification of the hello-world test:
#      $ make custom SIMULATOR=dsim CUSTOM_DIR=`pwd`/../../tests/core/custom CUSTOM_PROG=hello_world UVM_TESTNAME=uvmt_cv32_firmware_test_c
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

################################################################################
# Commonly used targets:
#      Here for historical reasons - mostly (completely?) superceeded by the
#      custom target.
#
hello-world: comp $(CUSTOM)/hello_world.hex $(CUSTOM)/hello_world.elf
	mkdir -p $(DSIM_RESULTS)/hello-world && cd $(DSIM_RESULTS)/hello-world  && \
	$(DSIM) -l dsim-hello-world.log -image $(DSIM_IMAGE) \
		-work $(DSIM_WORK) $(DSIM_RUN_FLAGS) $(DSIM_DMP_FLAGS) \
		-sv_lib $(UVM_HOME)/src/dpi/libuvm_dpi.so \
		-sv_lib $(OVP_MODEL_DPI) \
		+UVM_TESTNAME=uvmt_cv32_firmware_test_c \
		+firmware=$(CUSTOM)/hello_world.hex \
		+elf_file=$(CUSTOM)/hello_world.elf
#		+nm_file=$(CUSTOM)/hello_world.nm
#		+verbose

debug_test: comp $(CORE_TEST_DIR)/debug_test/debug_test.hex
	mkdir -p $(DSIM_RESULTS)/debug_test && cd $(DSIM_RESULTS)/debug_test  && \
	$(DSIM) -l dsim-debug_test.log -image $(DSIM_IMAGE) \
		-work $(DSIM_WORK) $(DSIM_RUN_FLAGS) $(DSIM_DMP_FLAGS) \
		-sv_lib $(UVM_HOME)/src/dpi/libuvm_dpi.so \
		-sv_lib $(OVP_MODEL_DPI) \
    +UVM_TESTNAME=uvmt_cv32_firmware_test_c \
    +firmware=$(CORE_TEST_DIR)/debug_test/debug_test.hex \
    +elf_file=$(CORE_TEST_DIR)/debug_test/debug_test.elf \

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
	mkdir -p $(DSIM_RESULTS)/hello_world && cd $(DSIM_RESULTS)/hello_world  && \
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
comp_riscv-dv:
	mkdir -p $(COREVDV_PKG)/out_$(DATE)/dsim
	dsim -sv \
		-work $(COREVDV_PKG)/out_$(DATE)/dsim \
		-genimage image \
		+incdir+$(UVM_HOME)/src \
		$(UVM_HOME)/src/uvm_pkg.sv \
		+define+DSIM \
		-suppress EnumMustBePositive \
		-suppress SliceOOB \
		+incdir+$(RISCVDV_PKG)/target/rv32imc \
		+incdir+$(RISCVDV_PKG)/user_extension \
		+incdir+$(RISCVDV_PKG)/tests \
		+incdir+$(COREVDV_PKG) \
		-f $(COREVDV_PKG)/manifest.f \
		-l $(COREVDV_PKG)/out_$(DATE)/dsim/compile.log 

#riscv-test: riscv-dv
#		+asm_file_name=$(RISCVDV_PKG)/out_2020-06-24/asm_tests/riscv_arithmetic_basic_test  \

gen_corev_arithmetic_base_test:
	dsim -sv_seed $(RNDSEED) \
		-sv_lib $(UVM_HOME)/src/dpi/libuvm_dpi.so \
		+acc+rwb \
		-image image \
		-work $(COREVDV_PKG)/out_$(DATE)/dsim \
		+UVM_TESTNAME=corev_instr_base_test  \
		+num_of_tests=2  \
		+start_idx=0  \
		+asm_file_name_opts=corev_arithmetic_base_test  \
		-l $(COREVDV_PKG)/out_$(DATE)/sim_riscv_arithmetic_basic_test_0.log \
		+instr_cnt=10000 \
		+num_of_sub_program=0 \
		+directed_instr_0=riscv_int_numeric_corner_stream,4 \
		+no_fence=1 \
		+no_data_page=1 \
		+no_branch_jump=1 \
		+boot_mode=m \
		+no_csr_instr=1
	mv *.S $(CORE_TEST_DIR)/custom

gen_corev_rand_instr_test:
	dsim  -sv_seed $(RNDSEED) \
		-sv_lib $(UVM_HOME)/src/dpi/libuvm_dpi.so \
		+acc+rwb \
		-image image \
		-work $(COREVDV_PKG)/out_$(DATE)/dsim \
	 	+UVM_TESTNAME=corev_instr_base_test \
		+num_of_tests=2  \
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
	mv *.S $(CORE_TEST_DIR)/custom

gen_corev_jump_stress_test:
	dsim  -sv_seed $(RNDSEED) \
		-sv_lib $(UVM_HOME)/src/dpi/libuvm_dpi.so \
		+acc+rwb \
		-image image \
		-work $(COREVDV_PKG)/out_$(DATE)/dsim \
	 	+UVM_TESTNAME=corev_instr_base_test \
		+num_of_tests=2  \
		+start_idx=0  \
		+asm_file_name_opts=corev_jump_stress_test  \
		-l $(COREVDV_PKG)/out_$(DATE)/sim_riscv_jump_stress_test_0.log \
		+instr_cnt=5000 \
		+num_of_sub_program=5 \
		+directed_instr_1=riscv_jal_instr,20
	mv *.S $(CORE_TEST_DIR)/custom

corev-dv: clean_riscv-dv \
	  clone_riscv-dv \
	  comp_riscv-dv \
	  gen_corev_arithmetic_base_test \
	  gen_corev_rand_instr_test \
	  gen_corev_jump_stress_test

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
clean_all: clean clean_core_tests clean_riscv-dv clean_test_programs
	rm -rf $(CV32E40P_PKG)
