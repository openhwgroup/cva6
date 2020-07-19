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
# XRUN-specific Makefile for the CV32E40P "uvmt_cv32" testbench.
# XRUN is the Cadence Xcelium SystemVerilog simulator (https://cadence.com/)
#
###############################################################################

XRUN              = xrun
XRUN_UVMHOME_ARG ?= CDNS-1.2-ML
XRUN_COMP_FLAGS  ?= -64bit -disable_sem2009 -access +rwc -q -clean \
                   -top uvmt_cv32_tb -sv -uvm -uvmhome $(XRUN_UVMHOME_ARG) \
                   $(TIMESCALE) $(SV_CMP_FLAGS)
XRUN_DIR         ?= xcelium.d
XRUN_GUI         ?=
XRUN_SINGLE_STEP ?=
#XRUN_VELABCOVERAGE = -covdut uvmt_cv32_tb -coverage function
#XRUN_VRUNCOVERAGE  = -covoverwrite -covtest uvmt_cv32_tb -covscope uvmt_cv32_tb
# VCOVERAGE     = imc -load cov_work/$(TESTBENCH)/$(TESTBENCH) -execcmd "report -summary"

XRUN_FILE_LIST ?= -f $(DV_UVMT_CV32_PATH)/uvmt_cv32.flist
ifeq ($(USE_ISS),YES)
    XRUN_FILE_LIST += -f $(DV_UVMT_CV32_PATH)/imperas_iss.flist
    XRUN_USER_COMPILE_ARGS += "+define+ISS+CV32E40P_TRACE_EXECUTION"
    XRUN_PLUSARGS +="+USE_ISS"
#     XRUN_PLUSARGS += +USE_ISS +ovpcfg="--controlfile $(OVP_CTRL_FILE)"
endif

XRUN_RUN_BASE_FLAGS   ?= -64bit $(XRUN_GUI) +UVM_VERBOSITY=$(XRUN_UVM_VERBOSITY) $(XRUN_PLUSARGS) -sv_lib $(OVP_MODEL_DPI)
# Simulate using latest elab
XRUN_RUN_FLAGS        ?= -R $(XRUN_RUN_BASE_FLAGS)

no_rule:
	@echo 'makefile: SIMULATOR is set to $(SIMULATOR), but no rule/target specified.'
	@echo 'try "make SIMULATOR=xrun sanity" (or just "make sanity" if shell ENV variable SIMULATOR is already set).'

help:
	xrun -help

.PHONY: comp hello_world hello-world

mk_xrun_dir: 
	$(MKDIR_P) $(XRUN_DIR)

hello_world: hello-world

cv32_riscv_tests: cv32-riscv-tests 

cv32_riscv_compliance_tests: cv32-riscv-compliance-tests 

XRUN_COMP = 	$(XRUN_COMP_FLAGS) \
		$(XRUN_USER_COMPILE_ARGS) \
		+incdir+$(DV_UVME_CV32_PATH) \
		+incdir+$(DV_UVMT_CV32_PATH) \
		-f $(CV32E40P_MANIFEST) \
		$(XRUN_FILE_LIST) \
		$(UVM_PLUSARGS)


comp: mk_xrun_dir $(CV32E40P_PKG) $(OVP_MODEL_DPI)
	$(XRUN) \
		$(XRUN_COMP) \
		-elaborate
#		$(XRUN_VELABCOVERAGE)


XRUN_SIM_PREREQ = comp
XRUN_COMP_RUN = $(XRUN_RUN_FLAGS)

ifeq ($(XRUN_SINGLE_STEP), YES)
	XRUN_SIM_PREREQ = mk_xrun_dir $(CV32E40P_PKG) $(OVP_MODEL_DPI)
	XRUN_COMP_RUN = $(XRUN_COMP) $(XRUN_RUN_BASE_FLAGS)
endif

################################################################################
# Custom test-programs.  See comment in dsim.mk for more info
custom: $(XRUN_SIM_PREREQ) $(CUSTOM_DIR)/$(CUSTOM_PROG).hex
	$(XRUN) -l xrun-$(CUSTOM_PROG).log $(XRUN_COMP_RUN) \
		+elf_file=$(CUSTOM_DIR)/$(CUSTOM_PROG).elf \
		+nm_file=$(CUSTOM_DIR)/$(CUSTOM_PROG).nm \
		+UVM_TESTNAME=uvmt_cv32_firmware_test_c \
		+firmware=$(CUSTOM_DIR)/$(CUSTOM_PROG).hex


################################################################################
# Explicit target tests
hello-world:  $(XRUN_SIM_PREREQ) $(CUSTOM)/hello_world.hex
	$(XRUN) -l xrun-hello-world.log $(XRUN_COMP_RUN) \
		+elf_file=$(CUSTOM)/hello_world.elf \
		+nm_file=$(CUSTOM)/hello_world.nm \
		+UVM_TESTNAME=uvmt_cv32_firmware_test_c \
		+firmware=$(CUSTOM)/hello_world.hex
#		$(XRUN_VRUNCOVERAGE)

misalign: $(XRUN_SIM_PREREQ) $(CUSTOM)/misalign.hex
	$(XRUN) -l xrun-misalign.log $(XRUN_COMP_RUN) \
		+elf_file=$(CUSTOM)/misalign.elf \
		+nm_file=$(CUSTOM)/misalign.nm \
		+UVM_TESTNAME=uvmt_cv32_firmware_test_c \
		+firmware=$(CUSTOM)/misalign.hex

illegal: $(XRUN_SIM_PREREQ) $(CUSTOM)/illegal.hex
	$(XRUN) -l xrun-illegal.log $(XRUN_COMP_RUN) \
		+elf_file=$(CUSTOM)/illegal.elf \
		+nm_file=$(CUSTOM)/illegal.nm \
		+UVM_TESTNAME=uvmt_cv32_firmware_test_c \
		+firmware=$(CUSTOM)/illegal.hex

fibonacci: $(XRUN_SIM_PREREQ) $(CUSTOM)/fibonacci.hex
	$(XRUN) -l xrun-fibonacci.log $(XRUN_COMP_RUN) \
		+elf_file=$(CUSTOM)/fibonacci.elf \
		+nm_file=$(CUSTOM)/fibonacci.nm \
		+UVM_TESTNAME=uvmt_cv32_firmware_test_c \
		+firmware=$(CUSTOM)/fibonacci.hex

dhrystone: $(XRUN_SIM_PREREQ) $(CUSTOM)/dhrystone.hex
	$(XRUN) -l xrun-dhrystone.log $(XRUN_COMP_RUN) \
		+elf_file=$(CUSTOM)/dhrystone.elf \
		+nm_file=$(CUSTOM)/dhrystone.nm \
		+UVM_TESTNAME=uvmt_cv32_firmware_test_c \
		+firmware=$(CUSTOM)/dhrystone.hex

riscv_ebreak_test_0: $(XRUN_SIM_PREREQ) $(CUSTOM)/riscv_ebreak_test_0.hex
	$(XRUN) -l xrun-riscv_ebreak_test_0.log $(XRUN_COMP_RUN) \
                +elf_file=$(CUSTOM)/riscv_ebreak_test_0.elf \
                +nm_file=$(CUSTOM)/riscv_ebreak_test_0.nm \
                +UVM_TESTNAME=uvmt_cv32_firmware_test_c \
                +firmware=$(CUSTOM)/riscv_ebreak_test_0.hex

debug_test: $(XRUN_SIM_PREREQ) $(CORE_TEST_DIR)/debug_test/debug_test.hex
	$(XRUN) -l xrun-riscv_debug_test.log $(XRUN_COMP_RUN) \
                +elf_file=$(CORE_TEST_DIR)/debug_test/debug_test.elf \
                +nm_file=$(CORE_TEST_DIR)/debug_test/debug_test.nm \
                +UVM_TESTNAME=uvmt_cv32_firmware_test_c \
                +firmware=$(CORE_TEST_DIR)/debug_test/debug_test.hex


# Runs tests in cv32_riscv_tests/ only
cv32-riscv-tests: $(XRUN_SIM_PREREQ) $(CV32_RISCV_TESTS_FIRMWARE)/cv32_riscv_tests_firmware.hex
	$(XRUN) -l xrun-riscv-tests.log $(XRUN_COMP_RUN) \
		+elf_file=$(CV32_RISCV_TESTS_FIRMWARE)/cv32_riscv_tests_firmware.elf \
		+nm_file=$(CV32_RISCV_TESTS_FIRMWARE)/cv32_riscv_tests_firmware.nm \
		+UVM_TESTNAME=uvmt_cv32_firmware_test_c \
		+firmware=$(CV32_RISCV_TESTS_FIRMWARE)/cv32_riscv_tests_firmware.hex

# Runs tests in cv32_riscv_compliance_tests/ only
cv32-riscv-compliance-tests: $(XRUN_SIM_PREREQ)  $(CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE)/cv32_riscv_compliance_tests_firmware.hex
	$(XRUN) -l xrun-riscv_compliance_tests.log $(XRUN_RUN_FLAGS) \
		+elf_file=$(CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE)/cv32_riscv_compliance_tests_firmware.elf \
		+nm_file=$(CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE)/cv32_riscv_compliance_tests_firmware.nm \
		+UVM_TESTNAME=uvmt_cv32_firmware_test_c \
		+firmware=$(CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE)/cv32_riscv_compliance_tests_firmware.hex

unit-test:  firmware-unit-test-clean
unit-test:  $(FIRMWARE)/firmware_unit_test.hex
unit-test: ALL_VSIM_FLAGS += "+firmware=$(FIRMWARE)/firmware_unit_test.hex"
unit-test: dsim-firmware-unit-test


# Runs all tests in riscv_tests/ and riscv_compliance_tests/
cv32-firmware: comp $(FIRMWARE)/firmware.hex
	$(XRUN) -R -l xrun-firmware.log \
		+UVM_TESTNAME=uvmt_cv32_firmware_test_c \
		+firmware=$(FIRMWARE)/firmware.hex

# XRUN UNIT TESTS: run each test individually. See comment header for dsim-unit-test for more info.
# TODO: update ../Common.mk to create "xrun-firmware-unit-test" target.
# Example: to run the ADDI test `make xrun-unit-test addi`
#xrun-unit-test: comp
#	$(XRUN) -R -l xrun-$(UNIT_TEST).log \
#		+UVM_TESTNAME=uvmt_cv32_firmware_test_c \
#		+firmware=$(FIRMWARE)/firmware_unit_test.hex

###############################################################################
# Use Google instruction stream generator (RISCV-DV) to create new test-programs
comp_riscv-dv:
	$(XRUN) $(XRUN_COMP_FLAGS) \
		$(XRUN_USER_COMPILE_ARGS) \
		-elaborate \
		+incdir+$(RISCVDV_PKG)/target/rv32imc \
		+incdir+$(RISCVDV_PKG)/user_extension \
		+incdir+$(RISCVDV_PKG)/tests \
		+incdir+$(COREVDV_PKG) \
		-f $(COREVDV_PKG)/manifest.f \
		-l $(COREVDV_PKG)/out_$(DATE)/run/compile.log 

gen_riscv-dv:
	$(XRUN) $(XRUN_RUN_FLAGS) \
		-xceligen rand_struct \
		+UVM_TESTNAME=corev_instr_base_test  \
		+num_of_tests=2  \
		+start_idx=0  \
		+asm_file_name=$(CORE_TEST_DIR)/google-riscv-dv  \
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

corev-dv: clean_riscv-dv clone_riscv-dv comp_riscv-dv gen_riscv-dv

###############################################################################
# Clean up your mess!

clean:
	rm -vrf $(XRUN_DIR)
	if [ -e xrun.history ]; then rm xrun.history; fi
	if [ -e xrun.log ]; then rm xru*.log; fi
	if [ -e trace_core_00_0.log ]; then rm trace_core_*.log; fi
	if [ -e waves.shm ]; then rm -rf waves.shm; fi

# Files created by Eclipse when using the Imperas ISS + debugger
clean_eclipse:
	rm  -f eguieclipse.log
	rm  -f idebug.log
	rm  -f stdout.txt
	rm  -rf workspace

# All generated files plus the clone of the RTL
clean_all: clean clean_eclipse clean_core_tests clean_riscv-dv clean_test_programs
	rm -rf $(CV32E40P_PKG)

