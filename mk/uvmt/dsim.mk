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
# DSIM-specific Makefile.
# DSIM is the Metrics Technologies SystemVerilog simulator  (https://metrics.ca/)
#
###############################################################################

DSIM                    = dsim
DSIM_HOME              ?= /tools/Metrics/dsim
DSIM_CMP_FLAGS         ?= $(TIMESCALE) $(SV_CMP_FLAGS) -top uvmt_$(CV_CORE_LC)_tb
DSIM_ERR_SUPPRESS      ?= MultiBlockWrite:ReadingOutputModport
DSIM_UVM_ARGS          ?= +incdir+$(UVM_HOME)/src $(UVM_HOME)/src/uvm_pkg.sv
DSIM_WORK              ?= $(SIM_CFG_RESULTS)/dsim_work
DSIM_IMAGE             ?= dsim.out
DSIM_RUN_FLAGS         ?=
DSIM_CODE_COV_SCOPE    ?= $(MAKE_PATH)/../tools/dsim/ccov_scopes.txt
DSIM_USE_ISS           ?= YES

DSIM_FILE_LIST         ?= -f $(DV_UVMT_PATH)/uvmt_$(CV_CORE_LC).flist
DSIM_FILE_LIST         += -f $(DV_UVMT_PATH)/imperas_iss.flist
DSIM_COMPILE_ARGS      += +define+$(CV_CORE_UC)_TRACE_EXECUTION

DSIM_USER_COMPILE_ARGS ?=
ifeq ($(USE_ISS),YES)
	DSIM_RUN_FLAGS     += +USE_ISS
else
	DSIM_RUN_FLAGS     += +DISABLE_OVPSIM
endif
ifeq ($(call IS_YES,$(USE_RVVI)),YES)
    DSIM_RUN_FLAGS     += +USE_RVVI
endif
ifeq ($(call IS_YES,$(TEST_DISABLE_ALL_CSR_CHECKS)),YES)
	DSIM_RUN_FLAGS +="+DISABLE_ALL_CSR_CHECKS"
endif
ifneq ($(TEST_DISABLE_CSR_CHECK),)
	DSIM_RUN_FLAGS += +DISABLE_CSR_CHECK=$(TEST_DISABLE_CSR_CHECK)
endif

DSIM_PMA_INC += +incdir+$(TBSRC_HOME)/uvmt \
                +incdir+$(CV_CORE_PKG)/rtl/include \
                +incdir+$(CV_CORE_COREVDV_PKG)/ldgen \
				+incdir+$(abspath $(MAKE_PATH)/../../../lib/mem_region_gen)

# Seed management for constrained-random sims. This is an intentional repeat
# of the root Makefile: dsim regressions use random seeds by default.
DSIM_SEED    ?= random
DSIM_RNDSEED ?=

ifeq ($(DSIM_SEED),random)
DSIM_RNDSEED = $(shell date +%N)
else
ifeq ($(DSIM_SEED),)
# Empty DSIM_SEED variable selects a random value
DSIM_RNDSEED = 1
else
DSIM_RNDSEED = $(DSIM_SEED)
endif
endif

DSIM_RUN_FLAGS         += $(USER_RUN_FLAGS)
DSIM_RUN_FLAGS         += -sv_seed $(DSIM_RNDSEED)

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
DSIM_DMP_FILE  ?= dsim.vcd
DSIM_DMP_FLAGS ?= -waves $(DSIM_DMP_FILE)
endif

ifneq ($(CCOV), 0)
	DSIM_COMPILE_ARGS += -code-cov block -code-cov-scope-specs $(DSIM_CODE_COV_SCOPE)
	DSIM_RUN_FLAGS    += -code-cov block -code-cov-scope-specs $(DSIM_CODE_COV_SCOPE)
endif

# Special var to point to tool and installation dependent path of DPI headers.
# Used to recompile dpi_dasm_spike if needed (by default, not needed).
DPI_INCLUDE        ?= $(shell dirname $(shell which dsim))/../include

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
	$(MKDIR_P) $(SIM_CFG_RESULTS)
	$(MKDIR_P) $(DSIM_WORK)

################################################################################
# DSIM compile target
comp: mk_results $(CV_CORE_PKG) $(SVLIB_PKG) $(OVP_MODEL_DPI)
	$(DSIM) \
		$(DSIM_CMP_FLAGS) \
		-suppress $(DSIM_ERR_SUPPRESS) \
		$(DSIM_UVM_ARGS) \
		$(DSIM_ACC_FLAGS) \
		$(CFG_COMPILE_FLAGS) \
		$(DSIM_COMPILE_ARGS) \
		$(DSIM_USER_COMPILE_ARGS) \
		+incdir+$(DV_UVME_PATH) \
		+incdir+$(DV_UVMT_PATH) \
		-f $(CV_CORE_MANIFEST) \
		$(DSIM_FILE_LIST) \
		-work $(DSIM_WORK) \
		+$(UVM_PLUSARGS) \
		-genimage $(DSIM_IMAGE)


################################################################################
# General test execution target "test"
#

################################################################################
# If the configuration specified OVPSIM arguments, generate an ovpsim.ic file and
# set IMPERAS_TOOLS to point to it
gen_ovpsim_ic:
	@rm -f $(SIM_RUN_RESULTS)/ovpsim.ic
	@mkdir -p $(SIM_RUN_RESULTS)
	@touch $(SIM_RUN_RESULTS)/ovpsim.ic
	@if [ ! -z "$(CFG_OVPSIM)" ]; then \
		echo "$(CFG_OVPSIM)" > $(SIM_RUN_RESULTS)/ovpsim.ic; \
	fi
export IMPERAS_TOOLS=$(SIM_RUN_RESULTS)/ovpsim.ic

# Skip compile if COMP is specified and negative
ifneq ($(call IS_NO,$(COMP)),NO)
DSIM_SIM_PREREQ = comp
endif

test: $(DSIM_SIM_PREREQ) hex gen_ovpsim_ic
	mkdir -p $(SIM_RUN_RESULTS) && \
	cd $(SIM_RUN_RESULTS) && \
		$(DSIM) \
			-l dsim-$(TEST_NAME).log \
			-image $(DSIM_IMAGE) \
			-work $(DSIM_WORK) \
			$(DSIM_RUN_FLAGS) \
			$(DSIM_DMP_FLAGS) \
			$(CFG_PLUSARGS) \
			$(TEST_PLUSARGS) \
			-sv_lib $(UVM_HOME)/src/dpi/libuvm_dpi.so \
			-sv_lib $(DPI_DASM_LIB) \
			-sv_lib $(abspath $(SVLIB_LIB)) \
			-sv_lib $(OVP_MODEL_DPI) \
			+UVM_TESTNAME=$(TEST_UVM_TEST) \
			+firmware=$(SIM_TEST_PROGRAM_RESULTS)/$(TEST_PROGRAM)$(OPT_RUN_INDEX_SUFFIX).hex \
			+elf_file=$(SIM_TEST_PROGRAM_RESULTS)/$(TEST_PROGRAM)$(OPT_RUN_INDEX_SUFFIX).elf \
			+itb_file=$(SIM_TEST_PROGRAM_RESULTS)/$(TEST_PROGRAM)$(OPT_RUN_INDEX_SUFFIX).itb

# Similar to above, but for the ASM directory.
asm: comp $(ASM_DIR)/$(ASM_PROG).hex $(ASM_DIR)/$(ASM_PROG).elf
	mkdir -p $(SIM_RESULTS)/$(CFG)/$(ASM_PROG)_$(RUN_INDEX) && cd $(SIM_RESULTS)/$(CFG)/$(ASM_PROG)_$(RUN_INDEX)  && \
	$(DSIM) -l dsim-$(ASM_PROG).log -image $(DSIM_IMAGE) \
		-work $(DSIM_WORK) $(DSIM_RUN_FLAGS) $(DSIM_DMP_FLAGS) \
		-sv_lib $(UVM_HOME)/src/dpi/libuvm_dpi.so \
		-sv_lib $(DPI_DASM_LIB) \
		-sv_lib $(OVP_MODEL_DPI) \
		+UVM_TESTNAME=$(UVM_TESTNAME) \
		+firmware=$(ASM_DIR)/$(ASM_PROG).hex \
		+elf_file=$(ASM_DIR)/$(ASM_PROG).elf

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

SIG_ROOT      ?= $(SIM_RESULTS)/$(CFG)/$(RISCV_ISA)
SIG           ?= $(SIM_RESULTS)/$(CFG)/$(RISCV_ISA)/$(COMPLIANCE_PROG)/$(RUN_INDEX)/$(COMPLIANCE_PROG).signature_output
REF           ?= $(COMPLIANCE_PKG)/riscv-test-suite/$(RISCV_ISA)/references/$(COMPLIANCE_PROG).reference_output
TEST_PLUSARGS ?= +signature=$(COMPLIANCE_PROG).signature_output

compliance: comp build_compliance
	mkdir -p $(SIM_RESULTS)/$(CFG)/$(RISCV_ISA)/$(COMPLIANCE_PROG)/$(RUN_INDEX)
	cd $(SIM_RESULTS)/$(CFG)/$(RISCV_ISA)/$(COMPLIANCE_PROG)/$(RUN_INDEX) && \
	export IMPERAS_TOOLS=$(CORE_V_VERIF)/$(CV_CORE_LC)/tests/cfg/ovpsim_no_pulp.ic && \
	$(DSIM) -l dsim-$(COMPLIANCE_PROG).log -image $(DSIM_IMAGE) \
		-work $(DSIM_WORK) $(DSIM_RUN_FLAGS) $(DSIM_DMP_FLAGS) $(TEST_PLUSARGS) \
		-sv_lib $(UVM_HOME)/src/dpi/libuvm_dpi.so \
		-sv_lib $(DPI_DASM_LIB) \
		-sv_lib $(OVP_MODEL_DPI) \
		+UVM_TESTNAME=$(UVM_TESTNAME) \
		+firmware=$(COMPLIANCE_PKG)/work/$(RISCV_ISA)/$(COMPLIANCE_PROG).hex \
		+elf_file=$(COMPLIANCE_PKG)/work/$(RISCV_ISA)/$(COMPLIANCE_PROG).elf

################################################################################
# Commonly used targets:
#      Here for historical reasons - mostly (completely?) superceeded by the
#      custom target.
#

# Mythical no-test-program testcase.  Might never be used.  Not known tow work
no-test-program: comp
	mkdir -p $(SIM_RESULTS)/$(CFG)/hello-world_$(RUN_INDEX) && cd $(SIM_RESULTS)/$(CFG)/hello-world_$(RUN_INDEX)  && \
	$(DSIM) -l dsim-$(UVM_TESTNAME).log -image $(DSIM_IMAGE) \
		-work $(DSIM_WORK) $(DSIM_RUN_FLAGS) $(DSIM_DMP_FLAGS) \
		-sv_lib $(UVM_HOME)/src/dpi/libuvm_dpi.so \
		-sv_lib $(DPI_DASM_LIB) \
		-sv_lib $(OVP_MODEL_DPI) \
		+UVM_TESTNAME=$(UVM_TESTNAME)

################################################################################
# DSIM UNIT TESTS: run each test individually.
#                  Example: to run the ADDI test `make dsim-unit-test addi`
# DO NOT INVOKE rule "dsim-firmware-unit-test" directly.   It is a support
# rule for rule "dsim-unit-test" (in included ../Firmware.mk).
dsim-firmware-unit-test: comp
	mkdir -p $(SIM_RESULTS)/firmware_$(RUN_INDEX) && cd $(SIM_RESULTS)/firmware_$(RUN_INDEX) && \
	$(DSIM) -l dsim-$(UNIT_TEST).log -image $(DSIM_IMAGE) \
		-work $(DSIM_WORK) $(DSIM_RUN_FLAGS) $(DSIM_DMP_FLAGS) \
		-sv_lib $(UVM_HOME)/src/dpi/libuvm_dpi.so \
		-sv_lib $(DPI_DASM_LIB) \
		-sv_lib $(OVP_MODEL_DPI) \
		+UVM_TESTNAME=uvmt_$(CV_CORE_LC)_firmware_test_c \
		+firmware=$(FIRMWARE)/firmware_unit_test.hex \
		+elf_file=$(FIRMWARE)/firmware_unit_test.elf

# Aliases for 'dsim-unit-test' (defined in ../Common.mk)
.PHONY: unit-test
unit-test: dsim-unit-test

###############################################################################
# Use Google instruction stream generator (RISCV-DV) to create new test-programs
#riscv-dv: clone_riscv-dv
comp_corev-dv: $(CV_CORE_PKG)
	mkdir -p $(SIM_COREVDV_RESULTS)
	dsim -sv \
		-work $(SIM_COREVDV_RESULTS)/dsim \
		-genimage image \
		+incdir+$(UVM_HOME)/src \
		$(UVM_HOME)/src/uvm_pkg.sv \
		+define+DSIM \
		-top $(CV_CORE_LC)_instr_gen_tb_top \
		-suppress EnumMustBePositive \
		-suppress SliceOOB \
		-f $(CV_CORE_MANIFEST) \
		+incdir+$(CV_CORE_COREVDV_PKG)/target/$(CV_CORE_LC) \
		+incdir+$(RISCVDV_PKG)/user_extension \
		+incdir+$(COREVDV_PKG) \
		+incdir+$(CV_CORE_COREVDV_PKG) \
		$(DSIM_PMA_INC) \
		$(CFG_COMPILE_FLAGS) \
		-f $(COREVDV_PKG)/manifest.f \
		-l $(SIM_COREVDV_RESULTS)/compile.log

#riscv-test: riscv-dv
#		+asm_file_name=$(RISCVDV_PKG)/out_2020-06-24/asm_tests/riscv_arithmetic_basic_test  \

gen_corev-dv:
	mkdir -p $(SIM_COREVDV_RESULTS)/$(TEST)
	# Clean old assembler generated tests in results
	idx=$(GEN_START_INDEX); sum=$$(($(GEN_START_INDEX) + $(GEN_NUM_TESTS))); \
	while [ $$idx -lt $${sum} ]; do \
		mkdir -p $(SIM_CFG_RESULTS)/$(TEST)/$$idx/test_program; \
		echo "idx = $$idx"; \
		idx=$$((idx + 1)); \
	done
	cd  $(SIM_COREVDV_RESULTS)/$(TEST) && \
	dsim  -sv_seed $(DSIM_RNDSEED) \
		-sv_lib $(UVM_HOME)/src/dpi/libuvm_dpi.so \
		+acc+rwb \
		-image image \
		-work $(SIM_COREVDV_RESULTS)/dsim \
	 	+UVM_TESTNAME=$(GEN_UVM_TEST) \
		+num_of_tests=$(GEN_NUM_TESTS) \
		+start_idx=$(GEN_START_INDEX)  \
		+asm_file_name_opts=$(TEST) \
		+ldgen_cp_test_path=$(SIM_CFG_RESULTS)/$(TEST) \
		-l $(TEST)_$(GEN_START_INDEX)_$(GEN_NUM_TESTS).log \
		$(CFG_PLUSARGS) \
		$(GEN_PLUSARGS)
	# Copy out final assembler files to test directory
	idx=$(GEN_START_INDEX); sum=$$(($(GEN_START_INDEX) + $(GEN_NUM_TESTS))); \
	while [ $$idx -lt $${sum} ]; do \
		cp ${BSP}/link_corev-dv.ld ${SIM_TEST_RESULTS}/$$idx/test_program/link.ld; \
		cp ${SIM_COREVDV_RESULTS}/${TEST}/${TEST}_$$idx.S ${SIM_TEST_RESULTS}/$$idx/test_program; \
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
	rm -rf $(SIM_RESULTS)

# All generated files plus the clone of the RTL
clean_all: clean clean_riscv-dv clean_test_programs clean_bsp clean_compliance clean_embench clean_dpi_dasm_spike clean_svlib
	rm -rf $(CV_CORE_PKG)

