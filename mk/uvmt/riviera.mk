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
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
#
###############################################################################
#
# Riviera-PRO-specific Makefile for the Core-V-Verif "uvmt" testbench.
# Riviera-PRO is the Aldec SystemVerilog simulator.
#
###############################################################################

# Executables
VLIB   					= vlib
VMAP 					= vmap
VLOG 					= $(CV_SIM_PREFIX) vlog
VSIM 					= $(CV_SIM_PREFIX) vsim
VWORK     				= work

# Paths
VSIM_RESULTS           ?= $(if $(CV_RESULTS),$(abspath $(CV_RESULTS))/riviera_results,$(MAKE_PATH)/riviera_results)
VSIM_COREVDV_RESULTS   ?= $(VSIM_RESULTS)/corev-dv
VSIM_COV_MERGE_DIR     ?= $(VSIM_RESULTS)/merged
UVM_HOME               ?= ${ALDEC_PATH}/vlib/uvm-1.2/src/
USES_DPI = 1

# Default flags
VLOG_COV                ?= -coverage sbecam
VSIM_USER_FLAGS         ?=
VSIM_COV 		?= -acdb -acdb_cov sbfectapm -acdb_file $(VSIM_TEST).acdb
VSIM_WAVES_ADV_DEBUG    ?=
VSIM_WAVES_DO           ?=

# Common QUIET flag defaults to -quiet unless VERBOSE is set
ifeq ($(call IS_YES,$(VERBOSE)),YES)
QUIET=
else
QUIET=-quiet
endif

ifeq ($(USES_DPI),1)
  DPILIB_VLOG_OPT =
  DPILIB_VSIM_OPT = -sv_lib "$(ALDEC_PATH)/bin/uvm_1_2_dpi"
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
				-timescale "1ns/1ps" \
				-err VCP2694 W1 #for riscv dv

VLOG_FILE_LIST = -f $(DV_UVMT_PATH)/uvmt_$(CV_CORE_LC).flist

VLOG_DEBUG_FLAGS ?= -dbg
VLOG_FLAGS += $(DPILIB_VLOG_OPT)

# Add the ISS to compilation
VLOG_FILE_LIST += -f $(DV_UVMT_PATH)/imperas_iss.flist
VLOG_FLAGS += "+define+$(CV_CORE_UC)_TRACE_EXECUTION"
VLOG_FLAGS += -dpilib

###############################################################################
# VSIM (Simulaion)
VSIM_FLAGS        += $(VSIM_USER_FLAGS) +access +r+w
VSIM_DEBUG_FLAGS  ?= -dbg
VSIM_GUI_FLAGS    ?= -gui
VSIM_SCRIPT_DIR	   = $(abspath $(MAKE_PATH)/../tools/riviera)

VSIM_UVM_ARGS      =

VSIM_FLAGS += -sv_lib $(basename $(OVP_MODEL_DPI))

ifeq ($(call IS_YES,$(USE_ISS)),YES)
VSIM_FLAGS += +USE_ISS
else
VSIM_FLAGS += +DISABLE_OVPSIM
endif

VSIM_FLAGS += -sv_lib $(basename $(DPI_DASM_LIB))
VSIM_FLAGS += -sv_lib $(basename $(abspath $(SVLIB_LIB)))

# Skip compile if requested (COMP=NO)
ifneq ($(call IS_NO,$(COMP)),NO)
VSIM_RUN_PREREQ = comp
endif

VSIM_PMA_INC += +incdir+$(TBSRC_HOME)/uvmt \
                +incdir+$(CV_CORE_PKG)/rtl/include \
                +incdir+$(CV_CORE_COREVDV_PKG)/ldgen \
                +incdir+$(abspath $(MAKE_PATH)/../../../lib/mem_region_gen)

################################################################################
# Coverage database generation
#TODO
ifeq ($(call IS_YES,$(COV)),YES)
VLOG_FLAGS  += $(VLOG_COV)
VSIM_FLAGS  += $(VSIM_COV)
endif

################################################################################
# Waveform generation
#TODO

################################################################################
# Interactive simulation
ifeq ($(call IS_YES,$(GUI)),YES)
VRUN_FLAGS += run -all
ifeq ($(call IS_YES,$(ADV_DEBUG)),YES)
VLOG_FLAGS += $(VLOG_DEBUG_FLAGS)
VSIM_FLAGS += $(VSIM_GUI_FLAGS) $(VSIM_DEBUG_FLAGS)
else
VSIM_FLAGS += $(VSIM_GUI_FLAGS)
endif
else
VSIM_FLAGS += -c
VRUN_FLAGS += run -all; endsim; quit -force
endif

################################################################################
# Coverage command
#TODO

################################################################################
# Waveform (post-process) command line
#TODO

################################################################################
# Targets

.PHONY: no_rule help mk_vsim_dir lib comp run

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
			$(VSIM_PMA_INC) \
			-uvmver 1.2 \
			+incdir+$(CV_CORE_COREVDV_PKG)/target/$(CV_CORE_LC) \
			+incdir+$(RISCVDV_PKG)/user_extension \
			+incdir+$(COREVDV_PKG) \
			+incdir+$(CV_CORE_COREVDV_PKG) \
			$(CFG_COMPILE_FLAGS) \
			-f $(CV_CORE_MANIFEST) \
			-f $(COREVDV_PKG)/manifest.f

gen_corev-dv:
	mkdir -p $(VSIM_COREVDV_RESULTS)/$(TEST)
	for (( idx=${GEN_START_INDEX}; idx < $$((${GEN_START_INDEX} + ${GEN_NUM_TESTS})); idx++ )); do \
		mkdir -p $(GEN_TEST_DIR)/test_build/$(CFG)/$$idx; \
	done
	cd  $(VSIM_COREVDV_RESULTS)/$(TEST) && \
		$(VSIM) \
			$(VSIM_FLAGS) \
			$(CV_CORE_LC)_instr_gen_tb_top \
			$(DPILIB_VSIM_OPT) \
			-lib $(VSIM_COREVDV_RESULTS)/work \
			+UVM_TESTNAME=$(GEN_UVM_TEST) \
			+num_of_tests=$(GEN_NUM_TESTS)  \
			-l $(TEST)_$(GEN_START_INDEX)_$(GEN_NUM_TESTS).log \
			+start_idx=$(GEN_START_INDEX) \
			+num_of_tests=$(GEN_NUM_TESTS) \
			+asm_file_name_opts=$(TEST) \
			+ldgen_cp_test_path=$(GEN_TEST_DIR)/test_build/$(CFG) \
			$(CFG_PLUSARGS) \
			$(GEN_PLUSARGS) \
			-do '$(VRUN_FLAGS)'
	# Copy out final assembler files to test directory
	for (( idx=${GEN_START_INDEX}; idx < $$((${GEN_START_INDEX} + ${GEN_NUM_TESTS})); idx++ )); do \
		cp -f ${BSP}/link_pma.ld ${GEN_TEST_DIR}/test_build/${CFG}/$$idx/link.ld; \
		cp ${VSIM_COREVDV_RESULTS}/${TEST}/${TEST}_$$idx.S ${GEN_TEST_DIR}/test_build/$(CFG)/$$idx; \
	done

comp_corev-dv: $(RISCVDV_PKG) $(CV_CORE_PKG) vlog_corev-dv

corev-dv: clean_riscv-dv \
	clone_riscv-dv \
	comp_corev-dv

################################################################################
# Riviera-PRO simulation targets

mk_vsim_dir:
	$(MKDIR_P) $(VSIM_RESULTS)

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

SIG_ROOT      ?= $(VSIM_RESULTS)/$(CFG)/$(RISCV_ISA)
SIG           ?= $(VSIM_RESULTS)/$(CFG)/$(RISCV_ISA)/$(COMPLIANCE_PROG)_$(RUN_INDEX)/$(COMPLIANCE_PROG).signature_output
REF           ?= $(COMPLIANCE_PKG)/riscv-test-suite/$(RISCV_ISA)/references/$(COMPLIANCE_PROG).reference_output
TEST_PLUSARGS ?= +signature=$(COMPLIANCE_PROG).signature_output

ifneq ($(call IS_NO,$(COMP)),NO)
VSIM_COMPLIANCE_PREREQ = build_compliance
endif

compliance: VSIM_TEST=$(COMPLIANCE_PROG)
compliance: OPT_SUBDIR=$(RISCV_ISA)
compliance: VSIM_FLAGS+=+firmware=$(COMPLIANCE_PKG)/work/$(RISCV_ISA)/$(COMPLIANCE_PROG).hex
compliance: VSIM_FLAGS+=+elf_file=$(COMPLIANCE_PKG)/work/$(RISCV_ISA)/$(COMPLIANCE_PROG).elf
compliance: TEST_UVM_TEST=uvmt_$(CV_CORE_LC)_firmware_test_c
compliance: $(VSIM_COMPLIANCE_PREREQ) run
compliance: export IMPERAS_TOOLS=$(CORE_V_VERIF)/$(CV_CORE_LC)/tests/cfg/ovpsim_no_pulp.ic

################################################################################
# If the configuration specified OVPSIM arguments, generate an ovpsim.ic file and
# set IMPERAS_TOOLS to point to it
gen_ovpsim_ic:
	@rm -f $(VSIM_RESULTS)/$(CFG)/$(TEST_NAME)_$(RUN_INDEX)/ovpsim.ic
	@mkdir -p $(VSIM_RESULTS)/$(CFG)/$(TEST_NAME)_$(RUN_INDEX)
	@touch $(VSIM_RESULTS)/$(CFG)/$(TEST_NAME)_$(RUN_INDEX)/ovpsim.ic
	@if [ ! -z "$(CFG_OVPSIM)" ]; then \
		echo "$(CFG_OVPSIM)" > $(VSIM_RESULTS)/$(CFG)/$(TEST_NAME)_$(RUN_INDEX)/ovpsim.ic; \
	fi
export IMPERAS_TOOLS=$(VSIM_RESULTS)/$(CFG)/$(TEST_NAME)_$(RUN_INDEX)/ovpsim.ic

# Target to create work directory in $(VSIM_RESULTS)/
lib: mk_vsim_dir $(CV_CORE_PKG) $(SVLIB_PKG) $(TBSRC_PKG) $(TBSRC)
	if [ ! -d "$(VSIM_RESULTS)/$(CFG)/$(VWORK)" ]; then \
		$(VLIB) "$(VSIM_RESULTS)/$(CFG)/$(VWORK)"; \
	fi

# Target to run vlog over SystemVerilog source in $(VSIM_RESULTS)/
comp: lib
	@echo "$(BANNER)"
	@echo "* Running vlog in $(VSIM_RESULTS)/$(CFG)"
	@echo "* Log: $(VSIM_RESULTS)/$(CFG)/vlog.log"
	@echo "$(BANNER)"
	cd $(VSIM_RESULTS)/$(CFG) && \
		$(VLOG) \
			$(VLOG_FLAGS) \
			$(CFG_COMPILE_FLAGS) \
			+incdir+$(DV_UVME_PATH) \
			+incdir+$(DV_UVMT_PATH) \
			-uvmver 1.2 \
			-f $(CV_CORE_MANIFEST) \
			$(VLOG_FILE_LIST) \
			$(TBSRC_PKG)

RUN_DIR = $(abspath $(VSIM_RESULTS)/$(CFG)/$(OPT_SUBDIR)/$(VSIM_TEST)_$(RUN_INDEX))

# Target to run VSIM (i.e. run the simulation)
run: $(VSIM_RUN_PREREQ) gen_ovpsim_ic
	@echo "$(BANNER)"
	@echo "* Running vsim in $(RUN_DIR)"
	@echo "* Log: $(RUN_DIR)/vsim-$(VSIM_TEST).log"
	@echo "$(BANNER)"
	mkdir -p $(RUN_DIR) && \
	cd $(RUN_DIR) && \
		$(VSIM) \
			$(VSIM_FLAGS) \
			${DPILIB_VSIM_OPT} \
			-l vsim-$(VSIM_TEST).log \
			-lib $(VSIM_RESULTS)/$(CFG)/work \
			+UVM_TESTNAME=$(TEST_UVM_TEST)\
			$(RTLSRC_VLOG_TB_TOP) \
			$(CFG_PLUSARGS) \
			$(TEST_PLUSARGS) \
			-do '$(VRUN_FLAGS)'

################################################################################
# Test targets

################################################################################
# The new general test target

test: VSIM_TEST=$(TEST_PROGRAM)
test: VSIM_FLAGS += +firmware=$(TEST_TEST_DIR)/test_build/$(CFG)/$(RUN_INDEX)/$(TEST_PROGRAM)$(OPT_RUN_INDEX_SUFFIX).hex
test: VSIM_FLAGS += +elf_file=$(TEST_TEST_DIR)/test_build/$(CFG)/$(RUN_INDEX)/$(TEST_PROGRAM)$(OPT_RUN_INDEX_SUFFIX).elf
test: VSIM_FLAGS += +itb_file=$(TEST_TEST_DIR)/test_build/$(CFG)/$(RUN_INDEX)/$(TEST_PROGRAM)$(OPT_RUN_INDEX_SUFFIX).itb
test: $(TEST_TEST_DIR)/test_build/$(CFG)/$(RUN_INDEX)/$(TEST_PROGRAM)$(OPT_RUN_INDEX_SUFFIX).hex run

################################################################################
# Invoke post-process waveform viewer
#TODO

################################################################################
# Invoke coverage
#TODO

###############################################################################
# Clean up your mess!

clean:
	rm -rf $(VSIM_RESULTS) library.cfg $(VWORK)

# All generated files plus the clone of the RTL
clean_all: clean clean_riscv-dv clean_test_programs clean-bsp clean_compliance clean_embench clean_dpi_dasm_spike clean_gen_linker_files clean_svlib
	rm -rf $(CV_CORE_PKG)
