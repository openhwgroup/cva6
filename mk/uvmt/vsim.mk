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
# VSIM-specific Makefile for the Core-V-Verif "uvmt" testbench.
# VSIM is the Mentor Graphics Questa SystemVerilog simulator.
#
###############################################################################

# Executables
VLIB   					= vlib
VMAP 					= vmap
VLOG 					= $(CV_SIM_PREFIX) vlog
VOPT 					= $(CV_SIM_PREFIX) vopt
VSIM 					= $(CV_SIM_PREFIX) vsim
VISUALIZER				= $(CV_TOOL_PREFIX) visualizer
VCOVER                  = vcover

# Paths
VWORK     				= work
VSIM_COV_MERGE_DIR      = $(SIM_CFG_RESULTS)/$(CFG)/merged
UVM_HOME               ?= $(abspath $(shell which $(VLIB))/../../verilog_src/uvm-1.2/src)
USES_DPI = 1

# Special var to point to tool and installation dependent path of DPI headers.
# Used to recompile dpi_dasm_spike if needed (by default, not needed).
DPI_INCLUDE            ?= $(abspath $(shell which $(VLIB))/../../include)

# Default flags
VSIM_USER_FLAGS         ?=
VOPT_COV  				?= +cover=setf+$(RTLSRC_VLOG_TB_TOP).
VSIM_COV 				?= -coverage
VOPT_WAVES_ADV_DEBUG    ?= -designfile design.bin
VSIM_WAVES_ADV_DEBUG    ?= -qwavedb=+signal+assertion+ignoretxntime+msgmode=both
VSIM_WAVES_DO           ?= $(VSIM_SCRIPT_DIR)/waves.tcl

# Common QUIET flag defaults to -quiet unless VERBOSE is set
ifeq ($(call IS_YES,$(VERBOSE)),YES)
QUIET=
else
QUIET=-quiet
endif

ifeq ($(USES_DPI),1)
  DPILIB_VLOG_OPT =
  DPILIB_VSIM_OPT = -sv_lib $(UVM_HOME)/../../../uvm-1.2/linux_x86_64/uvm_dpi
  DPILIB_TARGET = dpi_lib$(BITS)
else
  DPILIB_VLOG_OPT = +define+UVM_NO_DPI
  DPILIB_VSIM_OPT =
  DPILIB_TARGET =
endif

LIBDIR  = $(UVM_HOME)/lib
LIBNAME = uvm_dpi

OPT_RV_ISA_DIR = $(if $(RISCV_ISA),/$(RISCV_ISA),)

###############################################################################
# LDGEN VLOG (Compilation)
VSIM_PMA_INC += +incdir+$(TBSRC_HOME)/uvmt \
                +incdir+$(CV_CORE_PKG)/rtl/include \
                +incdir+$(CV_CORE_COREVDV_PKG)/ldgen \
                +incdir+$(abspath $(MAKE_PATH)/../../../lib/mem_region_gen)

VLOG_LDGEN_FLAGS ?= \
                    -suppress 2577 \
                    -suppress 2583 \
                    -suppress 13185 \
                    -suppress 13314 \
                    -suppress 13288 \
                    -suppress 2181 \
                    -suppress 13262 \
                    -timescale "1ns/1ps" \
                    -sv \
                    -mfcu \
                    +acc=rb \
                    $(QUIET)

VOPT_LDGEN_FLAGS ?= \
                    -debugdb \
                    -fsmdebug \
                    -suppress 7034 \
                    +acc \
                    $(QUIET)

VSIM_LDGEN_FLAGS ?= \
                    -batch \
                    -do $(VSIM_SCRIPT_DIR)/vsim.tcl

###############################################################################
# VLOG (Compilation)
VLOG_FLAGS    ?= \
		-suppress 2577 \
		-suppress 2583 \
		-suppress 13185 \
		-suppress 13314 \
		-suppress 13288 \
		-suppress 2181 \
		-suppress 13262 \
		-suppress vlog-2745 \
		-timescale "1ns/1ps" \
		-sv \
		-64 \
		-mfcu \
		+acc=rb \
		$(QUIET) \
		-writetoplevels  uvmt_$(CV_CORE_LC)_tb

VLOG_FILE_LIST = -f $(DV_UVMT_PATH)/uvmt_$(CV_CORE_LC).flist

VLOG_FLAGS += $(DPILIB_VLOG_OPT)

# Add the ISS to compilation
VLOG_FILE_LIST += -f $(DV_UVMT_PATH)/imperas_iss.flist
VLOG_FLAGS += "+define+$(CV_CORE_UC)_TRACE_EXECUTION"
VLOG_FLAGS += "+define+UVM"

###############################################################################
# VOPT (Optimization)
VOPT_FLAGS    ?= \
                 -64 \
                 -debugdb \
                 -fsmdebug \
                 -suppress 7034 \
                 +acc \
                 $(QUIET)

###############################################################################
# VSIM (Simulaion)
VSIM_FLAGS        += $(VSIM_USER_FLAGS)
VSIM_FLAGS        += $(USER_RUN_FLAGS)
VSIM_FLAGS        += -sv_seed $(RNDSEED)
VSIM_FLAGS        += -64
VSIM_FLAGS        += -suppress 7031
VSIM_FLAGS        += -suppress 8858
VSIM_FLAGS        += -suppress 8522
VSIM_FLAGS        += -suppress 8550
VSIM_FLAGS        += -suppress 8549
VSIM_FLAGS        += -permit_unmatched_virtual_intf
VSIM_DEBUG_FLAGS  ?= -debugdb
VSIM_GUI_FLAGS    ?= -gui -debugdb
VSIM_SCRIPT_DIR	   = $(abspath $(MAKE_PATH)/../tools/vsim)

VSIM_UVM_ARGS      = +incdir+$(UVM_HOME)/src $(UVM_HOME)/src/uvm_pkg.sv

VSIM_FLAGS += -sv_lib $(basename $(OVP_MODEL_DPI))
ifeq ($(call IS_YES,$(USE_ISS)),YES)
VSIM_FLAGS += +USE_ISS
else
VSIM_FLAGS += +DISABLE_OVPSIM
endif
ifeq ($(call IS_YES,$(TEST_DISABLE_ALL_CSR_CHECKS)),YES)
VSIM_FLAGS +="+DISABLE_ALL_CSR_CHECKS"
endif
ifneq ($(TEST_DISABLE_CSR_CHECK),)
VSIM_FLAGS += +DISABLE_CSR_CHECK=$(TEST_DISABLE_CSR_CHECK)
endif

VSIM_FLAGS += -sv_lib $(basename $(DPI_DASM_LIB))
VSIM_FLAGS += -sv_lib $(basename $(abspath $(SVLIB_LIB)))

# Skip compile if requested (COMP=NO)
ifneq ($(call IS_NO,$(COMP)),NO)
VSIM_SIM_PREREQ = comp
endif

################################################################################
# Coverage database generation
ifeq ($(call IS_YES,$(COV)),YES)
VOPT_FLAGS  += $(VOPT_COV)
VSIM_FLAGS  += $(VSIM_COV)
VSIM_FLAGS  += -do 'set TEST ${VSIM_TEST}; source $(VSIM_SCRIPT_DIR)/cov.tcl'
endif

################################################################################
# Waveform generation
ifeq ($(call IS_YES,$(WAVES)),YES)
ifeq ($(call IS_YES,$(ADV_DEBUG)),YES)
VSIM_FLAGS += $(VSIM_WAVES_ADV_DEBUG)
else
VSIM_FLAGS += -do $(VSIM_WAVES_DO)
endif
endif

ifeq ($(call IS_YES,$(ADV_DEBUG)),YES)
VOPT_FLAGS += $(VOPT_WAVES_ADV_DEBUG)
endif

################################################################################
# Interactive simulation
ifeq ($(call IS_YES,$(GUI)),YES)
ifeq ($(call IS_YES,$(ADV_DEBUG)),YES)
VSIM_FLAGS += -visualizer=+designfile=../design.bin
else
VSIM_FLAGS += -gui
endif
VSIM_FLAGS += -do $(VSIM_SCRIPT_DIR)/gui.tcl
else
VSIM_FLAGS += -batch
VSIM_FLAGS += -do $(VSIM_SCRIPT_DIR)/vsim.tcl
endif

################################################################################
# Coverage command
COV_FLAGS =
COV_REPORT = cov_report
COV_MERGE_TARGET =
COV_MERGE_FIND = find $(SIM_CFG_RESULTS) -type f -name "*.ucdb" | grep -v merged.ucdb
COV_MERGE_FLAGS=merge -64 -out merged.ucdb -inputs ucdb.list

ifeq ($(call IS_YES,$(MERGE)),YES)
COV_DIR=$(VSIM_COV_MERGE_DIR)
COV_MERGE_TARGET=cov_merge
else
COV_DIR=$(SIM_RUN_RESULTS)

ifeq ($(call IS_YES,$(MERGE)),YES)
ifeq ($(call IS_YES,$(GUI)),YES)
# Merged coverage GUI
COV_FLAGS=-viewcov $(VSIM_COV_MERGE_DIR)/merged.ucdb
else
# Merged coverage report
COV_FLAGS=-c -viewcov $(VSIM_COV_MERGE_DIR)/merged.ucdb -do "file delete -force $(COV_REPORT); coverage report -html -details -precision 2 -annotate -output $(COV_REPORT); exit -f"
endif
else
ifeq ($(call IS_YES,$(GUI)),YES)
# Test coverage GUI
COV_FLAGS=-viewcov $(TEST).ucdb
else
# Test coverage report
COV_FLAGS=-c -viewcov $(TEST).ucdb -do "file delete -force $(COV_REPORT); coverage report -html -details -precision 2 -annotate -output $(COV_REPORT); exit -f"
endif
endif
endif

################################################################################
# Waveform (post-process) command line
ifeq ($(call IS_YES,$(ADV_DEBUG)),YES)
WAVES_CMD = \
	cd $(SIM_RUN_RESULTS) && \
		$(VISUALIZER) \
			-designfile $(SIM_CFG_RESULTS)/design.bin \
			-wavefile qwave.db
else
WAVES_CMD = \
	cd $(SIM_RUN_RESULTS) && \
		$(VSIM) \
			-gui \
			-view vsim.wlf
endif

# Compute vsim (run) prereqs, by default do a full compile + run when running
# a test, set COMP=NO to skip vlib-vlog-vopt and just run vsim
ifneq ($(call IS_NO,$(COMP)),NO)
VSIM_RUN_PREREQ = opt
endif

################################################################################
# Targets

.PHONY: no_rule help mk_vsim_dir lib comp opt run

no_rule:
	@echo 'makefile: SIMULATOR is set to $(SIMULATOR), but no rule/target specified.'
	@echo 'try "make SIMULATOR=vsim sanity" (or just "make sanity" if shell ENV variable SIMULATOR is already set).'

help:
	vsim -help

################################################################################
# ldgen generation targets
vlog_ldgen: $(CV_CORE_PKG) $(SVLIB_PKG)
	@echo "$(BANNER)"
	@echo "* Generating linker scripts in $(SIM_LDGEN_RESULTS)"
	@echo "$(BANNER)"
	$(MKDIR_P) $(SIM_LDGEN_RESULTS)
	if [ ! -d "$(SIM_LDGEN_RESULTS)/$(VWORK)" ]; then \
		$(VLIB) $(SIM_LDGEN_RESULTS)/$(VWORK); \
	fi

	cd $(SIM_LDGEN_RESULTS) && \
		$(VLOG) \
			$(VLOG_LDGEN_FLAGS) \
			$(VSIM_PMA_INC) \
			$(CFG_COMPILE_FLAGS) \
			$(TBSRC_HOME)/ldgen/ldgen_tb.sv \
			-l vlog-ldgen.log

vopt_ldgen:
	cd $(SIM_LDGEN_RESULTS) && \
		$(VOPT) \
			$(VOPT_LDGEN_FLAGS) \
			-work $(VWORK) \
			ldgen_tb \
			-o ldgen_tb_vopt \
			-l vopt-ldgen.log

vsim_ldgen:
	cd $(SIM_LDGEN_RESULTS) && \
		$(VSIM) \
			$(VSIM_LDGEN_FLAGS) \
			-work $(VWORK) \
			$(CFG_PLUSARGS) \
			+ldgen_cp_test_path=$(SIM_LDGEN_RESULTS) \
			ldgen_tb_vopt \
			-l vsim-ldgen.log

ldgen: vlog_ldgen vopt_ldgen vsim_ldgen

################################################################################
# corev-dv generation targets

vlog_corev-dv:
	$(MKDIR_P) $(SIM_COREVDV_RESULTS)
	$(MKDIR_P) $(COREVDV_PKG)/out_$(DATE)/run
	cd $(SIM_COREVDV_RESULTS) && \
		$(VLIB) $(VWORK)
	cd $(SIM_COREVDV_RESULTS) && \
		$(VLOG) \
			$(VLOG_FLAGS) \
			+incdir+$(UVM_HOME) \
			$(VSIM_PMA_INC) \
			$(UVM_HOME)/uvm_pkg.sv \
			+incdir+$(CV_CORE_COREVDV_PKG)/target/$(CV_CORE_LC) \
			+incdir+$(RISCVDV_PKG)/user_extension \
			+incdir+$(COREVDV_PKG) \
			+incdir+$(CV_CORE_COREVDV_PKG) \
			$(CFG_COMPILE_FLAGS) \
			-f $(CV_CORE_MANIFEST) \
			-f $(COREVDV_PKG)/manifest.f \
			$(CFG_PLUSARGS) \
			-l vlog.log

vopt_corev-dv:
	cd $(SIM_COREVDV_RESULTS) && \
		$(VOPT) \
			-work $(VWORK) \
			$(VOPT_FLAGS) \
			$(CV_CORE_LC)_instr_gen_tb_top \
			-o $(CV_CORE_LC)_instr_gen_tb_top_vopt \
			-l vopt.log

gen_corev-dv:
	mkdir -p $(SIM_COREVDV_RESULTS)/$(TEST)
	for (( idx=${GEN_START_INDEX}; idx < $$((${GEN_START_INDEX} + ${GEN_NUM_TESTS})); idx++ )); do \
		mkdir -p $(SIM_TEST_RESULTS)/$$idx/test_program; \
	done
	cd $(SIM_COREVDV_RESULTS)/$(TEST) && \
		$(VMAP) work ../work
	cd  $(SIM_COREVDV_RESULTS)/$(TEST) && \
		$(VSIM) \
			$(VSIM_FLAGS) \
			$(CV_CORE_LC)_instr_gen_tb_top_vopt \
			$(DPILIB_VSIM_OPT) \
			+UVM_TESTNAME=$(GEN_UVM_TEST) \
			+num_of_tests=$(GEN_NUM_TESTS)  \
			-l $(TEST)_$(GEN_START_INDEX)_$(GEN_NUM_TESTS).log \
			+start_idx=$(GEN_START_INDEX) \
			+num_of_tests=$(GEN_NUM_TESTS) \
			+UVM_TESTNAME=$(GEN_UVM_TEST) \
			+asm_file_name_opts=$(TEST) \
			+ldgen_cp_test_path=$(SIM_TEST_RESULTS) \
			$(CFG_PLUSARGS) \
			$(GEN_PLUSARGS)

	# Copy out final assembler files to test directory
	for (( idx=${GEN_START_INDEX}; idx < $$((${GEN_START_INDEX} + ${GEN_NUM_TESTS})); idx++ )); do \
		cp -f ${BSP}/link_corev-dv.ld ${SIM_TEST_RESULTS}/$$idx/test_program/link.ld; \
		cp ${SIM_COREVDV_RESULTS}/${TEST}/${TEST}_$$idx.S ${SIM_TEST_RESULTS}/$$idx/test_program; \
	done

comp_corev-dv: $(RISCVDV_PKG) $(CV_CORE_PKG) vlog_corev-dv vopt_corev-dv

corev-dv: clean_riscv-dv clone_riscv-dv comp_corev-dv

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

SIG_ROOT          ?= $(SIM_CFG_RESULTS)/$(RISCV_ISA)
SIG               ?= $(SIM_CFG_RESULTS)/$(RISCV_ISA)/$(COMPLIANCE_PROG)/$(RUN_INDEX)/$(COMPLIANCE_PROG).signature_output
REF               ?= $(COMPLIANCE_PKG)/riscv-test-suite/$(RISCV_ISA)/references/$(COMPLIANCE_PROG).reference_output
COMPLIANCE_RUN_DIR = $(SIM_CFG_RESULTS)/$(RISCV_ISA)/$(COMPLIANCE_PROG)/$(RUN_INDEX)
TEST_PLUSARGS     ?= +signature=$(COMPLIANCE_PROG).signature_output

ifneq ($(call IS_NO,$(COMP)),NO)
VSIM_COMPLIANCE_PREREQ = build_compliance
endif

# Target to run VSIM (i.e. run the simulation)
compliance: $(VSIM_COMPLIANCE_PREREQ) $(VSIM_RUN_PREREQ) gen_ovpsim_ic
	@echo "$(BANNER)"
	@echo "* Running vsim in $(COMPLIANCE_RUN_DIR)"
	@echo "* Log: $(COMPLIANCE_RUN_DIR)/vsim-$(COMPLIANCE_PROG).log"
	@echo "$(BANNER)"
	mkdir -p $(COMPLIANCE_RUN_DIR) && \
	cd $(COMPLIANCE_RUN_DIR) && \
		$(VMAP) work $(SIM_CFG_RESULTS)/work
	cd $(COMPLIANCE_RUN_DIR) && \
		$(VSIM) \
			-work $(VWORK) \
			$(VSIM_FLAGS) \
			-l vsim-$(COMPLIANCE_PROG).log \
			$(DPILIB_VSIM_OPT) \
			+UVM_TESTNAME=uvmt_$(CV_CORE_LC)_firmware_test_c \
			$(RTLSRC_VOPT_TB_TOP) \
			$(CFG_PLUSARGS) \
			$(TEST_PLUSARGS) \
			+firmware=$(COMPLIANCE_PKG)/work/$(RISCV_ISA)/$(COMPLIANCE_PROG).hex \
			+elf_file=$(COMPLIANCE_PKG)/work/$(RISCV_ISA)/$(COMPLIANCE_PROG).elf

compliance: export IMPERAS_TOOLS=$(CORE_V_VERIF)/$(CV_CORE_LC)/tests/cfg/ovpsim_no_pulp.ic

################################################################################
# Questa simulation targets

mk_vsim_dir:
	$(MKDIR_P) $(SIM_CFG_RESULTS)

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

# Target to create work directory in $(VSIM_RESULTS)/
lib: mk_vsim_dir $(CV_CORE_PKG) $(SVLIB_PKG) $(TBSRC_PKG) $(TBSRC)
	if [ ! -d "$(SIM_CFG_RESULTS)/$(VWORK)" ]; then \
		$(VLIB) $(SIM_CFG_RESULTS)/$(VWORK); \
	fi

# Target to run vlog over SystemVerilog source in $(VSIM_RESULTS)/
vlog: lib
	@echo "$(BANNER)"
	@echo "* Running vlog in $(SIM_CFG_RESULTS)"
	@echo "* Log: $(SIM_CFG_RESULTS)/vlog.log"
	@echo "$(BANNER)"
	cd $(SIM_CFG_RESULTS) && \
		$(VLOG) \
			-work $(VWORK) \
			-l vlog.log \
			$(VLOG_FLAGS) \
			$(CFG_COMPILE_FLAGS) \
			+incdir+$(DV_UVME_PATH) \
			+incdir+$(DV_UVMT_PATH) \
			+incdir+$(UVM_HOME) \
			$(UVM_HOME)/uvm_pkg.sv \
			-f $(CV_CORE_MANIFEST) \
			$(VLOG_FILE_LIST) \
			$(TBSRC_PKG)

# Target to run vopt over compiled code in $(VSIM_RESULTS)/
opt: vlog
	@echo "$(BANNER)"
	@echo "* Running vopt in $(SIM_CFG_RESULTS)"
	@echo "* Log: $(SIM_CFG_RESULTS)/vopt.log"
	@echo "$(BANNER)"
	cd $(SIM_CFG_RESULTS) && \
		$(VOPT) \
			-work $(VWORK) \
			-l vopt.log \
			$(VOPT_FLAGS) \
			$(RTLSRC_VLOG_TB_TOP) \
			-o $(RTLSRC_VOPT_TB_TOP)

comp: opt

RUN_DIR = $(abspath $(SIM_RUN_RESULTS))

# Target to run VSIM (i.e. run the simulation)
run: $(VSIM_RUN_PREREQ) gen_ovpsim_ic
	@echo "$(BANNER)"
	@echo "* Running vsim in $(RUN_DIR)"
	@echo "* Log: $(RUN_DIR)/vsim-$(VSIM_TEST).log"
	@echo "$(BANNER)"
	mkdir -p $(RUN_DIR) && \
	cd $(RUN_DIR) && \
		$(VMAP) work $(SIM_CFG_RESULTS)/work
	cd $(RUN_DIR) && \
		$(VSIM) \
			-work $(VWORK) \
			$(VSIM_FLAGS) \
			-l vsim-$(VSIM_TEST).log \
			$(DPILIB_VSIM_OPT) \
			+UVM_TESTNAME=$(TEST_UVM_TEST) \
			$(RTLSRC_VOPT_TB_TOP) \
			$(CFG_PLUSARGS) \
			$(TEST_PLUSARGS)

################################################################################
# Test targets

################################################################################
# The new general test target

test: VSIM_TEST=$(TEST_PROGRAM)
test: VSIM_FLAGS += +firmware=$(SIM_TEST_PROGRAM_RESULTS)/$(TEST_PROGRAM)$(OPT_RUN_INDEX_SUFFIX).hex
test: VSIM_FLAGS += +elf_file=$(SIM_TEST_PROGRAM_RESULTS)/$(TEST_PROGRAM)$(OPT_RUN_INDEX_SUFFIX).elf
test: VSIM_FLAGS += +itb_file=$(SIM_TEST_PROGRAM_RESULTS)/$(TEST_PROGRAM)$(OPT_RUN_INDEX_SUFFIX).itb
test: hex run

################################################################################
# Invoke post-process waveform viewer
waves:
	@if [ -z "$(TEST)" ]; then \
		echo "Error: TEST variable must be defined"; \
		exit 2; \
	fi
	$(WAVES_CMD)

################################################################################
# Invoke coverage
cov_merge:
	$(MKDIR_P) $(VSIM_COV_MERGE_DIR)
	cd $(VSIM_COV_MERGE_DIR) && \
		$(COV_MERGE_FIND) > $(VSIM_COV_MERGE_DIR)/ucdb.list
	cd $(VSIM_COV_MERGE_DIR) && \
		$(VCOVER) \
			$(COV_MERGE_FLAGS)
cov: $(COV_MERGE_TARGET)
	cd $(COV_DIR) && \
		$(VSIM) \
			$(COV_FLAGS)

###############################################################################
# Clean up your mess!

clean:
	rm -rf $(SIM_RESULTS)

# All generated files plus the clone of the RTL
clean_all: clean clean_riscv-dv clean_test_programs clean_bsp clean_compliance clean_embench clean_dpi_dasm_spike clean_svlib
	rm -rf $(CV_CORE_PKG)
