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
# VSIM-specific Makefile for the CV32E40P "uvmt_cv32" testbench.
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
VSIM_RESULTS           ?= $(MAKE_PATH)/vsim_results
VSIM_RISCVDV_RESULTS   ?= $(VSIM_RESULTS)/riscv-dv
VSIM_COV_MERGE_DIR     ?= $(VSIM_RESULTS)/merged
UVM_HOME               ?= $(abspath $(shell which $(VLIB))/../../verilog_src/uvm-1.2/src)
USES_DPI = 1

# Default flags
VSIM_USER_FLAGS         ?=
VOPT_COV  				?= +cover=setf+$(RTLSRC_VLOG_TB_TOP).
VSIM_COV 				?= -coverage
VOPT_WAVES_ADV_DEBUG    ?= -designfile design.bin
VSIM_WAVES_ADV_DEBUG    ?= -qwavedb=+signal+assertion+ignoretxntime+msgmode=both
VSIM_WAVES_DO           ?= $(VSIM_SCRIPT_DIR)/waves.tcl
NUM_TESTS               ?= 2

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

###############################################################################
# VLOG (Compilation)
VLOG_FLAGS    ?= \
				-suppress 2577 \
				-suppress 2583 \
				-suppress 13314 \
				-suppress 13288 \
        		-suppress 2181 \
				-suppress 13262 \
				-timescale "1ns/1ps" \
				-sv \
        		-mfcu \
        		+acc=rb \
				$(QUIET) \
        		-writetoplevels  uvmt_cv32_tb
VLOG_FILE_LIST = -f $(DV_UVMT_CV32_PATH)/uvmt_cv32.flist

VLOG_FLAGS += $(DPILIB_VLOG_OPT)

# Add the ISS to compilation
ifeq ($(call IS_YES,$(USE_ISS)),YES)
VLOG_FILE_LIST += -f $(DV_UVMT_CV32_PATH)/imperas_iss.flist
VLOG_FLAGS += "+define+ISS+CV32E40P_TRACE_EXECUTION"
endif

###############################################################################
# VOPT (Optimization)
VOPT_FLAGS    ?= -debugdb \
				 -fsmdebug \
				 -suppress 7034 \
				 +acc \
				 $(QUIET)

###############################################################################
# VSIM (Simulaion)
VSIM_FLAGS        += $(VSIM_USER_FLAGS)
VSIM_FLAGS        += $(USER_RUN_FLAGS)
VSIM_FLAGS        += -sv_seed $(RNDSEED)
VSIM_DEBUG_FLAGS  ?= -debugdb
VSIM_GUI_FLAGS    ?= -gui -debugdb
VSIM_SCRIPT_DIR	   = $(abspath $(MAKE_PATH)/../tools/vsim)

VSIM_UVM_ARGS      = +incdir+$(UVM_HOME)/src $(UVM_HOME)/src/uvm_pkg.sv

ifeq ($(call IS_YES,$(USE_ISS)),YES)
VSIM_FLAGS += +USE_ISS
VSIM_FLAGS += -sv_lib $(DV_OVPM_MODEL)/bin/Linux64/riscv_CV32E40P.dpi
endif

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
COV_MERGE_FIND = find $(VSIM_RESULTS) -type f -name "*.ucdb" | grep -v merged.ucdb > $(VSIM_COV_MERGE_DIR)/ucdb.list
COV_MERGE_FLAGS=merge -64 -out merged.ucdb -inputs ucdb.list

ifeq ($(call IS_YES,$(MERGE)),YES)
COV_DIR=$(VSIM_RESULTS)/$(COV_MERGE_DIR)
COV_MERGE_TARGET=cov_merge
else
COV_DIR=$(VSIM_RESULTS)/$(TEST)
endif

ifeq ($(call IS_YES,$(MERGE)),YES)
ifeq ($(call IS_YES,$(GUI)),YES)
# Merged coverage GUI
COV_FLAGS=-viewcov merged.ucdb
else
# Merged coverage report
COV_FLAGS=-c -viewcov merged.ucdb -do "file delete -force $(COV_REPORT); coverage report -html -details -precision 2 -annotate -output $(COV_REPORT); exit -f"
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

################################################################################
# Waveform (post-process) command line
ifeq ($(call IS_YES,$(ADV_DEBUG)),YES)
WAVES_CMD = \
	cd $(VSIM_RESULTS)/$(TEST) && \
		$(VISUALIZER) \
			-designfile ../design.bin \
			-wavefile qwave.db
else
WAVES_CMD = \
	cd $(VSIM_RESULTS)/$(TEST) && \
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
# riscv-dv generation targets

vlog_riscv-dv:
	$(MKDIR_P) $(VSIM_RISCVDV_RESULTS)
	$(MKDIR_P) $(COREVDV_PKG)/out_$(DATE)/run
	cd $(VSIM_RISCVDV_RESULTS) && \
		$(VLIB) $(VWORK)
	cd $(VSIM_RISCVDV_RESULTS) && \
		$(VLOG) \
			$(VLOG_FLAGS) \
			+incdir+$(UVM_HOME) \
			$(UVM_HOME)/uvm_pkg.sv \
			+incdir+$(COREVDV_PKG)/target/cv32e40p \
			+incdir+$(RISCVDV_PKG)/user_extension \
			+incdir+$(RISCVDV_PKG)/tests \
			+incdir+$(COREVDV_PKG) \
			-f $(COREVDV_PKG)/manifest.f \
			-l $(COREVDV_PKG)/out_$(DATE)/run/vlog.log

vopt-riscv-dv:
	cd $(VSIM_RISCVDV_RESULTS) && \
		$(VOPT) \
			-work $(VWORK) \
			$(VOPT_FLAGS) \
			corev_instr_gen_tb_top \
			-o corev_instr_gen_tb_top_vopt \
			-l $(COREVDV_PKG)/out_$(DATE)/run/vopt.log

comp_riscv-dv: vlog_riscv-dv vopt-riscv-dv

gen_corev_arithmetic_base_test:
	mkdir -p $(VSIM_RISCVDV_RESULTS)/corev_arithmetic_base_test	
	cd $(VSIM_RISCVDV_RESULTS)/corev_arithmetic_base_test && \
		$(VMAP) work ../work
	cd $(VSIM_RISCVDV_RESULTS)/corev_arithmetic_base_test && \
		$(VSIM) $(VSIM_FLAGS) \
			corev_instr_gen_tb_top_vopt \
			$(DPILIB_VSIM_OPT) \
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
	cp $(VSIM_RISCVDV_RESULTS)/corev_arithmetic_base_test/*.S $(CORE_TEST_DIR)/custom

gen_corev_rand_instr_test:
	mkdir -p $(VSIM_RISCVDV_RESULTS)/corev_rand_instr_test	
	cd $(VSIM_RISCVDV_RESULTS)/corev_rand_instr_test && \
		$(VMAP) work ../work
	cd $(VSIM_RISCVDV_RESULTS)/corev_rand_instr_test && \
		$(VSIM) $(VSIM_FLAGS) \
			corev_instr_gen_tb_top_vopt \
			$(DPILIB_VSIM_OPT) \
			+UVM_TESTNAME=corev_instr_base_test  \
			+num_of_tests=2  \
			+start_idx=0  \
			+asm_file_name_opts=corev_rand_instr_test  \
			-l $(COREVDV_PKG)/out_$(DATE)/sim_corev_rand_instr_test_0.log \
			+instr_cnt=10000 \
			+num_of_sub_program=0 \
			+directed_instr_0=riscv_int_numeric_corner_stream,4 \
			+no_fence=1 \
			+no_data_page=1 \
			+no_branch_jump=1 \
			+boot_mode=m \
			+no_csr_instr=1
	cp $(VSIM_RISCVDV_RESULTS)/corev_rand_instr_test/*.S $(CORE_TEST_DIR)/custom

gen_corev_rand_interrupt_test:
	mkdir -p $(VSIM_RISCVDV_RESULTS)/corev_rand_interrupt_test	
	cd $(VSIM_RISCVDV_RESULTS)/corev_rand_interrupt_test && \
		$(VMAP) work ../work
	cd $(VSIM_RISCVDV_RESULTS)/corev_rand_interrupt_test && \
		$(VSIM) $(VSIM_FLAGS) \
			corev_instr_gen_tb_top_vopt \
			$(DPILIB_VSIM_OPT) \
			+UVM_TESTNAME=corev_instr_base_test  \
			+num_of_tests=$(NUM_TESTS)  \
			+start_idx=0  \
			+asm_file_name_opts=corev_rand_interrupt_test  \
			-l $(COREVDV_PKG)/out_$(DATE)/sim_corev_rand_interrupt_test_0.log \
			+instr_cnt=50000 \
			+num_of_sub_program=5 \
            +directed_instr_0=riscv_load_store_rand_instr_stream,4 \
            +directed_instr_1=riscv_loop_instr,4 \
            +directed_instr_2=riscv_hazard_instr_stream,4 \
            +directed_instr_3=riscv_load_store_hazard_instr_stream,4 \
            +directed_instr_4=riscv_multi_page_load_store_instr_stream,4 \
            +directed_instr_5=riscv_mem_region_stress_test,4 \
            +directed_instr_6=riscv_jal_instr,4 \
			+no_fence=1 \
            +enable_interrupt=1 \
            +randomize_csr=1 \
			+boot_mode=m \
			+no_csr_instr=1
	cp $(VSIM_RISCVDV_RESULTS)/corev_rand_interrupt_test/*.S $(CORE_TEST_DIR)/custom

comp_corev-dv: clean_riscv-dv \
	clone_riscv-dv \
	comp_riscv-dv 

corev-dv: comp_corev-dv \
	gen_corev_arithmetic_base_test \
	gen_corev_rand_instr_test

################################################################################
# Questa simulation targets

mk_vsim_dir: 
	$(MKDIR_P) $(VSIM_RESULTS)

# Target to create work directory in $(VSIM_RESULTS)/
lib: mk_vsim_dir $(CV32E40P_PKG) $(TBSRC_PKG) $(TBSRC)
	if [ ! -d "$(VSIM_RESULTS)/$(VWORK)" ]; then \
		$(VLIB) $(VSIM_RESULTS)/$(VWORK); \
	fi

# Target to run vlog over SystemVerilog source in $(VSIM_RESULTS)/
comp: lib
	@echo "$(BANNER)"
	@echo "* Running vlog in $(VSIM_RESULTS)"
	@echo "* Log: $(VSIM_RESULTS)/vlog.log"
	@echo "$(BANNER)"
	cd $(VSIM_RESULTS) && \
		$(VLOG) \
			-work $(VWORK) \
			-l vlog.log \
			$(VLOG_FLAGS) \
			+incdir+$(DV_UVME_CV32_PATH) \
			+incdir+$(DV_UVMT_CV32_PATH) \
			+incdir+$(UVM_HOME) \
			$(UVM_HOME)/uvm_pkg.sv \
			-f $(CV32E40P_MANIFEST) \
			$(VLOG_FILE_LIST) \
			$(TBSRC_PKG)

# Target to run vopt over compiled code in $(VSIM_RESULTS)/
opt: comp
	@echo "$(BANNER)"
	@echo "* Running vopt in $(VSIM_RESULTS)"
	@echo "* Log: $(VSIM_RESULTS)/vopt.log"
	@echo "$(BANNER)"
	cd $(VSIM_RESULTS) && \
		$(VOPT) \
			-work $(VWORK) \
			-l vopt.log \
			$(VOPT_FLAGS) \
			$(RTLSRC_VLOG_TB_TOP) \
			-o $(RTLSRC_VOPT_TB_TOP)

# Target to run VSIM (i.e. run the simulation)
run: $(VSIM_RUN_PREREQ)
	@echo "$(BANNER)"
	@echo "* Running vsim in $(VSIM_RESULTS)/$(VSIM_TEST)"
	@echo "* Log: $(VSIM_RESULTS)/$(VSIM_TEST)/vsim-$(VSIM_TEST).log"
	@echo "$(BANNER)"
	mkdir -p $(VSIM_RESULTS)/$(VSIM_TEST) && \
	cd $(VSIM_RESULTS)/$(VSIM_TEST) && \
		$(VMAP) work ../work
	cd $(VSIM_RESULTS)/$(VSIM_TEST) && \
		$(VSIM) \
			-work $(VWORK) \
			$(VSIM_FLAGS) \
			-l vsim-$(VSIM_TEST).log \
			$(DPILIB_VSIM_OPT) \
			+UVM_TESTNAME=uvmt_cv32_firmware_test_c \
			$(RTLSRC_VOPT_TB_TOP)

################################################################################
# Test targets

.PHONY: hello-world

hello-world: VSIM_TEST=hello-world
hello-world: VSIM_FLAGS += +firmware=$(CUSTOM)/hello_world.hex +elf_file=$(CUSTOM)/hello_world.elf
hello-world: $(CUSTOM)/hello_world.hex run

interrupt_test: VSIM_TEST=interrupt_test
interrupt_test: VSIM_FLAGS += +firmware=$(CORE_TEST_DIR)/interrupt_test/interrupt_test.hex +elf_file=$(CORE_TEST_DIR)/interrupt_test/interrupt_test.elf
interrupt_test: $(CORE_TEST_DIR)/interrupt_test/interrupt_test.hex run

misalign: VSIM_TEST=misalign
misalign: VSIM_FLAGS += +firmware=$(CUSTOM)/misalign.hex +elf_file=$(CUSTOM)/misalign.elf
misalign: $(CUSTOM)/misalign.hex run

fibonacci: VSIM_TEST=fibonacci
fibonacci: VSIM_FLAGS += +firmware=$(CUSTOM)/fibonacci.hex +elf_file=$(CUSTOM)/fibonacci.elf
fibonacci: $(CUSTOM)/fibonacci.hex run

dhrystone: VSIM_TEST=dhrystone
dhrystone: VSIM_FLAGS += +firmware=$(CUSTOM)/dhrystone.hex +elf_file=$(CUSTOM)/dhrystone.elf
dhrystone: $(CUSTOM)/dhrystone.hex run

custom: VSIM_TEST=$(CUSTOM_PROG)
custom: VSIM_FLAGS += +firmware=$(CUSTOM_DIR)/$(CUSTOM_PROG).hex +elf_file=$(CUSTOM_DIR)/$(CUSTOM_PROG).elf
custom: $(CUSTOM_DIR)/$(CUSTOM_PROG).hex run

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
	$(MKDIR_P) $(VSIM_RESULTS)/$(COV_MERGE_DIR)
	cd $(COV_DIR) && \
		$(COV_MERGE_FIND)
	cd $(VSIM_RESULTS)/$(COV_MERGE_DIR) && \
		$(VCOVER) \
			$(COV_MERGE_FLAGS)
cov: $(COV_MERGE_TARGET)
	cd $(COV_DIR) && \
		$(VSIM) \
			$(COV_FLAGS)

###############################################################################
# Clean up your mess!

clean:
	rm -rf $(VSIM_RESULTS)

# All generated files plus the clone of the RTL
clean_all: clean clean_core_tests
	rm -rf $(CV32E40P_PKG)
