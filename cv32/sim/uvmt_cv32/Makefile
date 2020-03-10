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
# Makefile for the CV32E40P "uvmt_cv32" testbench.  Substantially modified
# from the original Makefile for the RI5CY testbench.
#
###############################################################################
# 
# Copyright 2019 Clifford Wolf
# Copyright 2019 Robert Balas
#
# Permission to use, copy, modify, and/or distribute this software for any
# purpose with or without fee is hereby granted, provided that the above
# copyright notice and this permission notice appear in all copies.
#
# THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES WITH
# REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF MERCHANTABILITY
# AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY SPECIAL, DIRECT,
# INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES WHATSOEVER RESULTING FROM
# LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION OF CONTRACT, NEGLIGENCE OR
# OTHER TORTIOUS ACTION, ARISING OUT OF OR IN CONNECTION WITH THE USE OR
# PERFORMANCE OF THIS SOFTWARE.
#
# Original Author: Robert Balas (balasr@iis.ee.ethz.ch)
#
###############################################################################

MAKE          = make
WAVES         = 0
COREV_PROJ    = cv32
PROJ_ROOT_DIR = $(PWD)/../../..



# Compile compile flags for all simulators
SV_CMP_FLAGS = 
UVM_PLUSARGS =

# questa simulator

USES_DPI=1

ifeq ($(USES_DPI),1)
  DPILIB_VLOG_OPT = 
  DPILIB_VSIM_OPT = -sv_lib $(UVM_HOME)/../../uvm-1.2/linux_x86_64/uvm_dpi
  DPILIB_TARGET = dpi_lib$(BITS)
else
  DPILIB_VLOG_OPT = +define+UVM_NO_DPI 
  DPILIB_VSIM_OPT = 
  DPILIB_TARGET =
endif

LIBDIR  = $(UVM_HOME)/lib
LIBNAME = uvm_dpi

VLIB      = vlib
VWORK     = work

VLOG          = vlog
VLOG_FLAGS    = -pedanticerrors -suppress 2577 -suppress 2583 \
        $(DPILIB_VLOG_OPT) \
	-timescale "1ns/1ps" \
        -mfcu \
        -suppress 2181 \
	-suppress 13262 \
        +acc=rb \
        -writetoplevels  uvmt_cv32_tb \
        +incdir+$(UVM_HOME)/src \
        $(UVM_HOME)/src/uvm.sv

VLOG_LOG      = vloggy

VOPT          = vopt
VOPT_FLAGS    = -debugdb -fsmdebug -pedanticerrors +acc #=mnprft

VSIM              = vsim
VSIM_HOME         = /usr/pack/modelsim-$(VVERSION)-kgf/questasim
VSIM_FLAGS       ?=  # user defined
ALL_VSIM_FLAGS    = $(VSIM_FLAGS)
VSIM_DEBUG_FLAGS  = -debugdb
VSIM_GUI_FLAGS    = -gui -debugdb
VSIM_SCRIPT_DIR	  = ../questa
VSIM_SCRIPT       = $(VSIM_SCRIPT_DIR)/vsim.tcl

VSIM_UVM_ARGS           = +incdir+$(UVM_HOME)/src $(UVM_HOME)/src/uvm_pkg.sv




# dsim is the Metrics Technologies SystemVerilog simulator  (https://metrics.ca/)
DSIM                    = dsim
DSIM_HOME               = /tools/Metrics/dsim
DSIM_CMP_FLAGS          = -timescale 1ns/1ps $(SV_CMP_FLAGS)
DSIM_UVM_ARGS           = +incdir+$(UVM_HOME)/src $(UVM_HOME)/src/uvm_pkg.sv
DSIM_RESULTS           ?= $(PWD)/dsim_results
DSIM_WORK              ?= $(DSIM_RESULTS)/dsim_work
DSIM_IMAGE              = dsim.out

# UVM Environment
export DV_UVMT_CV32_PATH  = $(PROJ_ROOT_DIR)/$(COREV_PROJ)/tb/uvmt_cv32
export DV_UVME_CV32_PATH  = $(PROJ_ROOT_DIR)/$(COREV_PROJ)/env/uvme_cv32
export DV_UVML_HRTBT_PATH = $(PROJ_ROOT_DIR)/lib/uvm_libs/uvml_hrtbt
export DV_UVML_TRN_PATH   = $(PROJ_ROOT_DIR)/lib/uvm_libs/uvml_trn
export DV_UVML_LOGS_PATH  = $(PROJ_ROOT_DIR)/lib/uvm_libs/uvml_logs
export DV_UVML_SB_PATH    = $(PROJ_ROOT_DIR)/lib/uvm_libs/uvml_sb
DV_UVMT_CV32_SRCS  = $(wildcard $(DV_UVMT_CV32_PATH)/*.sv))

# Testcase name: must be the CLASS name of the testcase (not the filename).
# Look in ../../tests/uvmt_cv32.
UVM_TESTNAME ?= uvmt_cv32_smoke_test_c

# TB source files for the CV32E core
TBSRC_HOME  := $(PROJ_ROOT_DIR)/$(COREV_PROJ)/tb
export TBSRC_HOME  = $(PROJ_ROOT_DIR)/$(COREV_PROJ)/tb
TBSRC_PKG   := $(TBSRC_HOME)/tb_riscv/include/perturbation_defines.sv
TBSRC_TOP   := $(TBSRC_HOME)/uvmt_cv32/uvmt_cv32_tb.sv
TBSRC       := $(TBSRC_HOME)/uvmt_cv32/uvmt_cv32_tb.sv \
               $(TBSRC_HOME)/uvmt_cv32/uvmt_cv32_dut_wrap.sv \
               $(TBSRC_HOME)/core/tb_top.sv \
               $(TBSRC_HOME)/core/riscv_wrapper.sv \
               $(TBSRC_HOME)/core/mm_ram.sv \
               $(TBSRC_HOME)/core/dp_ram.sv \
               $(TBSRC_HOME)/tb_riscv/riscv_random_stall.sv \
               $(TBSRC_HOME)/tb_riscv/riscv_random_interrupt_generator.sv

SIM_LIBS    := $(PROJ_ROOT_DIR)/lib/sim_libs

RTLSRC_VLOG_TB_TOP	:= $(basename $(notdir $(TBSRC_TOP)))
RTLSRC_VOPT_TB_TOP	:= $(addsuffix _vopt, $(RTLSRC_VLOG_TB_TOP))

# RTL source files for the CV32E core
# DESIGN_RTL_DIR is used by CV32E40P_MANIFEST file
CV32E40P_PKG         := $(PROJ_ROOT_DIR)/core-v-cores/cv32e40p
FPNEW_PKG            := $(CV32E40P_PKG)/rtl/fpnew
CV32E40P_MANIFEST    := $(CV32E40P_PKG)/cv32e40p_manifest.flist
export DESIGN_RTL_DIR = $(CV32E40P_PKG)/rtl

RTLSRC_HOME   := $(CV32E40P_PKG)/rtl
RTLSRC_INCDIR := $(RTLSRC_HOME)/include


###############################################################################
# Common Makefile:
#    - Core Firmware and the RISCV GCC Toolchain (SDK)
#    - Variables for RTL dependencies
include ../Common.mk


###############################################################################
# CV32E40P RTL dependencies
# The variables RTLSRC_PKG and RTLSRC need to be re-evaluated since
# CV32E40P_PKG was null the first time.
# TODO: cmd to eval RTLSRC needs to be replaced with a manifest (flist)
clone_cv32e40p_rtl:
	$(CLONE_CV32E40P_CMD)

clone_fpnew_rtl: clone_cv32e40p_rtl
	$(CLONE_FPNEW_CMD)

$(CV32E40P_PKG):
	$(CLONE_CV32E40P_CMD)
	$(CLONE_FPNEW_CMD)


###############################################################################
# Defaults: assume compile of both ENV and RTL if no target chosen
.DEFAULT_GOAL := dsim-hello_world

all: clean_all dsim-hello_world


###############################################################################
# SystemVerilog simulator compilation and run

# Metrics dsim
.PHONY: dsim-sim

MKDIR_P = mkdir -p

mk_results: 
	$(MKDIR_P) $(DSIM_RESULTS)
	$(MKDIR_P) $(DSIM_WORK)

# DSIM compile target
#      - note that uvme_cv32_pkg.flist *must* be read before uvmt_cv32.flist
#      - TODO: cd $(DSIM_RESULTS) - incompatible with pkg file
dsim-comp: mk_results $(CV32E40P_PKG)
	$(DSIM) \
		$(DSIM_CMP_FLAGS) \
		$(DSIM_UVM_ARGS) \
		-sv_lib $(UVM_HOME)/src/dpi/libuvm_dpi.so \
		+incdir+$(DV_UVME_CV32_PATH) \
		+incdir+$(DV_UVMT_CV32_PATH) \
		-f $(CV32E40P_MANIFEST) \
		-f $(DV_UVME_CV32_PATH)/uvme_cv32_pkg.flist \
		-f $(DV_UVMT_CV32_PATH)/uvmt_cv32.flist \
		-work $(DSIM_WORK) \
		+$(UVM_PLUSARGS) \
		-genimage $(DSIM_IMAGE)

dsim-no-firmware: dsim-comp
	mkdir -p $(DSIM_RESULTS)/hello_world && cd $(DSIM_RESULTS)/hello_world  && \
	$(DSIM) -l dsim-$(UVM_TESTNAME).log -image $(DSIM_IMAGE) \
		-work $(DSIM_WORK) $(DSIM_RUN_FLAGS) \
		-sv_lib $(UVM_HOME)/src/dpi/libuvm_dpi.so \
		+UVM_TESTNAME=$(UVM_TESTNAME)
#		+verbose

dsim-hello_world: dsim-comp $(CUSTOM)/hello_world.hex
	mkdir -p $(DSIM_RESULTS)/hello_world && cd $(DSIM_RESULTS)/hello_world  && \
	$(DSIM) -l dsim-hello_world.log -image $(DSIM_IMAGE) \
		-work $(DSIM_WORK) $(DSIM_RUN_FLAGS) \
		-sv_lib $(UVM_HOME)/src/dpi/libuvm_dpi.so \
		+UVM_TESTNAME=uvmt_cv32_firmware_test_c \
		+firmware=$(CUSTOM)/hello_world.hex
#		+verbose

# Runs tests in riscv_tests/ only
dsim-cv32_riscv_tests: dsim-comp $(CV32_RISCV_TESTS_FIRMWARE)/cv32_riscv_tests_firmware.hex
	mkdir -p $(DSIM_RESULTS)/riscv-tests && cd $(DSIM_RESULTS)/riscv-tests && \
	$(DSIM) -l dsim-riscv_tests.log -image $(DSIM_IMAGE) \
		-work $(DSIM_WORK) $(DSIM_RUN_FLAGS) \
		-sv_lib $(UVM_HOME)/src/dpi/libuvm_dpi.so \
		+UVM_TESTNAME=uvmt_cv32_firmware_test_c \
		+firmware=$(CV32_RISCV_TESTS_FIRMWARE)/cv32_riscv_tests_firmware.hex

# Runs tests in riscv_compliance_tests/ only
dsim-cv32_riscv_compliance_tests: dsim-comp $(CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE)/cv32_riscv_compliance_tests_firmware.hex
	mkdir -p $(DSIM_RESULTS)/riscv-compliance && cd $(DSIM_RESULTS)/riscv-compliance && \
	$(DSIM) -l dsim-riscv_compliance_tests.log -image $(DSIM_IMAGE) \
		-work $(DSIM_WORK) $(DSIM_RUN_FLAGS) \
		-sv_lib $(UVM_HOME)/src/dpi/libuvm_dpi.so \
		+UVM_TESTNAME=uvmt_cv32_firmware_test_c \
		+firmware=$(CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE)/cv32_riscv_compliance_tests_firmware.hex

# Runs all tests in riscv_tests/ and riscv_compliance_tests/
dsim-firmware: dsim-comp $(FIRMWARE)/firmware.hex
	mkdir -p $(DSIM_RESULTS)/firmware && cd $(DSIM_RESULTS)/firmware && \
	$(DSIM) -l dsim-firmware.log -image $(DSIM_IMAGE) \
		-work $(DSIM_WORK) \
		-sv_lib $(UVM_HOME)/src/dpi/libuvm_dpi.so \
		+UVM_TESTNAME=uvmt_cv32_firmware_test_c \
		+firmware=$(FIRMWARE)/firmware.hex

###############################################################################
# DSIM UNIT TESTS: run each test individually.
# DO NOT INVOKE rule "dsim-firmware-unit-test" directly.   It is a support
# rule for rule "dsim-unit-test" (in included ../Common.mk).
#
# Example: to run the ADDI test `make dsim-unit-test addi`
dsim-unit-test: dsim-comp
	mkdir -p $(DSIM_RESULTS)/firmware && cd $(DSIM_RESULTS)/firmware && \
	$(DSIM) -l dsim-$(UNIT_TEST).log -image $(DSIM_IMAGE) \
		-work $(DSIM_WORK) \
		-sv_lib $(UVM_HOME)/src/dpi/libuvm_dpi.so \
		+UVM_TESTNAME=uvmt_cv32_firmware_test_c \
		+firmware=$(FIRMWARE)/firmware_unit_test.hex


# Mentor Questasim

.lib-rtl:
	$(VLIB) $(VWORK)
	touch .lib-rtl


.build-rtl: .lib-rtl $(CV32E40P_PKG) $(TBSRC_PKG) $(TBSRC)
	$(VLOG)  -work $(VWORK) $(VLOG_FLAGS) -f $(DV_UVME_CV32_PATH)/uvme_cv32_pkg.flist
	$(VLOG)  -work $(VWORK) $(VLOG_FLAGS)  -f $(CV32E40P_MANIFEST) -f $(DV_UVMT_CV32_PATH)/uvmt_cv32.flist
	$(VLOG) \
		-work $(VWORK) \
		$(VLOG_FLAGS) \
		+incdir+$(DV_UVME_CV32_PATH) \
		+incdir+$(DV_UVMT_CV32_PATH) \
		-f $(DV_UVMT_CV32_PATH)/uvmt_cv32.flist \
		-f $(DV_UVME_CV32_PATH)/uvme_cv32_pkg.flist \
		-f $(CV32E40P_MANIFEST) \
		$(TBSRC_PKG) $(TBSRC) 
		

vsim-all:  .opt-rtl
	

.opt-rtl: .build-rtl
	$(VOPT) -work $(VWORK) $(VOPT_FLAGS) $(RTLSRC_VLOG_TB_TOP) -o $(RTLSRC_VOPT_TB_TOP)
	touch .opt-rtl

# run tb and exit
.PHONY: vsim-run
vsim-run: ALL_VSIM_FLAGS += -c +UVM_TESTNAME=uvmt_cv32_firmware_test_c 
vsim-run: vsim-all
	$(VSIM) -work $(VWORK) $(DPILIB_VSIM_OPT) $(ALL_VSIM_FLAGS)\
	$(RTLSRC_VOPT_TB_TOP) -do 'source $(VSIM_SCRIPT); exit -f'



# run tb and drop into interactive shell
.PHONY: vsim-run-sh
vsim-run-sh: ALL_VSIM_FLAGS += -c
vsim-run-sh: vsim-all
	$(VSIM) -work $(VWORK) $(DPILIB_VSIM_OPT) $(ALL_VSIM_FLAGS) \
	$(RTLSRC_VOPT_TB_TOP) -do $(VSIM_SCRIPT)

# run tb with simulator gui
.PHONY: vsim-run-gui
vsim-run-gui: ALL_VSIM_FLAGS += $(VSIM_GUI_FLAGS) +UVM_TESTNAME=uvmt_cv32_firmware_test_c +firmware=$(FIRMWARE)/firmware.hex
vsim-run-gui: vsim-all
	$(VSIM) -work $(VWORK) $(DPILIB_VSIM_OPT) $(ALL_VSIM_FLAGS) \
	$(RTLSRC_VOPT_TB_TOP) -do $(VSIM_SCRIPT)


.PHONY: questa-hello_world
questa-hello_world: vsim-all $(CUSTOM)/hello_world.hex
questa-hello_world: ALL_VSIM_FLAGS += +firmware=$(CUSTOM)/hello_world.hex
questa-hello_world: vsim-run

.PHONY: questa-cv32_riscv_tests
questa-cv32_riscv_tests: vsim-all $(CV32_RISCV_TESTS_FIRMWARE)/cv32_riscv_tests_firmware.hex
questa-cv32_riscv_tests: ALL_VSIM_FLAGS += +firmware=$(CV32_RISCV_TESTS_FIRMWARE)/cv32_riscv_tests_firmware.hex
questa-cv32_riscv_tests: vsim-run

.PHONY: questa-cv32_riscv_tests-gui
questa-cv32_riscv_tests-gui: vsim-all $(CV32_RISCV_TESTS_FIRMWARE)/cv32_riscv_tests_firmware.hex
questa-cv32_riscv_tests-gui: ALL_VSIM_FLAGS += +firmware=$(CV32_RISCV_TESTS_FIRMWARE)/cv32_riscv_tests_firmware.hex
questa-cv32_riscv_tests-gui: vsim-run-gui

.PHONY: questa-cv32_riscv_compliance_tests
questa-cv32_riscv_compliance_tests: vsim-all $(CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE)/cv32_riscv_compliance_tests_firmware.hex
questa-cv32_riscv_compliance_tests: ALL_VSIM_FLAGS += +firmware=$(CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE)/cv32_riscv_compliance_tests_firmware.hex
questa-cv32_riscv_compliance_tests: vsim-run

.PHONY: questa-cv32_riscv_compliance_tests-gui
questa-cv32_riscv_compliance_tests-gui: vsim-all $(CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE)/cv32_riscv_compliance_tests_firmware.hex
questa-cv32_riscv_compliance_tests-gui: ALL_VSIM_FLAGS += +firmware=$(CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE)/cv32_riscv_compliance_tests_firmware.hex
questa-cv32_riscv_compliance_tests-gui: vsim-run-gui

.PHONY: questa-firmware
questa-firmware: vsim-all $(FIRMWARE)/firmware.hex
questa-firmware: ALL_VSIM_FLAGS += +firmware=$(FIRMWARE)/firmware.hex
questa-firmware: vsim-run

.PHONY: questa-firmware-gui
questa-firmware-gui: vsim-all $(FIRMWARE)/firmware.hex
questa-firmware-gui: ALL_VSIM_FLAGS += +firmware=$(FIRMWARE)/firmware.hex
questa-firmware-gui: vsim-run-gui

.PHONY: questa-unit-test 
questa-unit-test:  firmware-unit-test-clean 
questa-unit-test:  $(FIRMWARE)/firmware_unit_test.hex 
questa-unit-test: ALL_VSIM_FLAGS += "+firmware=$(FIRMWARE)/firmware_unit_test.hex"
questa-unit-test: vsim-run

.PHONY: questa-unit-test-gui 
questa-unit-test-gui:  firmware-unit-test-clean 
questa-unit-test-gui:  $(FIRMWARE)/firmware_unit_test.hex 
questa-unit-test-gui: ALL_VSIM_FLAGS += "+firmware=$(FIRMWARE)/firmware_unit_test.hex"
questa-unit-test-gui: vsim-run-gui

###############################################################################
# Clean up your mess!

.PHONY: clean_dsim clean_core_tests clean_all

# Metrics dsim cleanup
clean_dsim:
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


clean_questa:
	if [ -d $(VWORK) ]; then rm -r $(VWORK); fi
	rm -f transcript vsim.wlf vsim.dbg trace_core*.log \
	.build-rtl .opt-rtl .lib-rtl *.vcd objdump

# Clean all generated files of the C and assembler tests in tests/core
# CORE_TEST_DIR is defined in ../Common.mk
clean_core_tests:
	find $(CORE_TEST_DIR) -name *.o   -exec rm {} \;
	find $(CORE_TEST_DIR) -name *.hex -exec rm {} \;
	find $(CORE_TEST_DIR) -name *.elf -exec rm {} \;
	find $(CORE_TEST_DIR) -name *.map -exec rm {} \;

# All generated files plus the clone of the RTL
clean_all: clean_questa clean_dsim clean_core_tests custom-clean firmware-clean
	rm -rf $(CV32E40P_PKG)
