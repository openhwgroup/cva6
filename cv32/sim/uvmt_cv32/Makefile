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
# Makefile to run tests and regressions of the CV32E UVM Environment and RTL.
# Currently only supports Metrics DSIM.
#
###############################################################################

MAKE          = make
COREV_PROJ    = cv32
PROJ_ROOT_DIR = $(PWD)/../../..

# Compile compile flags for all simulators
SV_CMP_FLAGS = 
UVM_PLUSARGS =

# dsim is the Metrics Technologies SystemVerilog simulator  (https://metrics.ca/)
DSIM                    = dsim
DSIM_HOME               = /tools/Metrics/dsim
DSIM_CMP_FLAGS          = -timescale 1ns/1ps $(SV_CMP_FLAGS)
DSIM_UVM_ARGS           = +incdir+$(UVM_HOME)/src $(UVM_HOME)/src/uvm_pkg.sv
DSIM_RESULTS           ?= $(PWD)/results
DSIM_WORK              ?= $(DSIM_RESULTS)/dsim_work
DSIM_IMAGE              = dsim.out

# UVM Environment
export DV_UVMT_CV32_PATH = $(PROJ_ROOT_DIR)/$(COREV_PROJ)/tb/uvmt_cv32
export DV_UVME_CV32_PATH = $(PROJ_ROOT_DIR)/$(COREV_PROJ)/env/uvme_cv32
DV_UVMT_CV32_SRCS  = $(wildcard $(DV_UVMT_CV32_PATH)/*.sv))

# Testcase name: must be the CLASS name of the testcase (not the filename).
# Look in ../../tests/uvmt_cv32.
UVM_TESTNAME ?= uvmt_cv32_smoke_test_c

# TB source files for the CV32E core
TBSRC_HOME  := $(PROJ_ROOT_DIR)/$(COREV_PROJ)/tb
TBSRC_PKG   := $(TBSRC_HOME)/tb_riscv/include/perturbation_defines.sv
TBSRC       := $(TBSRC_HOME)/uvmt_cv32/uvmt_cv32_tb.sv \
               $(TBSRC_HOME)/uvmt_cv32/uvmt_cv32_dut_wrap.sv \
               $(TBSRC_HOME)/core/mm_ram.sv \
               $(TBSRC_HOME)/core/dp_ram.sv \
               $(TBSRC_HOME)/tb_riscv/riscv_random_stall.sv \
               $(TBSRC_HOME)/tb_riscv/riscv_random_interrupt_generator.sv
SIM_LIBS    := $(PROJ_ROOT_DIR)/lib/sim_libs

# RTL source files for the CV32E core
CV32E40P_PKG  := $(PROJ_ROOT_DIR)/core-v-cores/cv32e40p
RTLSRC_HOME   := $(CV32E40P_PKG)/rtl
FPNEW_PKG     := $(RTLSRC_HOME)/fpnew
RTLSRC_INCDIR := $(RTLSRC_HOME)/include
RTLSRC_PKG    := $(FPNEW_PKG)/src/fpnew_pkg.sv \
                 $(RTLSRC_HOME)/cv32e40p_sim_clock_gating.sv \
                 $(addprefix $(RTLSRC_HOME)/include/,\
                   apu_core_package.sv \
                   riscv_defines.sv \
                   riscv_tracer_defines.sv)
RTLSRC        := $(filter-out $(RTLSRC_HOME)/riscv_register_file_latch.sv,\
                   $(wildcard $(RTLSRC_HOME)/*.sv))


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
	$(eval RTLSRC_HOME   = $(CV32E40P_PKG)/rtl)
	$(eval RTLSRC_PKG = $(FPNEW_PKG)/src/fpnew_pkg.sv \
	                    $(addprefix $(RTLSRC_HOME)/include/,\
	                      apu_core_package.sv \
	                      riscv_defines.sv \
	                      riscv_tracer_defines.sv))
	$(eval RTLSRC = $(RTLSRC_HOME)/riscv_alu_div.sv \
                  $(RTLSRC_HOME)/cv32e40p_sim_clock_gating.sv \
                  $(RTLSRC_HOME)/riscv_controller.sv \
                  $(RTLSRC_HOME)/riscv_ex_stage.sv \
                  $(RTLSRC_HOME)/riscv_id_stage.sv \
                  $(RTLSRC_HOME)/riscv_load_store_unit.sv \
                  $(RTLSRC_HOME)/riscv_prefetch_L0_buffer.sv \
                  $(RTLSRC_HOME)/riscv_alu.sv \
                  $(RTLSRC_HOME)/riscv_core.sv \
                  $(RTLSRC_HOME)/riscv_fetch_fifo.sv \
                  $(RTLSRC_HOME)/riscv_if_stage.sv \
                  $(RTLSRC_HOME)/riscv_mult.sv \
                  $(RTLSRC_HOME)/register_file_test_wrap.sv \
                  $(RTLSRC_HOME)/riscv_apu_disp.sv \
                  $(RTLSRC_HOME)/riscv_cs_registers.sv \
                  $(RTLSRC_HOME)/riscv_hwloop_controller.sv \
                  $(RTLSRC_HOME)/riscv_int_controller.sv \
                  $(RTLSRC_HOME)/riscv_pmp.sv \
                  $(RTLSRC_HOME)/riscv_register_file.sv \
                  $(RTLSRC_HOME)/riscv_alu_basic.sv \
                  $(RTLSRC_HOME)/riscv_compressed_decoder.sv \
                  $(RTLSRC_HOME)/riscv_decoder.sv \
                  $(RTLSRC_HOME)/riscv_hwloop_regs.sv \
                  $(RTLSRC_HOME)/riscv_L0_buffer.sv \
                  $(RTLSRC_HOME)/riscv_prefetch_buffer.sv \
                  $(RTLSRC_HOME)/riscv_tracer.sv)


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

# TODO: cd $(DSIM_RESULTS) - incompatible with pkg file
dsim-comp: mk_results $(CV32E40P_PKG)
	$(DSIM) \
		$(DSIM_CMP_FLAGS) \
		$(DSIM_UVM_ARGS) \
		+incdir+$(DV_UVMT_CV32_PATH) \
		+incdir+$(DV_UVME_CV32_PATH) \
		-f $(DV_UVMT_CV32_PATH)/uvmt_cv32.flist \
		-f $(DV_UVME_CV32_PATH)/uvme_cv32_pkg.flist \
		$(RTLSRC_PKG) $(RTLSRC) $(TBSRC_PKG) $(TBSRC) \
		+incdir+$(RTLSRC_INCDIR) \
		-sv_lib $(UVM_HOME)/src/dpi/libuvm_dpi.so \
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
# rule for rule "dsim-unit-test" (in included ../Firmware.mk).
#
# Example: to run the ADDI test `make dsim-unit-test addi`
dsim-firmware-unit-test: dsim-comp
	mkdir -p $(DSIM_RESULTS)/firmware && cd $(DSIM_RESULTS)/firmware && \
	$(DSIM) -l dsim-$(UNIT_TEST).log -image $(DSIM_IMAGE) \
		-work $(DSIM_WORK) \
		-sv_lib $(UVM_HOME)/src/dpi/libuvm_dpi.so \
		+UVM_TESTNAME=uvmt_cv32_firmware_test_c \
		+firmware=$(FIRMWARE)/firmware_unit_test.hex


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

# Clean all generated files of the C and assembler tests in tests/core
clean_core_tests:
	find $(CORE_TEST_DIR) -name *.o   -exec rm {} \;
	find $(CORE_TEST_DIR) -name *.hex -exec rm {} \;
	find $(CORE_TEST_DIR) -name *.elf -exec rm {} \;
	find $(CORE_TEST_DIR) -name *.map -exec rm {} \;

# All generated files plus the clone of the RTL
clean_all: clean_dsim clean_core_tests
	rm -rf $(CV32E40P_PKG)
