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
SV_CMP_FLAGS = +define+__USE_COREV_SIMULATION_MODELS__ # workaround for https://github.com/openhwgroup/cv32e40p/issues/208
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

# Testcase name
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
                 $(SIM_LIBS)/cluster_clock_gating.sv \
                 $(addprefix $(RTLSRC_HOME)/include/,\
                   apu_core_package.sv \
                   riscv_defines.sv \
                   riscv_tracer_defines.sv)
RTLSRC        := $(filter-out $(RTLSRC_HOME)/riscv_register_file_latch.sv,\
                   $(wildcard $(RTLSRC_HOME)/*.sv))

###############################################################################
# CV32E40P RTL dependencies
# The variables RTLSRC_PKG and RTLSRC need to be re-evaluated since
# CV32E40P_PKG was null the first time.
# TODO: cmd to eval RTLSRC needs to be replaced with a manifest (flist)
$(CV32E40P_PKG):
	git clone https://github.com/openhwgroup/cv32e40p --recurse $(CV32E40P_PKG)
	git clone https://github.com/pulp-platform/fpnew --recurse $(FPNEW_PKG)
	$(eval RTLSRC_HOME   = $(CV32E40P_PKG)/rtl)
	$(eval RTLSRC_PKG = $(FPNEW_PKG)/src/fpnew_pkg.sv \
	                    $(SIM_LIBS)/cluster_clock_gating.sv \
	                    $(addprefix $(RTLSRC_HOME)/include/,\
	                      apu_core_package.sv \
	                      riscv_defines.sv \
	                      riscv_tracer_defines.sv))
	$(eval RTLSRC = $(RTLSRC_HOME)/riscv_alu_div.sv \
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
# Firmware and the RISCV GCC Toolchain (SDK)

# riscv toolchain install path
RISCV            ?= ~/.riscv
RISCV_EXE_PREFIX  = $(RISCV)/bin/riscv32-unknown-elf-

# firmware vars
CORE_TEST_DIR     = ../../tests/core
FIRMWARE          = $(CORE_TEST_DIR)/firmware
CUSTOM            = $(CORE_TEST_DIR)/custom


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
		+UVM_TESTNAME=$(UVM_TESTNAME) \
		+$(UVM_PLUSARGS) \
		-genimage $(DSIM_IMAGE)

dsim-hello_world: dsim-comp $(CUSTOM)/hello_world.hex
	mkdir -p $(DSIM_RESULTS)/hello_world && cd $(DSIM_RESULTS)/hello_world  && \
	$(DSIM) -l dsim-hello_world.log -image $(DSIM_IMAGE) \
		-work $(DSIM_WORK) $(DSIM_RUN_FLAGS) \
		-sv_lib $(UVM_HOME)/src/dpi/libuvm_dpi.so \
		+UVM_TESTNAME=$(UVM_TESTNAME) \
		+firmware=/data/mike/GitHubRepos/MikeOpenHWGroup/core-v-verif/ohw_mike_20200214/cv32/tests/core/custom/hello_world.hex
#		+verbose +firmware=$(ROOT_DIR)/$(CUSTOM)/hello_world.hex


###############################################################################
# Clean up your mess!

# Metrics dsim cleanup
.PHONY: dsim-clean clean_all

dsim-clean:
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

clean_all: dsim-clean
	rm -rf $(CV32E40P_PKG)
