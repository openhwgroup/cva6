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
# Makefile to test compilation of the UVM Environment and RTL.  Written
# specifically for Metrics DSIM.  Not intended to run tests from here.
#
###############################################################################

MAKE       = make
COREV_PROJ = cv32
ROOT_DIR   = $(PWD)/../../..

# dsim is the Metrics Technologies SystemVerilog simulator  (https://metrics.ca/)
DSIM                    = dsim
DSIM_HOME               = /tools/Metrics/dsim
DSIM_CMP_FLAGS          = -timescale 1ns/1ps
DSIM_UVM_ARGS           = +incdir+$(UVM_HOME)/src $(UVM_HOME)/src/uvm_pkg.sv
DSIM_RESULTS           ?= $(PWD)/results
DSIM_WORK              ?= $(DSIM_RESULTS)/dsim_work
DSIM_IMAGE              = dsim.out

# UVM Environment
export DV_UVMT_CV32_PATH = $(ROOT_DIR)/$(COREV_PROJ)/tb/uvmt_cv32
export DV_UVME_CV32_PATH = $(ROOT_DIR)/$(COREV_PROJ)/env/uvme_cv32
DV_UVMT_CV32_SRCS  = $(wildcard $(DV_UVMT_CV32_PATH)/*.sv))

# TB source files for the CV32E core
TBSRC_HOME  := $(ROOT_DIR)/$(COREV_PROJ)/tb
TBSRC_PKG   := $(TBSRC_HOME)/tb_riscv/include/perturbation_defines.sv
TBSRC       := $(TBSRC_HOME)/uvmt_cv32/uvmt_cv32_tb.sv \
               $(TBSRC_HOME)/uvmt_cv32/uvmt_cv32_dut_wrap.sv \
               $(TBSRC_HOME)/core/mm_ram.sv \
               $(TBSRC_HOME)/core/dp_ram.sv \
               $(TBSRC_HOME)/tb_riscv/riscv_random_stall.sv \
               $(TBSRC_HOME)/tb_riscv/riscv_random_interrupt_generator.sv

# RTL source files for the CV32E core
RTLSRC_HOME   := $(ROOT_DIR)/rtl
RTLSRC_INCDIR := $(RTLSRC_HOME)/include
FPNEW_PKG     := $(RTLSRC_HOME)/fpnew
RTLSRC_PKG    := $(FPNEW_PKG)/src/fpnew_pkg.sv \
                 $(addprefix $(RTLSRC_HOME)/include/,\
                   apu_core_package.sv \
                   riscv_defines.sv \
                   riscv_tracer_defines.sv)
RTLSRC        := $(filter-out $(RTLSRC_HOME)/riscv_register_file_latch.sv,\
                   $(wildcard $(RTLSRC_HOME)/*.sv))

# assume compile of both ENV and RTL if no target chosen
.DEFAULT_GOAL := dsim-comp

all: clean_all dsim-comp

# fpnew dependencies
$(FPNEW_PKG):
	git clone https://github.com/pulp-platform/fpnew --recurse $(FPNEW_PKG)

# Metrics dsim testbench compilation 
.PHONY: dsim-comp dsim-comp-rtl-only

MKDIR_P = mkdir -p

mk_results: 
	$(MKDIR_P) $(DSIM_RESULTS)
	$(MKDIR_P) $(DSIM_WORK)

# TODO: cd $(DSIM_RESULTS) - incompatible with pkg file
dsim-comp: mk_results $(FPNEW_PKG)
	$(DSIM) \
		$(DSIM_CMP_FLAGS) \
		$(DSIM_UVM_ARGS) \
		+incdir+$(DV_UVMT_CV32_PATH) \
		+incdir+$(DV_UVME_CV32_PATH) \
		-f $(DV_UVMT_CV32_PATH)/uvmt_cv32.flist \
		-f $(DV_UVME_CV32_PATH)/uvme_cv32_pkg.flist \
		$(RTLSRC_PKG) $(RTLSRC) $(TBSRC_PKG) $(TBSRC) \
		+incdir+$(RTLSRC_INCDIR) \
		-work $(DSIM_WORK) \
		-genimage $(DSIM_IMAGE)

# Metrics dsim cleanup
.PHONY: dsim-clean clean_all

dsim-clean:
	rm -f dsim.log
	rm -f dsim-*.log
	rm -f metrics_history.db
	rm -f metrics.xml
	rm -f trace_core_00_0.log
	rm -rf dsim_work
	rm -f dsim.env
	rm -f $(DSIM_IMAGE)
	rm -rf $(DSIM_RESULTS)

clean_all: dsim-clean
	rm -rf $(FPNEW_PKG)
