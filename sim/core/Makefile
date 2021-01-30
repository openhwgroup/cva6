###############################################################################
#
# Copyright 2021 OpenHW Group
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
# Makefile for the CVA6 "core" testbench.
#
###############################################################################

# Shell environment variables
export CVA6_DESIGN_HOME ?= ../..
export CVA6_CORE_HOME   ?= ../..

# Global "Constants"
MAKE           = make
MAKE_DIR       = $(PWD)
MAKE_PATH     := $(shell dirname $(realpath $(firstword $(MAKEFILE_LIST))))
COREV_PROJ     = cva6
PROJ_ROOT_DIR  = $(abspath $(MAKE_PATH)/../..)
DATE           = $(shell date +%F)
# Global Variables
WAVES         ?= 0
WAVE          ?= 0
RESULTS_DIR   ?= results
TEST_PROGRAM  ?= no_test

###############################################################################
# Common Makefile:
#    - Core Firmware and the RISCV GCC Toolchain (SDK)
#    - Variables for RTL dependencies
#include $(PROJ_ROOT_DIR)/cva6/sim/Common.mk
include ../../sim/Common.mk

###############################################################################
# Verilator specific variables, targets and rules

VERI_COMPILE_FLAGS ?=
VERI_RUNTIME_FLAGS ?=
VERI_WORKDIR       ?= verilator_work
VERI_CVA6_TH       ?= cva6_testharness
VERI_RESULTS_DIR   ?= verilator_$(RESULTS_DIR)
VERI_TRANS_LOG     ?= verilator_trans.log
VERI_COMPL_LOG     ?= verilator_compl.log
VERI_RUN_LOG       ?= $(TEST_PROGRAM).log
# User controlled VCD dumping (using either "WAVE" or "WAVES"):
# Conditionally compile the C++ testbench (-DVCD_TRACE) and pass
# the --trace flags to the verilator call.
ifneq (${WAVES}, 0)
VERI_TRACE          =--trace
VERI_COMPILE_FLAGS  =-DVCD_TRACE
endif
ifneq (${WAVE}, 0)
VERI_TRACE          =--trace
VERI_COMPILE_FLAGS  =-DVCD_TRACE
endif

verilator_clean:
	@echo "[VERILATOR] clean up"
	rm -rf verilator_results/verilator_work

verilator_comp:
	@echo "$(BANNER)"
	@echo "[VERILATOR] Translating Model"
	mkdir -p $(VERI_RESULTS_DIR)
	mkdir -p $(VERI_RESULTS_DIR)/$(VERI_WORKDIR)
	verilator \
	    -f ${CVA6_DESIGN_HOME}/cva6_manifest.flist \
	    ${PROJ_ROOT_DIR}/core_tb/cva6_core_tb.sv \
	    ${PROJ_ROOT_DIR}/core_tb/cva6_core_tb.cpp \
	    $(VERI_TRACE) \
	    --unroll-count 256 \
	    -Werror-PINMISSING \
	    -Werror-IMPLICIT \
	    -Wno-fatal \
	    -Wno-PINCONNECTEMPTY \
	    -Wno-ASSIGNDLY \
	    -Wno-DECLFILENAME \
	    -Wno-UNUSED \
	    -Wno-UNOPTFLAT \
	    -Wno-BLKANDNBLK \
	    -Wno-style \
	    -CFLAGS "-std=gnu++11 $(VERI_COMPILE_FLAGS)" \
	    -Wall \
	    --sv \
	    --cc \
	    --vpi \
	    --top-module $(VERI_CVA6_TH) \
	    --Mdir $(VERI_RESULTS_DIR)/$(VERI_WORKDIR) \
	    --exe \
	    | tee 2>&1 $(VERI_RESULTS_DIR)/$(VERI_WORKDIR)/$(VERI_TRANS_LOG)
	@echo "$(BANNER)"
	@echo "[VERILATOR] Compiling Model"
	@echo "$(PROJ_ROOT_DIR)"
	$(MAKE) -C $(VERI_RESULTS_DIR)/$(VERI_WORKDIR) -f V$(VERI_CVA6_TH).mk \
	    | tee $(VERI_RESULTS_DIR)/$(VERI_WORKDIR)/$(VERI_COMPL_LOG)

verilator_run:
	@echo "$(BANNER)"
	@echo "[VERILATOR] Running Model"
	mkdir -p $(VERI_RESULTS_DIR)
	cd $(VERI_RESULTS_DIR) && \
	mkdir -p $(TEST_PROGRAM)
	cp $(VERI_RESULTS_DIR)/$(VERI_WORKDIR)/V$(VERI_CVA6_TH) $(VERI_RESULTS_DIR)/$(TEST_PROGRAM)
	cd $(VERI_RESULTS_DIR)/$(TEST_PROGRAM) && \
	./V$(VERI_CVA6_TH) $(VERI_RUNTIME_FLAGS) ${VERI_TRACE} \
	    | tee $(VERI_RUN_LOG)

verilator_all: verilator_clean verilator_comp verilator_run

###############################################################################
# Metrics DSIM specific variables, targets and rules

DSIM_CMP_FLAGS     ?=
DSIM_RUN_FLAGS     ?=
DSIM_WORK_DIR      ?= dsim_work
DSIM_IMAGE         ?= dsim.out
DSIM_RESULTS_DIR   ?= dsim_$(RESULTS_DIR)
DSIM_COMPL_LOG     ?= dsim_compl.log
DSIM_RUN_LOG       ?= $(TEST_PROGRAM).log

# User controlled wave dumping (using either "WAVE" or "WAVES"):
# By default, dump FST waves (small dumpfile, more info).
# the --trace flags to the verilator call.
ifneq (${WAVES}, 0)
  DSIM_CMP_FLAGS += +acc
  DSIM_DMP_FILE  ?= $(TEST_PROGRAM).fst
  DSIM_RUN_FLAGS += -waves $(DSIM_DMP_FILE) +disass +disass_display
endif
ifneq (${WAVE}, 0)
  DSIM_CMP_FLAGS += +acc
  DSIM_DMP_FILE  ?= $(TEST_PROGRAM).fst
  DSIM_RUN_FLAGS += -waves $(DSIM_DMP_FILE) +disass +disass_display
endif

# Delete compiler outputs, but not simulation results
dsim_clean:
	@echo "[DSIM] clean up"
	rm -rf $(DSIM_RESULTS_DIR)/$(DSIM_WORK_DIR)
	rm -rf $(DSIM_RESULTS_DIR)/dsim.env $(DSIM_RESULTS_DIR)/*.log

dsim_comp:
	@echo "$(BANNER)"
	@echo "[DSIM] Building Model"
	mkdir -p $(DSIM_RESULTS_DIR)
	dsim \
	    -timescale 1ns/1ps \
	    -sv \
	    +incdir+${UVM_HOME}/src \
	    ${UVM_HOME}/src/uvm_pkg.sv \
	    -f ${CVA6_DESIGN_HOME}/cva6_manifest.flist \
	    ${CVA6_CORE_HOME}/core_tb/cva6_core_tb.sv \
	    ${DSIM_CMP_FLAGS} \
	    -work $(DSIM_RESULTS_DIR)/$(DSIM_WORK_DIR) \
	    -genimage $(DSIM_IMAGE)
	mv dsim.env $(DSIM_RESULTS_DIR)
	mv dsim.log $(DSIM_RESULTS_DIR)

dsim_run:
	@echo "$(BANNER)"
	@echo "[DSIM] Running Model"
	mkdir -p $(DSIM_RESULTS_DIR)
	cd $(DSIM_RESULTS_DIR)  && \
	mkdir -p $(TEST_PROGRAM) && \
	cd $(TEST_PROGRAM) && \
	dsim \
	    -l $(TEST_PROGRAM).log \
	    -timescale 1ns/1ps \
	    -sv_lib ${UVM_HOME}/src/dpi/libuvm_dpi.so \
	    -image $(DSIM_IMAGE) \
	    -work ../$(DSIM_WORK_DIR) \
	    ${DSIM_RUN_FLAGS}

#	    -work $(DSIM_RESULTS_DIR)/$(DSIM_WORK_DIR) \

dsim_all: dsim_clean dsim_comp dsim_run

###############################################################################
# Common targets and rules

clean_all: dsim_clean verilator_clean
	@echo "[ALL] clean up"
	rm -rf *.log *.dasm
	rm -rf results *results*

help:
	@echo "Example targets and variables:"
	@echo "  make verilator_all <TEST_PROGRAM=test-program> <WAVES=1>"
	@echo "  make verilator_run <TEST_PROGRAM=test-program> <WAVES=1> (if you've previously compiled)"
	@echo "  make dsim_all <TEST_PROGRAM=test-program> <WAVES=1>"
