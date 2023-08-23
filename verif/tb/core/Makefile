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
# Makefile for the CVA6 "core_only" testbench.
#
###############################################################################

mkfile_path := $(abspath $(lastword $(MAKEFILE_LIST)))
root-dir    := $(dir $(mkfile_path))

ifndef CVA6_REPO_DIR
$(warning must set CVA6_REPO_DIR to point at the root of CVA6 sources and CVA6_TB_DIR to point here -- doing it for you...)
export CVA6_REPO_DIR = $(abspath $(root-dir)../../../)
export CVA6_TB_DIR   = $(root-dir)
endif

.DEFAULT_GOAL := help

# target takes one of the following cva6 hardware configuration:
# cv64a6_imafdc_sv39, cv32a6_imac_sv0
target     ?= cv64a6_imafdc_sv39
FLIST_CORE := $(CVA6_REPO_DIR)/core/Flist.$(target)

###############################################################################
# Cadence Xcelium specific commands, variables
###############################################################################
XRUN                   ?= xrun
XRUN_COMP_FLAGS        ?= -sv -64bit -disable_sem2009 -access +rwc -timescale 1ns/1ps
XRUN_ACC_FLAGS         ?=
XRUN_DISABLED_WARNINGS ?= -nowarn UEXPSC
XRUN_UVMHOME_ARG       ?= -uvm -uvmhome CDNS-1.2-ML
XRUN_COMPL_LOG         ?= xrun_compl.log
XRUN_RUN_LOG           ?= xrun_run.log
XRUN_RESULTS_DIR       ?= xrun_results

XRUN_COMP = $(XRUN_COMP_FLAGS) \
            $(XRUN_ACC_FLAGS) \
            $(XRUN_DISABLED_WARNINGS) \
            $(XRUN_UVMHOME_ARG) \
            -l $(XRUN_COMPL_LOG) \
            -f $(FLIST_CORE) \
            -f $(CVA6_TB_DIR)/Flist.cva6_tb \
            -top cva6_core_only_tb \
            -elaborate

xrun_comp:
	@echo "[XRUN] Building Model"
	mkdir -p $(XRUN_RESULTS_DIR)
	cd $(XRUN_RESULTS_DIR) && \
	$(XRUN) $(XRUN_COMP)

xrun_run: xrun_comp
	@echo "[XRUN] Running Model"
	cd $(XRUN_RESULTS_DIR) && \
	$(XRUN) -R -xmlibdirname ./xcelium.d -l $(XRUN_RUN_LOG)

xrun_clean_all:
	@echo "[XRUN] Cleanup (entire xrun_results dir)"
	rm -rf $(XRUN_RESULTS_DIR)

###############################################################################
# dsim-specific commands, variables
###############################################################################
DSIM               ?= dsim
DSIM_HOME          ?= /tools/Metrics/dsim
DSIM_CMP_FLAGS     ?= $(TIMESCALE) -top worklib.$(top_level) -pli_lib
DSIM_WORK_DIR      ?= dsim_work
DSIM_RESULTS_DIR   ?= dsim_results
DSIM_UVMHOME_ARG   ?= +incdir+$(UVM_HOME)/src $(UVM_HOME)/src/uvm_pkg.sv
DSIM_COMPL_LOG     ?= dsim_compl.log
DSIM_RUN_LOG       ?= dsim_run.log
DSIM_IMAGE         ?= dsim.out
DSIM_ACC_FLAGS     ?= +acc
DSIM_DMP_FILE      ?= dsim.fst
DSIM_DMP_FLAGS     ?= -waves $(DSIM_DMP_FILE)

DSIM_COMP = $(DSIM_COMP_FLAGS) \
            $(DSIM_ACC_FLAGS) \
            $(DSIM_DISABLED_WARNINGS) \
            $(DSIM_UVMHOME_ARG) \
            -l $(DSIM_COMPL_LOG) \
            -genimage $(DSIM_IMAGE) \
            -f $(FLIST_CORE) \
            -f $(CVA6_TB_DIR)/Flist.cva6_tb

dsim_comp:
	@echo "[DSIM] Building Model"
	mkdir -p $(DSIM_RESULTS_DIR)
	cd $(DSIM_RESULTS_DIR) && \
	$(DSIM) $(DSIM_COMP)

dsim_run: dsim_comp
	@echo "[DSIM] Running Model"
	cd $(DSIM_RESULTS_DIR) && \
	$(DSIM) \
		$(DSIM_RUN_FLAGS) \
		$(DSIM_DMP_FLAGS) \
		-l $(DSIM_RUN_LOG) \
		-image $(DSIM_IMAGE) \
		-sv_lib $(UVM_HOME)/src/dpi/libuvm_dpi.so

dsim_clean:
	@echo "[DSIM] Cleanup (select contents of dsim_results dir)"
	cd $(DSIM_RESULTS_DIR) && \
	rm -rf $(DSIM_RESULTS_DIR) && \
	rm -rf $(DSIM_WORK_DIR) && \
	rm -f $(DSIM_IMAGE) && \
	rm -f $(DSIM_COMPL_LOG) && \
	rm -f $(DSIM_RUN_LOG) && \
	rm -f dsim.env && \
	rm -f metrics.db && \
	rm -f metrics_history.db && \
	rm -f trace_hart*.log && \
	rm -f $(DSIM_DMP_FILE) && \
	rm -f $(DSIM_DMP_FILE).hier

dsim_clean_all:
	@echo "[DSIM] Cleanup (entire dsim_results dir)"
	rm -rf $(DSIM_RESULTS_DIR)

###############################################################################
# Common targets and rules
###############################################################################

clean_all: xrun_clean_all dsim_clean_all veri_clean_all


help:
	@echo "Shell environment:"
	@echo "   CVA6_REPO_DIR  : $(CVA6_REPO_DIR)"
	@echo "   CVA6_TB_DIR    : $(CVA6_TB_DIR)"
	@echo "DSIM targets:"
	@echo "   make dsim_comp : Compiles with DSIM"
	@echo "   make dsim_run  : Compiles and runs with DSIM"
	@echo "XRUN targets:"
	@echo "   make xrun_comp : Compiles with XRUN"
	@echo "   make xrun_run  : Compiles and runs with XRUN"
	@echo "Clean-up targets:"
	@echo "   make clean_all : Deletes ALL generated files"
	@echo "Support for other simulators on the ToDo list..."

