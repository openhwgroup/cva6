# Copyright 2021 Thales DIS design services SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Jean-Roch COULON (jean-roch.coulon@thalesgroup.fr)

mkfile_path := $(abspath $(lastword $(MAKEFILE_LIST)))
root-dir    := $(dir $(mkfile_path))

ifndef CVA6_REPO_DIR
$(warning must set CVA6_REPO_DIR to point at the root of CVA6 sources and CVA6_TB_DIR to point here -- doing it for you...)
export CVA6_REPO_DIR = $(abspath $(root-dir)../../core-v-cores/cva6/)
export CVA6_TB_DIR   = $(root-dir)/../tb/core
endif

.DEFAULT_GOAL := help

FLIST_TB   := $(CVA6_TB_DIR)/Flist.cva6_tb
ifeq ($(findstring 32, $(variant)),32)
    FLIST_CORE := $(CVA6_REPO_DIR)/core/Flist.cv32a6_imac_sv0
else
    FLIST_CORE := $(CVA6_REPO_DIR)/core/Flist.cv64a6_imafdc_sv39
endif

VERDI          ?=
user-define    ?= +define+WT_CACHE
USERDEFINE      = +define+RVFI_TRACE $(user-define)

###############################################################################
# Synopsys VCS specific commands, variables
###############################################################################
VCS                     = vcs
ALL_VLOGAN_FLAGS        = $(if $(VERDI), -kdb,) -sverilog -assert svaext $(USERDEFINE) -timescale=1ns/1ns
ALL_VCS_FLAGS           = $(if $(VERDI), -kdb -debug_access+r -lca,) -full64 -timescale=1ns/1ns
VCS_WORK_DIR            = vcs_work
SIMV                    = $(VCS_WORK_DIR)/simv

vcs_comp:
	@echo "[VCS] Building Model"
	mkdir -p $(VCS_WORK_DIR)
	cd $(VCS_WORK_DIR) && vlogan $(ALL_VLOGAN_FLAGS) -f $(FLIST_CORE)
	cd $(VCS_WORK_DIR) && vlogan $(ALL_VLOGAN_FLAGS) -f $(FLIST_TB)
	cd $(VCS_WORK_DIR) && vcs $(ALL_VCS_FLAGS) work.cva6_core_only_tb

vcs_run:
	$(VCS_WORK_DIR)/simv $(if $(VERDI), -verdi,)

vcs_clean:
	@echo "[VCS] Cleanup (entire vcs_work dir)"
	rm -rf $(VCS_WORK_DIR) simv* *.daidir *.vpd *.db csrc ucli.key vc_hdrs.h

###############################################################################
# Verilator
###############################################################################

VERILATOR             ?= verilator
ALL_VERILATOR_FLAGS   ?= -Werror-PINMISSING -Werror-IMPLICIT -Wno-fatal \
    -Wno-PINCONNECTEMPTY -Wno-ASSIGNDLY -Wno-DECLFILENAME -Wno-UNUSED \
    -Wno-UNOPTFLAT -Wno-BLKANDNBLK -Wno-style -Wall --cc  --vpi --exe \
    --Mdir $(VERILATOR_WORK_DIR) -O3 $(USERDEFINE)
VERILATOR_WORK_DIR    ?= verilator_work
VERILATOR_RESULTS_DIR ?= verilator_results

veri_comp:
	@echo "[VERILATOR] Building Model"
	$(VERILATOR) \
	    $(ALL_VERILATOR_FLAGS) --top-module cva6_core_only_tb \
		-f $(FLIST_CORE) -f $(FLIST_TB) \
		$(CVA6_TB_DIR)/cva6_tb_verilator.cpp
	@echo "[VERILATOR] Compiling Model"
	$(MAKE) -C $(VERILATOR_WORK_DIR) -f Vcva6_core_only_tb.mk

veri_clean_all:
	@echo "[VERILATOR] Cleanup (both work and results dirs)"
	rm -rf $(VERILATOR_WORK_DIR)
	rm -rf $(VERILATOR_RESULTS_DIR)

###############################################################################
# Common targets and rules
###############################################################################

clean_all: xrun_clean_all dsim_clean_all veri_clean_all


help:
	@echo "Shell environment:"
	@echo "   CVA6_REPO_DIR    : $(CVA6_REPO_DIR)"
	@echo "   CVA6_TB_DIR      : $(CVA6_TB_DIR)"
	@echo "Verilator targets:"
	@echo "   make verilate    : Builds verilator"
	@echo "   make veri_comp   : Builds and compiles verilator"
	@echo "   make veri_run    : Builds, compiles and runs"
	@echo "DSIM targets:"
	@echo "   make dsim_comp   : Compiles with DSIM"
	@echo "   make dsim_run    : Compiles and runs with DSIM"
	@echo "XRUN targets:"
	@echo "   make xrun_comp   : Compiles with XRUN"
	@echo "   make xrun_run    : Compiles and runs with XRUN"
	@echo "VCS targets:"
	@echo "   make vcs_comp    : Compiles with VCS"
	@echo "   make vcs_run     : Compiles and runs with VCS"
	@echo "   make vcs_run_gui : Compiles and runs with VCS"
	@echo "Clean-up targets:"
	@echo "   make clean_all   : Deletes ALL generated files"
	@echo "Support for other simulators on the ToDo list..."

