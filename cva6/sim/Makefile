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
export CORE_V_VERIF  = $(root-dir)/../..
endif

.DEFAULT_GOAL := help

FLIST_TB   := $(CVA6_TB_DIR)/Flist.cva6_tb
# target takes one of the following cva6 hardware configuration:
# cv64a6_imafdc_sv39, cv32a6_imac_sv0, cv32a6_imac_sv32, cv32a6_imafc_sv32
target     ?= cv64a6_imafdc_sv39
FLIST_CORE := $(CVA6_REPO_DIR)/core/Flist.$(target)

VERDI          ?=
user-define    ?= +define+WT_CACHE
USERDEFINE      = +define+RVFI_TRACE $(user-define)

###############################################################################
# Synopsys VCS specific commands, variables
###############################################################################
VCS                     = vcs
ALL_VLOGAN_FLAGS        = $(if $(VERDI), -kdb,) -sverilog -assert svaext $(USERDEFINE) -timescale=1ns/1ns
ALL_VCS_FLAGS           = $(if $(VERDI), -kdb -debug_access+r -lca,) -full64 -timescale=1ns/1ns
VCS_WORK_DIR            = $(CORE_V_VERIF)/cva6/sim/vcs_results/default/vcs.d
SIMV                    = $(VCS_WORK_DIR)/simv

vcs_core_comp:
	@echo "[VCS] Building Model"
	mkdir -p $(VCS_WORK_DIR)
	cd $(VCS_WORK_DIR) && vlogan $(ALL_VLOGAN_FLAGS) -f $(FLIST_CORE)
	cd $(VCS_WORK_DIR) && vlogan $(ALL_VLOGAN_FLAGS) -f $(FLIST_TB)
	cd $(VCS_WORK_DIR) && vcs $(ALL_VCS_FLAGS) work.cva6_core_only_tb

vcs_core_run:
	$(VCS_WORK_DIR)/simv $(if $(VERDI), -verdi,)

export CVA6_UVMT_DIR          = $(CORE_V_VERIF)/cva6/tb/uvmt
export CVA6_UVMT_PATH         = $(CORE_V_VERIF)/cva6/tb/uvmt
export CVA6_UVME_PATH         = $(CORE_V_VERIF)/cva6/env/uvme
export CV_CORE_LC             = cva6
export CV_CORE_UC             = CVA6
export DV_UVMT_PATH           = $(CORE_V_VERIF)/$(CV_CORE_LC)/tb/uvmt
export DV_UVME_PATH           = $(CORE_V_VERIF)/$(CV_CORE_LC)/env/uvme
export DV_UVML_HRTBT_PATH     = $(CORE_V_VERIF)/lib/uvm_libs/uvml_hrtbt
export DV_UVMA_ISACOV_PATH    = $(CORE_V_VERIF)/lib/uvm_agents/uvma_isacov
export DV_UVMA_CLKNRST_PATH   = $(CORE_V_VERIF)/lib/uvm_agents/uvma_clknrst
export DV_UVMA_INTERRUPT_PATH = $(CORE_V_VERIF)/lib/uvm_agents/uvma_interrupt
export DV_UVMA_DEBUG_PATH     = $(CORE_V_VERIF)/lib/uvm_agents/uvma_debug
export DV_UVMA_OBI_PATH       = $(CORE_V_VERIF)/lib/uvm_agents/uvma_obi
export DV_UVML_TRN_PATH       = $(CORE_V_VERIF)/lib/uvm_libs/uvml_trn
export DV_UVML_LOGS_PATH      = $(CORE_V_VERIF)/lib/uvm_libs/uvml_logs
export DV_UVML_SB_PATH        = $(CORE_V_VERIF)/lib/uvm_libs/uvml_sb
export CV_CORE_PKG            = $(CORE_V_VERIF)/core-v-cores/$(CV_CORE_LC)
export DESIGN_RTL_DIR         = $(CV_CORE_PKG)/rtl

DPI_DASM_PKG                  = $(CORE_V_VERIF)/lib/dpi_dasm
DPI_DASM_SPIKE_PKG            = $(CORE_V_VERIF)/$(CV_CORE_LC)/vendor_lib/dpi_dasm_spike
export DPI_DASM_ROOT          = $(DPI_DASM_PKG)
export DPI_DASM_SPIKE_ROOT    = $(DPI_DASM_SPIKE_PKG)
export TBSRC_HOME             = $(CORE_V_VERIF)/cva6/tb
export DV_OVPM_HOME           = $(CORE_V_VERIF)/$(CV_CORE_LC)/vendor_lib/imperas
export DV_OVPM_MODEL          = $(DV_OVPM_HOME)/riscv_$(CV_CORE_UC)_OVPsim
export DV_OVPM_DESIGN         = $(DV_OVPM_HOME)/design

ALL_UVM_FLAGS           = -lca -sverilog +incdir+/opt/synopsys/vcs-mx/O-2018.09-SP1-1/etc/uvm/src \
	  /opt/synopsys/vcs-mx/O-2018.09-SP1-1/etc/uvm/src/uvm_pkg.sv +UVM_VERBOSITY=UVM_MEDIUM -ntb_opts uvm-1.2 -timescale=1ns/1ps \
	  -assert svaext -race=all -ignore unique_checks -full64 -q +incdir+/opt/synopsys/vcs-mx/O-2018.09-SP1-1/etc/uvm/src \
	  +incdir+$(CORE_V_VERIF)/$(CV_CORE_LC)/env/uvme +incdir+$(CORE_V_VERIF)/$(CV_CORE_LC)/tb/uvmt \
	  $(USERDEFINE) $(if $(VERDI), -debug_access+all -kdb,)
ALL_SIMV_UVM_FLAGS      = -licwait 20 -l vcs-hello-world.log -cm_name hello-world +ntb_random_seed=1 \
		-sv_lib $(CORE_V_VERIF)/lib/dpi_dasm/lib/Linux64/libdpi_dasm +signature=I-ADD-01.signature_output \
		+UVM_TESTNAME=uvmt_cva6_firmware_test_c $(if $(VERDI), -gui,)

vcs_uvm_comp:
	@echo "[VCS] Building Model"
	mkdir -p $(VCS_WORK_DIR)
	cd $(VCS_WORK_DIR) && vcs $(ALL_UVM_FLAGS) \
	  -f $(FLIST_CORE) \
	  -f $(CVA6_TB_DIR)/Flist.cva6_tb \
	  -f $(CVA6_UVMT_DIR)/uvmt_cva6.flist \
	  -top uvmt_cva6_tb

vcs_uvm_run:
	cp Mem_init.txt $(VCS_WORK_DIR)/
	cd $(VCS_WORK_DIR)/ && \
	$(VCS_WORK_DIR)/simv ${ALL_SIMV_UVM_FLAGS} \
		+elf_file=$(CORE_V_VERIF)/cva6/sim/hello-world.elf \
		+firmware=$(CORE_V_VERIF)/cva6/sim/hello-world.hex && \
	mv $(VCS_WORK_DIR)/trace_rvfi_hart_00.dasm $(CORE_V_VERIF)/cva6/sim/

vcs_clean_all:
	@echo "[VCS] Cleanup (entire vcs_work dir)"
	rm -rf $(CORE_V_VERIF)/cva6/sim/vcs_results/ verdiLog/ simv* *.daidir *.vpd *.db csrc ucli.key vc_hdrs.h novas* inter.fsdb uart

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

clean_all: vcs_clean_all veri_clean_all
	rm -f Mem_init.txt
	rm -f trace*.log
	rm -f trace*.dasm

help:
	@echo "Shell environment:"
	@echo "   CVA6_REPO_DIR    : $(CVA6_REPO_DIR)"
	@echo "   CVA6_TB_DIR      : $(CVA6_TB_DIR)"
	@echo "Verilator targets:"
	@echo "   make veri_comp   : Builds, compiles and runs with verilator"
	@echo "VCS targets:"
	@echo "   make vcs_core_comp    : Compiles with VCS"
	@echo "   make vcs_core_run     : Runs with VCS"
	@echo "Clean-up targets:"
	@echo "   make clean_all   : Deletes ALL generated files"
	@echo "Support for other simulators on the ToDo list..."

