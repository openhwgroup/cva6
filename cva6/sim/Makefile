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
ifndef TARGET_CFG
export TARGET_CFG = $(target)
endif

.DEFAULT_GOAL := help

FLIST_TB   := $(CVA6_TB_DIR)/Flist.cva6_tb
# target takes one of the following cva6 hardware configuration:
# cv64a6_imafdc_sv39, cv32a6_imac_sv0, cv32a6_imac_sv32, cv32a6_imafc_sv32
target     ?= cv64a6_imafdc_sv39
FLIST_CORE := $(if $(gate), $(CVA6_REPO_DIR)/core/Flist.cva6_gate,$(CVA6_REPO_DIR)/core/Flist.cva6)

TRACE_FAST      ?=
TRACE_COMPACT   ?=
VERDI           ?=
path-var        ?=
tool_path       ?=
isscomp_opts    ?=
issrun_opts     ?=
isspostrun_opts ?=
log             ?=
variant         ?=

# TRACE_FAST, TRACE_COMPACT and VERDI are mutually exclusive and imply non-empty DEBUG.
ifneq ($(TRACE_FAST),)
ifneq ($(TRACE_COMPACT),)
$(error Variables TRACE_FAST and TRACE_COMPACT are mutually exclusive, please unset one of them)
endif
ifneq ($(VERDI),)
$(error Variables TRACE_FAST and VERDI are mutually exclusive, please unset one of them)
endif
DEBUG=1
endif

ifneq ($(TRACE_COMPACT),)
ifneq ($(TRACE_FAST),)
$(error Variables TRACE_COMPACT and TRACE_FAST are mutually exclusive, please unset one of them)
endif
ifneq ($(VERDI),)
$(error Variables TRACE_COMPACT and VERDI are mutually exclusive, please unset one of them)
endif
DEBUG=1
endif

ifneq ($(VERDI),)
ifneq ($(TRACE_COMPACT),)
$(error Variables VERDI and TRACE_COMPACT are mutually exclusive, please unset one of them)
endif
ifneq ($(TRACE_FAST),)
$(error Variables VERDI and TRACE_FAST are mutually exclusive, please unset one of them)
endif
DEBUG=1
endif

# Make these variables available to sub-Makefiles.
export DEBUG TRACE_FAST TRACE_COMPACT

TESTNAME := $(shell basename -s .o $(elf))

ifeq ($(isspostrun_opts), "")
grep_address:
	grep $(isspostrun_opts) ./trace_rvfi_hart_00.dasm
else
grep_address:
endif

#######################################################################################
#                   Code Coverage
#######################################################################################
#code coverage is deactivated by default
#To activate the code coverage: define the env variable cov with: (export cov=value) , to deactivate it: (unset cov) OR (export cov= )
cov-exclude-list ?= $(root-dir)/cov-exclude-mod.lst

ifdef cov
	cov-comp-opt = -cm line+cond+fsm+tgl+assert -cm_hier $(cov-exclude-list)
	cov-run-opt  = -cm line+cond+fsm+tgl+assert -cm_name $(TESTNAME)
else
	cov-comp-opt =
	cov-run-opt  =
endif

###############################################################################
# Spike specific commands, variables
###############################################################################
spike:
	$(tool_path)/spike --log-commits --isa=$(variant) -l $(elf)
	cp $(log).iss $(log)

###############################################################################
# testharness specific commands, variables
###############################################################################
vcs-testharness:
	make -C $(path_var) vcs_build target=$(target) defines=$(subst +define+,,$(isscomp_opts))
	$(path_var)/work-vcs/simv $(if $(VERDI), -verdi -do $(path_var)/init_testharness.do,) +permissive -sv_lib $(path_var)/work-dpi/ariane_dpi \
	  +tohost_addr=$(shell $$RISCV/bin/riscv-none-elf-nm -B $(elf) | grep -w tohost | cut -d' ' -f1) \
	  +PRELOAD=$(elf) +permissive-off ++$(elf) $(issrun_opts)
	$(tool_path)/spike-dasm --isa=$(variant) < ./trace_rvfi_hart_00.dasm > $(log)
	grep $(isspostrun_opts) ./trace_rvfi_hart_00.dasm

veri-testharness:
	make -C $(path_var) verilate target=$(target) defines=$(subst +define+,,$(isscomp_opts))
	$(path_var)/work-ver/Variane_testharness $(if $(TRACE_COMPACT), -f verilator.fst) $(if $(TRACE_FAST), -v verilator.vcd) $(elf) $(issrun_opts) +PRELOAD=$(elf) \
	  +tohost_addr=$(shell $$RISCV/bin/riscv-none-elf-nm -B $(elf) | grep -w tohost | cut -d' ' -f1)
	$(tool_path)/spike-dasm --isa=$(variant) < ./trace_rvfi_hart_00.dasm > $(log)
	# If present, move default trace files to per-test directory.
	[ ! -f verilator.fst ] || mv verilator.fst `dirname $(log)`/`basename $(log) .log`.$(target).fst
	[ ! -f verilator.vcd ] || mv verilator.vcd `dirname $(log)`/`basename $(log) .log`.$(target).vcd
	grep $(isspostrun_opts) ./trace_rvfi_hart_00.dasm

###############################################################################
# UVM specific commands, variables
###############################################################################
ALL_VCS_FLAGS           = $(if $(VERDI), -kdb -debug_access+all -lca,) -sverilog -full64 -timescale=1ns/1ns
VCS_WORK_DIR            = $(CORE_V_VERIF)/cva6/sim/vcs_results/default/vcs.d
SIMV                    = $(VCS_WORK_DIR)/simv

export CVA6_UVMT_DIR          = $(CORE_V_VERIF)/cva6/tb/uvmt
export CVA6_UVMT_PATH         = $(CORE_V_VERIF)/cva6/tb/uvmt
export CVA6_UVME_PATH         = $(CORE_V_VERIF)/cva6/env/uvme
export CV_CORE_LC             = cva6
export CV_CORE_UC             = CVA6
export DV_UVMT_PATH           = $(CORE_V_VERIF)/$(CV_CORE_LC)/tb/uvmt
export DV_UVME_PATH           = $(CORE_V_VERIF)/$(CV_CORE_LC)/env/uvme
export DV_UVML_HRTBT_PATH     = $(CORE_V_VERIF)/lib/uvm_libs/uvml_hrtbt
export DV_UVMA_CORE_CNTRL_PATH = $(CORE_V_VERIF)/lib/uvm_agents/uvma_core_cntrl
export DV_UVMA_ISACOV_PATH    = $(CORE_V_VERIF)/lib/uvm_agents/uvma_isacov
export DV_UVMA_CLKNRST_PATH   = $(CORE_V_VERIF)/lib/uvm_agents/uvma_clknrst
export DV_UVMA_CVXIF_PATH     = $(CORE_V_VERIF)/lib/uvm_agents/uvma_cvxif
export DV_UVMA_AXI_PATH       = $(CORE_V_VERIF)/lib/uvm_agents/uvma_axi
export DV_UVMA_INTERRUPT_PATH = $(CORE_V_VERIF)/lib/uvm_agents/uvma_interrupt
export DV_UVMA_DEBUG_PATH     = $(CORE_V_VERIF)/lib/uvm_agents/uvma_debug
export DV_UVMA_OBI_PATH       = $(CORE_V_VERIF)/lib/uvm_agents/uvma_obi
export DV_UVML_TRN_PATH       = $(CORE_V_VERIF)/lib/uvm_libs/uvml_trn
export DV_UVML_MEM_PATH       = $(CORE_V_VERIF)/lib/uvm_libs/uvml_mem
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

ALL_UVM_FLAGS           = -lca -sverilog +incdir+$(VCS_HOME)/etc/uvm/src \
	  $(VCS_HOME)/etc/uvm/src/uvm_pkg.sv +UVM_VERBOSITY=UVM_MEDIUM -ntb_opts uvm-1.2 -timescale=1ns/1ps \
	  -assert svaext -race=all -ignore unique_checks -full64 -q +incdir+$(VCS_HOME)/etc/uvm/src \
	  +incdir+$(CORE_V_VERIF)/$(CV_CORE_LC)/env/uvme +incdir+$(CORE_V_VERIF)/$(CV_CORE_LC)/tb/uvmt \
	  $(if $(DEBUG), -debug_access+all $(if $(VERDI), -kdb) $(if $(TRACE_COMPACT),+vcs+fsdbon))

ALL_SIMV_UVM_FLAGS      = -licwait 20 +ntb_random_seed=1 \
		-sv_lib $(CORE_V_VERIF)/lib/dpi_dasm/lib/Linux64/libdpi_dasm +signature=I-ADD-01.signature_output \
		+UVM_TESTNAME=uvmt_cva6_firmware_test_c

ifneq ($(DEBUG),)               # If RTL DEBUG support requested
  ifneq ($(VERDI),)             #   If VERDI interactive mode requested, use GUI and do not run simulation
  ALL_SIMV_UVM_FLAGS       += \
                 -gui -do $(CORE_V_VERIF)/cva6/sim/init_uvm.do
  else                          #   else: *not* VERDI, use CLI mode and appropriate batch dump controls
    ifneq ($(TRACE_FAST),)      #     TRACE_FAST: Generate waveform trace in VPD format
      ALL_SIMV_UVM_FLAGS   += \
                 -ucli -do $(CORE_V_VERIF)/cva6/sim/init_run_uvm_vpd.do
      SIMV_TRACE_EXTN      = vpd
    endif
    ifneq ($(TRACE_COMPACT),)   #     TRACE_COMPACT: Generate waveform trace in FSDB format
      ALL_SIMV_UVM_FLAGS   += \
                 -ucli -do $(CORE_V_VERIF)/cva6/sim/init_run_uvm_fsdb.do
      SIMV_TRACE_EXTN      = fsdb
    endif
  endif
endif

dpi-library = $(VCS_WORK_DIR)/work-dpi
dpi_build:
	mkdir -p $(dpi-library)
	g++ -shared -fPIC -std=c++0x -Bsymbolic -std=c++11 -I../corev_apu/tb/dpi -O3 -I$(SPIKE_ROOT)/include \
	-I$(VCS_HOME)/include -I$(RISCV)/include -c $(CVA6_REPO_DIR)/corev_apu/tb/dpi/elfloader.cc \
	-o $(dpi-library)/elfloader.o
	g++ -shared -m64 -o $(dpi-library)/ariane_dpi.so $(dpi-library)/elfloader.o -L$(RISCV)/lib -Wl,-rpath,$(RISCV)/lib

vcs_uvm_comp: dpi_build
	@echo "[VCS] Building Model"
	mkdir -p $(VCS_WORK_DIR)
	cd $(VCS_WORK_DIR) && vcs $(ALL_UVM_FLAGS) \
	  -f $(FLIST_CORE) -f $(FLIST_TB) \
	  -f $(CVA6_UVMT_DIR)/uvmt_cva6.flist \
	  $(cov-comp-opt) $(isscomp_opts)\
	  -top uvmt_cva6_tb

vcs_uvm_run:
	$(if $(TRACE_FAST), unset VERDI_HOME ;) \
	cd $(VCS_WORK_DIR)/ && \
	$(VCS_WORK_DIR)/simv ${ALL_SIMV_UVM_FLAGS} \
	++$(elf) \
	+PRELOAD=$(elf) \
	+tohost_addr=$(shell $$RISCV/bin/riscv-none-elf-nm -B $(elf) | grep -w tohost | cut -d' ' -f1) \
	-sv_lib $(dpi-library)/ariane_dpi \
	$(cov-run-opt) $(issrun_opts) && \
	mv $(VCS_WORK_DIR)/trace_rvfi_hart_00.dasm $(CORE_V_VERIF)/cva6/sim/ && \
	{ [ -z "`ls $(VCS_WORK_DIR)/*.$(SIMV_TRACE_EXTN)`" ] || \
	  for i in `ls $(VCS_WORK_DIR)/*.$(SIMV_TRACE_EXTN)` ; do mv $$i $(CORE_V_VERIF)/cva6/sim/`basename $$i` ; done || \
	  true ; }

vcs-uvm:
	make vcs_uvm_comp
	make vcs_uvm_run
	$(tool_path)/spike-dasm --isa=$(variant) < ./trace_rvfi_hart_00.dasm > $(log)
	grep $(isspostrun_opts) ./trace_rvfi_hart_00.dasm
	[ -z "`ls *.$(SIMV_TRACE_EXTN)`" ] || \
          for i in `ls *.$(SIMV_TRACE_EXTN)` ; do mv $$i `dirname $(log)`/`basename $(log) .log`.$(target).$$i ; done || true

generate_cov_dash:
	urg -dir $(VCS_WORK_DIR)/simv.vdb

vcs_clean_all:
	@echo "[VCS] Cleanup (entire vcs_work dir)"
	rm -rf $(CORE_V_VERIF)/cva6/sim/vcs_results/ verdiLog/ simv* *.daidir *.vpd *.fsdb *.db csrc ucli.key vc_hdrs.h novas* inter.fsdb uart

###############################################################################
# Common targets and rules
###############################################################################

clean_all: vcs_clean_all
	rm -f *.txt
	rm -f trace*.log
	rm -f trace*.dasm
	rm -f *.vpd *.fsdb *.vcd *.fst

help:
	@echo "Shell environment:"
	@echo "   CVA6_REPO_DIR    : $(CVA6_REPO_DIR)"
	@echo "   CVA6_TB_DIR      : $(CVA6_TB_DIR)"
	@echo "VCS targets:"
	@echo "   make vcs_uvm_comp    : Compiles with VCS"
	@echo "   make vcs_uvm_run     : Runs with VCS"
	@echo "Clean-up targets:"
	@echo "   make clean_all   : Deletes ALL generated files"
	@echo "Support for other simulators on the ToDo list..."
