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
# Makefile for the CV32E40P "core" testbench.  Substantially modified from the
# Makefile original for the RI5CY testbench.
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
MAKE_DIR      = $(PWD)
PROJ_ROOT_DIR = $(PWD)/../../..

# Compile compile flags for all simulators
SV_CMP_FLAGS = 

# vsim configuration
VVERSION  = "10.7b"

VLIB      = vlib
VWORK     = work

VLOG          = vlog
VLOG_FLAGS    = -pedanticerrors -suppress 2577 -suppress 2583
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

# vcs configuration (hopelessly out of date)
VCS_VERSION             = O-2018.09-SP1-1
VCS_HOME                = /opt/synopsys/vcs-mx/$(VCS_VERSION)
VCS                     = vcs
VCS_FLAGS               ?= # user defined
ALL_VCS_FLAGS               = $(VCS_FLAGS)
VCS_SCRIPT_DIR	        = ../vcs
VCS_SCRIPT              = $(VCS_SCRIPT_DIR)/vcs_batch.tcl
VCS_SCRIPT_GUI          = $(VCS_SCRIPT_DIR)/vcs.tcl
SIMV                    = ./simv

# dsim is the Metrics Technologies SystemVerilog simulator  (https://metrics.ca/)
DSIM                    = dsim
DSIM_HOME               = /tools/Metrics/dsim
DSIM_CMP_FLAGS          = -timescale 1ns/1ps $(SV_CMP_FLAGS)
DSIM_RUN_FLAGS          = -write-sql
DSIM_UVM_ARGS           = +incdir+$(UVM_HOME)/src $(UVM_HOME)/src/uvm_pkg.sv
DSIM_RESULTS           ?= $(PWD)/results
DSIM_WORK              ?= $(DSIM_RESULTS)/dsim_work
DSIM_IMAGE              = dsim.out

ifneq (${WAVES}, 0)
  DSIM_CMP_FLAGS += +acc+b
  DSIM_DMP_FILE  ?= dsim.fst
  DSIM_RUN_FLAGS += -waves $(DSIM_DMP_FILE) +disass +disass_display
endif

# xrun is the Cadence xcelium SystemVerilog simulator (https://cadence.com/)
XRUN              = xrun
XRUN_FLAGS        = -clean -smartorder -sv -top worklib.tb_top -timescale 1ns/1ps
XRUN_DIR          = xcelium.d

# verilator configuration
VERILATOR           = verilator
VERI_FLAGS         +=
VERI_COMPILE_FLAGS += -Wno-BLKANDNBLK $(SV_CMP_FLAGS) # hope this doesn't hurt us in the long run
VERI_TRACE          =
VERI_OBJ_DIR       ?= cobj_dir
VERI_LOG_DIR       ?= cobj_dir/logs
VERI_CFLAGS        += -O2

# TB source files for the CV32E core
TBSRC_HOME  := $(PROJ_ROOT_DIR)/$(COREV_PROJ)/tb
TBSRC_TOP   := $(TBSRC_HOME)/core/tb_top.sv
TBSRC_CORE  := $(TBSRC_HOME)/core
TBSRC_PKG   := $(TBSRC_CORE)/tb_riscv/include/perturbation_defines.sv
TBSRC       := $(TBSRC_CORE)/tb_top.sv \
               $(TBSRC_CORE)/cv32e40p_tb_wrapper.sv \
               $(TBSRC_CORE)/mm_ram.sv \
               $(TBSRC_CORE)/dp_ram.sv \
               $(TBSRC_CORE)/tb_riscv/riscv_random_stall.sv \
               $(TBSRC_CORE)/tb_riscv/riscv_random_interrupt_generator.sv

RTLSRC_VLOG_TB_TOP	:= $(basename $(notdir $(TBSRC_TOP)))
RTLSRC_VOPT_TB_TOP	:= $(addsuffix _vopt, $(RTLSRC_VLOG_TB_TOP))

TBSRC_VERI  := $(TBSRC_CORE)/tb_top_verilator.sv \
               $(TBSRC_CORE)/cv32e40p_tb_wrapper.sv \
               $(TBSRC_CORE)/mm_ram.sv \
               $(TBSRC_CORE)/dp_ram.sv
SIM_LIBS    := $(PROJ_ROOT_DIR)/lib/sim_libs

# RTL source files for the CV32E core
# DESIGN_RTL_DIR is used by CV32E40P_MANIFEST file
CV32E40P_PKG         := $(PROJ_ROOT_DIR)/core-v-cores/cv32e40p
CV32E40P_RTLSRC_INCDIR  := $(CV32E40P_PKG)/rtl/include
CV32E40P_RTLSRC_PKG  := $(CV32E40P_PKG)/rtl/fpnew/src/fpnew_pkg.sv \
				$(addprefix $(CV32E40P_RTLSRC_INCDIR)/,\
				cv32e40p_apu_core_package.sv cv32e40p_defines.sv \
				cv32e40p_tracer_defines.sv)
CV32E40P_RTLSRC  := $(filter-out $(CV32E40P_PKG)/rtl/cv32e40p_register_file_latch.sv, \
                $(wildcard $(CV32E40P_PKG)/rtl/*.sv))
FPNEW_PKG            := $(CV32E40P_PKG)/rtl/fpnew
# FIXME: temporarily using a local manifest for the core.
#        This is BAD PRACTICE and will be fixed with
#        https://github.com/openhwgroup/cv32e40p/pull/421 is resolved.
#CV32E40P_MANIFEST    := $(CV32E40P_PKG)/cv32e40p_manifest.flist
CV32E40P_MANIFEST    := cv32e40p_temp_manifest.flist
export DESIGN_RTL_DIR = $(CV32E40P_PKG)/rtl

# Shorthand rules for convience
cv32e40p_pkg: $(CV32E40P_PKG)

tbsrc_pkg: $(TBSRC_PKG)

tbsrc: $(TBSRC)

###############################################################################

SIMULATOR ?= vcs

.PHONY: hello_world
hello-world: $(SIMULATOR)-hello_world

.PHONY: cv32_riscv_tests
cv32_riscv_tests: $(SIMULATOR)-cv32_riscv_tests

.PHONY: cv32_riscv_tests-gui
cv32_riscv_tests-gui: $(SIMULATOR)-cv32_riscv_tests-gui

.PHONY: cv32_riscv_compliance_tests
cv32_riscv_compliance_tests: $(SIMULATOR)-cv32_riscv_compliance_tests

.PHONY: cv32_riscv_compliance_tests-gui
cv32_riscv_compliance_tests-gui: $(SIMULATOR)-cv32_riscv_compliance_tests-gui

.PHONY: firmware
firmware: $(SIMULATOR)-firmware

.PHONY: firmware-gui
firmware-gui: $(SIMULATOR)-firmware-gui

.PHONY: unit-test
unit-test: $(SIMULATOR)-unit-test

.PHONY: unit-test-gui
unit-test-gui: $(SIMULATOR)-unit-test-gui

###############################################################################
# Common Makefile:
#    - Core Firmware and the RISCV GCC Toolchain (SDK)
#    - Variables for RTL dependencies
include $(PROJ_ROOT_DIR)/cv32/sim/Common.mk


# assume verilator if no target chosen
.DEFAULT_GOAL := sanity-veri-run

all: clean_all sanity-veri-run dsim-sanity

###############################################################################
# Metrics DSIM 
.PHONY: dsim-comp dsim-comp-rtl-only

MKDIR_P = mkdir -p

mk_results: 
	$(MKDIR_P) $(DSIM_RESULTS)
	$(MKDIR_P) $(DSIM_WORK)

# Metrics dsim compile targets
dsim-comp: mk_results cv32e40p_pkg tbsrc_pkg tbsrc
		cd $(DSIM_RESULTS) && \
		$(DSIM) \
		$(DSIM_CMP_FLAGS) \
		$(DSIM_UVM_ARGS) \
		-f $(MAKE_DIR)/$(CV32E40P_MANIFEST) \
		$(TBSRC_PKG) \
		$(TBSRC) \
		-work $(DSIM_WORK) \
		-genimage $(DSIM_IMAGE)

dsim-comp-rtl-only: mk_results $(CV32E40P_PKG)
	$(DSIM) \
		$(DSIM_CMP_FLAGS) \
		-f $(CV32E40P_MANIFEST) \
		-work $(DSIM_WORK) \
		-genimage $(DSIM_IMAGE)


# Metrics dsim simulations
.PHONY: dsim-hello_world dsim-cv32_riscv_tests dsim-cv32_riscv_compliance_tests dsim-firmware

dsim-sanity: dsim-hello_world

# Runs the hello world test
dsim-hello_world: dsim-comp $(CUSTOM)/hello_world.hex
	mkdir -p $(DSIM_RESULTS)/hello_world && cd $(DSIM_RESULTS)/hello_world  && \
	$(DSIM) -l dsim-hello_world.log -image $(DSIM_IMAGE) \
		-work $(DSIM_WORK) $(DSIM_RUN_FLAGS) \
		-sv_lib $(UVM_HOME)/src/dpi/libuvm_dpi.so \
		-sv_lib $(OVP_MODEL_DPI)  \
		+firmware=$(CUSTOM)/hello_world.hex \
		+elf_file=$(CUSTOM)/hello_world.elf \
		+nm_file=$(CUSTOM)/hello_world.nm
#		+verbose

# Runs tests in riscv_tests/ only
dsim-cv32_riscv_tests: dsim-comp $(CV32_RISCV_TESTS_FIRMWARE)/cv32_riscv_tests_firmware.hex
	mkdir -p $(DSIM_RESULTS)/riscv-tests && cd $(DSIM_RESULTS)/riscv-tests && \
	$(DSIM) -l dsim-riscv_tests.log -image $(DSIM_IMAGE) \
		-work $(DSIM_WORK) $(DSIM_RUN_FLAGS) \
		-sv_lib $(UVM_HOME)/src/dpi/libuvm_dpi.so \
		-sv_lib $(OVP_MODEL_DPI)  \
		+firmware=$(CV32_RISCV_TESTS_FIRMWARE)/cv32_riscv_tests_firmware.hex \
		+elf_file=$(CV32_RISCV_TESTS_FIRMWARE)/cv32_riscv_tests_firmware.elf \
		+nm_file=$(CV32_RISCV_TESTS_FIRMWARE)/cv32_riscv_tests_firmware.nm

# Runs tests in riscv_compliance_tests/ only
dsim-cv32_riscv_compliance_tests: dsim-comp $(CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE)/cv32_riscv_compliance_tests_firmware.hex
	mkdir -p $(DSIM_RESULTS)/riscv-compliance && cd $(DSIM_RESULTS)/riscv-compliance && \
	$(DSIM) -l dsim-riscv_compliance_tests.log -image $(DSIM_IMAGE) \
		-work $(DSIM_WORK) $(DSIM_RUN_FLAGS) \
		-sv_lib $(UVM_HOME)/src/dpi/libuvm_dpi.so \
		-sv_lib $(OVP_MODEL_DPI)  \
		+firmware=$(CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE)/cv32_riscv_compliance_tests_firmware.hex \
		+elf_file=$(CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE)/cv32_riscv_compliance_tests_firmware.elf \
		+nm_file=$(CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE)/cv32_riscv_compliance_tests_firmware.nm

# Runs all tests in riscv_tests/ and riscv_compliance_tests/
dsim-firmware: dsim-comp $(FIRMWARE)/firmware.hex
	mkdir -p $(DSIM_RESULTS)/firmware && cd $(DSIM_RESULTS)/firmware && \
	$(DSIM) -l dsim-firmware.log -image $(DSIM_IMAGE) \
		-work $(DSIM_WORK) \
		-sv_lib $(UVM_HOME)/src/dpi/libuvm_dpi.so \
		-sv_lib $(OVP_MODEL_DPI)  \
		+firmware=$(FIRMWARE)/firmware.hex \
		+elf_file=$(FIRMWARE)/firmware.elf \
		+nm_file=$(FIRMWARE)/firmware.nm

# Runs a "unit-test" (see rule dsim-unit-test in ../Common.mk)
dsim-firmware-unit-test: dsim-comp
	mkdir -p $(DSIM_RESULTS)/firmware && cd $(DSIM_RESULTS)/firmware && \
	$(DSIM) -l dsim-$(UNIT_TEST).log -image $(DSIM_IMAGE) \
		-work $(DSIM_WORK) \
		-sv_lib $(UVM_HOME)/src/dpi/libuvm_dpi.so \
		-sv_lib $(OVP_MODEL_DPI)  \
		+firmware=$(FIRMWARE)/firmware_unit_test.hex \
		+elf_file=$(FIRMWARE)/firmware_unit_test.elf \
		+nm_file=$(FIRMWARE)/firmware_unit_test.nm

# Metrics dsim cleanup
.PHONY: dsim-clean

dsim-clean: tc-clean
	rm -f dsim.log
	rm -f dsim-*.log
	rm -f metrics_history.db
	rm -f metrics.xml
	rm -f trace_core_00_0.log
	rm -rf dsim_work
	rm -f dsim.env
	rm -f $(DSIM_IMAGE)
	rm -rf $(DSIM_RESULTS)

###############################################################################
# Mentor Questasim


.lib-rtl:
	$(VLIB) $(VWORK)
	touch .lib-rtl


.build-rtl: .lib-rtl $(CV32E40P_PKG) $(TBSRC_PKG) $(TBSRC)
	$(VLOG) \
		-work $(VWORK) \
		$(VLOG_FLAGS) \
		-f $(CV32E40P_MANIFEST) \
		$(TBSRC_PKG) $(TBSRC) 
		

vsim-all:  .opt-rtl
	

.opt-rtl: .build-rtl
	$(VOPT) -work $(VWORK) $(VOPT_FLAGS) $(RTLSRC_VLOG_TB_TOP) -o $(RTLSRC_VOPT_TB_TOP)
	touch .opt-rtl

# run tb and exit
.PHONY: vsim-run
vsim-run: ALL_VSIM_FLAGS += -c  
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
vsim-run-gui: ALL_VSIM_FLAGS += $(VSIM_GUI_FLAGS) 
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

questa-clean:
	if [ -d $(VWORK) ]; then rm -r $(VWORK); fi
	rm -f transcript vsim.wlf vsim.dbg trace_core*.log \
	.build-rtl .opt-rtl .lib-rtl *.vcd objdump

###############################################################################
# Cadence Xcelium xrun testbench compilation
.PHONY: xrun-all
xrun-all: $(CV32E40P_PKG) $(FPNEW_PKG) $(RTLSRC_PKG) $(RTLSRC) $(TBSRC_PKG) $(TBSRC)
	$(XRUN) \
		$(XRUN_FLAGS) \
		-f $(CV32E40P_MANIFEST) \
		$(TBSRC_PKG) $(TBSRC)

.PHONY: xrun-hello_world xrun-firmware
xrun-hello_world: xrun-all $(CUSTOM)/hello_world.hex
	$(XRUN) \
		$(XRUN_FLAGS) \
		-f $(CV32E40P_MANIFEST) \
		$(TBSRC_PKG) $(TBSRC) \
		+firmware=$(CUSTOM)/hello_world.hex

xrun-firmware: xrun-all $(FIRMWARE)/firmware.hex
	$(XRUN) \
		$(XRUN_FLAGS) \
		-f $(CV32E40P_MANIFEST) \
		$(TBSRC_PKG) $(TBSRC) \
		+firmware=$(FIRMWARE)/firmware.hex

# Cadence Xcelium xrun cleanup
.PHONY: xrun-clean xrun-clean-all
xrun-clean:
	rm -vrf $(XRUN_DIR)
	if [ -e xrun.history ]; then rm xrun.history; fi
	if [ -e xrun.log ]; then rm xrun.log; fi

xrun-clean-all: xrun-clean
	rm -vrf $(addprefix $(FIRMWARE)/firmware., elf bin hex map) \
		$(FIRMWARE_OBJS) $(FIRMWARE_TEST_OBJS) $(COMPLIANCE_TEST_OBJS)

###############################################################################
# Verilator

# We first test if the user wants to to vcd dumping. This hacky part is required
# because we need to conditionally compile the testbench (-DVCD_TRACE) and pass
# the --trace flags to the verilator call
ifeq ($(findstring +vcd,$(VERI_FLAGS)),+vcd)
VERI_TRACE="--trace"
VERI_CFLAGS+="-DVCD_TRACE"
endif

verilate: testbench_verilator

sanity-veri-run:
	make custom CUSTOM_PROG=hello_world

testbench_verilator: $(CV32E40P_PKG) $(TBSRC_VERI) $(TBSRC_PKG)
	$(VERILATOR) --cc --sv --exe \
		$(VERI_TRACE) \
		--Wno-lint --Wno-UNOPTFLAT \
		--Wno-MODDUP --top-module \
		tb_top_verilator $(TBSRC_VERI) \
		-f $(CV32E40P_MANIFEST) \
		$(TBSRC_CORE)/tb_top_verilator.cpp --Mdir $(VERI_OBJ_DIR) \
		-CFLAGS "-std=gnu++11 $(VERI_CFLAGS)" \
		$(VERI_COMPILE_FLAGS)
	$(MAKE) -C $(VERI_OBJ_DIR) -f Vtb_top_verilator.mk
	cp $(VERI_OBJ_DIR)/Vtb_top_verilator testbench_verilator

custom: verilate $(VERI_CUSTOM)/$(CUSTOM_PROG).hex
	mkdir -p $(VERI_LOG_DIR)
	./testbench_verilator $(VERI_FLAGS) \
		"+firmware=$(VERI_CUSTOM)/$(CUSTOM_PROG).hex" \
		| tee $(VERI_LOG_DIR)/$(CUSTOM_PROG).log

cv32-riscv-tests: verilate ../../tests/core/cv32_riscv_tests_firmware/cv32_riscv_tests_firmware.hex
	mkdir -p $(VERI_LOG_DIR)
	./testbench_verilator $(VERI_FLAGS) \
		"+firmware=../../tests/core/cv32_riscv_tests_firmware/cv32_riscv_tests_firmware.hex" \
		| tee $(VERI_LOG_DIR)/$(cv32-riscv-tests).log


# verilator specific cleanup
veri-clean: verilate-clean

verilate-clean: tc-clean
	if [ -d $(VERI_LOG_DIR) ]; then rm -r $(VERI_LOG_DIR); fi
	if [ -d $(VERI_OBJ_DIR) ]; then rm -r $(VERI_OBJ_DIR); fi
	rm -rf testbench_verilator
	if [ -e memory_dump.bin ]; then rm memory_dump.bin; fi


###############################################################################
# Synopsys VCS

vcsify: $(CV32E40P_PKG) $(FPNEW_PKG) $(CV32E40P_RTLSRC_PKG) $(CV32E40P_RTLSRC) $(TBSRC_PKG) $(TBSRC)
	$(VCS) +vc -sverilog -race=all -ignore unique_checks -full64 \
		-timescale=1ns/1ps \
		-assert svaext \
		-CC "-I$(VCS_HOME)/include -O3 -march=native" $(VCS_FLAGS) \
		$(CV32E40P_RTLSRC_PKG) $(CV32E40P_RTLSRC) $(TBSRC_PKG) $(TBSRC) \
		+incdir+$(CV32E40P_RTLSRC_INCDIR)

RTLSRC_TB_TOP	:= $(basename $(notdir $(TBSRC_TOP)))

vcs-run: vcsify
	$(SIMV) $(ALL_VCS_FLAGS) -ucli -do $(VCS_SCRIPT)

vcs-run-gui: vcsify
	$(SIMV) $(ALL_VCS_FLAGS) -gui -do $(VCS_SCRIPT_GUI)

.PHONY: vcs-hello_world
vcs-hello_world: vcsify $(CUSTOM)/hello_world.hex
vcs-hello_world: ALL_VCS_FLAGS += +firmware=$(CUSTOM)/hello_world.hex
vcs-hello_world: vcs-run

.PHONY: vcs-cv32_riscv_tests
vcs-cv32_riscv_tests: vcsify $(CV32_RISCV_TESTS_FIRMWARE)/cv32_riscv_tests_firmware.hex
vcs-cv32_riscv_tests: ALL_VCS_FLAGS += +firmware=$(CV32_RISCV_TESTS_FIRMWARE)/cv32_riscv_tests_firmware.hex
vcs-cv32_riscv_tests: vcs-run

.PHONY: vcs-cv32_riscv_tests-gui
vcs-cv32_riscv_tests-gui: vcsify $(CV32_RISCV_TESTS_FIRMWARE)/cv32_riscv_tests_firmware.hex
vcs-cv32_riscv_tests-gui: ALL_VCS_FLAGS += +firmware=$(CV32_RISCV_TESTS_FIRMWARE)/cv32_riscv_tests_firmware.hex
vcs-cv32_riscv_tests-gui: vcs-run-gui

.PHONY: vcs-cv32_riscv_compliance_tests
vcs-cv32_riscv_compliance_tests: vcsify $(CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE)/cv32_riscv_compliance_tests_firmware.hex
vcs-cv32_riscv_compliance_tests: ALL_VCS_FLAGS += +firmware=$(CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE)/cv32_riscv_compliance_tests_firmware.hex
vcs-cv32_riscv_compliance_tests: vcs-run

.PHONY: vcs-cv32_riscv_compliance_tests-gui
vcs-cv32_riscv_compliance_tests-gui: vcsify $(CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE)/cv32_riscv_compliance_tests_firmware.hex
vcs-cv32_riscv_compliance_tests-gui: ALL_VCS_FLAGS += +firmware=$(CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE)/cv32_riscv_compliance_tests_firmware.hex
vcs-cv32_riscv_compliance_tests-gui: vcs-run-gui

.PHONY: vcs-firmware
vcs-firmware: vcsify $(FIRMWARE)/firmware.hex
vcs-firmware: ALL_VCS_FLAGS += +firmware=$(FIRMWARE)/firmware.hex
vcs-firmware: vcs-run

.PHONY: vcs-firmware-gui
vcs-firmware-gui: vcsify $(FIRMWARE)/firmware.hex
vcs-firmware-gui: ALL_VCS_FLAGS += +firmware=$(FIRMWARE)/firmware.hex
vcs-firmware-gui: vcs-run-gui

.PHONY: vcs-unit-test 
vcs-unit-test:  firmware-unit-test-clean 
vcs-unit-test:  $(FIRMWARE)/firmware_unit_test.hex 
vcs-unit-test: ALL_VCS_FLAGS += "+firmware=$(FIRMWARE)/firmware_unit_test.hex"
vcs-unit-test: vcs-run

.PHONY: vcs-unit-test-gui 
vcs-unit-test-gui:  firmware-unit-test-clean 
vcs-unit-test-gui:  $(FIRMWARE)/firmware_unit_test.hex 
vcs-unit-test-gui: ALL_VCS_FLAGS += "+firmware=$(FIRMWARE)/firmware_unit_test.hex"
vcs-unit-test-gui: vcs-run-gui

vcs-clean:
	rm -rf simv* *.daidir *.vpd *.db csrc ucli.key vc_hdrs.h

###############################################################################
# CV32E40P RTL dependencies

clone_cv32e40p_rtl:
	$(CLONE_CV32E40P_CMD)

clone_fpnew_rtl: clone_cv32e40p_rtl
	$(CLONE_FPNEW_CMD)

$(CV32E40P_PKG):
	$(CLONE_CV32E40P_CMD)
	$(CLONE_FPNEW_CMD)


###############################################################################
# general targets
.PHONY: tc-clean
	
# clean up toolchain generated files (CORE_TEST_DIR defined in ../Common.mk)
tc-clean:
	find $(CORE_TEST_DIR) -name *.o       -exec rm {} \;
	find $(CORE_TEST_DIR) -name *.hex     -exec rm {} \;
	find $(CORE_TEST_DIR) -name *.elf     -exec rm {} \;
	find $(CORE_TEST_DIR) -name *.readelf -exec rm {} \;
	find $(CORE_TEST_DIR) -name *.objdump -exec rm {} \;
	find $(CORE_TEST_DIR) -name *.map     -exec rm {} \;

.PHONY: clean clean_all distclean
clean: questa-clean tc-clean verilate-clean vcs-clean firmware-clean custom-clean dsim-clean xrun-clean vcs-clean

distclean: clean
	rm -rf riscv-fesvr riscv-isa-sim $(CV32E40P_PKG) work

clean_all: distclean
#endend
