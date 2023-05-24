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
# Makefile for the CV_CORE "core" testbench.  Substantially modified from the
# Makefile original for the RI5CY testbench.
#
###############################################################################
#
# Copyright 2019 Claire Wolf
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

# "Constants"
MAKE           = make
MAKE_DIR       = $(PWD)
MAKE_PATH     := $(shell dirname $(realpath $(firstword $(MAKEFILE_LIST))))
COREV_PROJ     = cv32
CORE_V_VERIF   = $(abspath $(MAKE_PATH)/../../..)
DATE           = $(shell date +%F)
WAVES          = 0

CV_CORE       ?= CV32E40P
CV_CORE_LC     = $(shell echo $(CV_CORE) | tr A-Z a-z)
CV_CORE_UC     = $(shell echo $(CV_CORE) | tr a-z A-Z)

SIMULATOR     ?= $(CV_SIMULATOR)

# Test-Program directores.
# Relative path is used for Verilator which cannot seem to handle loooong pathnames.
TEST_PROGRAM_PATH    = $(CORE_V_VERIF)/$(CV_CORE_LC)/tests/programs/custom
TEST_PROGRAM_RELPATH = ../../tests/programs/custom

# Common output directories
RUN_INDEX               ?= 0
SIM_RESULTS              = simulation_results
SIM_TEST_RESULTS         = $(SIM_RESULTS)/$(TEST)
SIM_RUN_RESULTS          = $(SIM_TEST_RESULTS)/$(RUN_INDEX)
SIM_TEST_PROGRAM_RESULTS = $(SIM_RUN_RESULTS)/test_program
SIM_BSP_RESULTS          = $(SIM_TEST_PROGRAM_RESULTS)/bsp

# Compile compile flags for all simulators
SV_CMP_FLAGS =

# Default "custom test-program"
CUSTOM_PROG  ?= requested_csr_por
TEST         ?= hello-world

###############################################################################
# Generate and include TEST_FLAGS_MAKE, based on the YAML test description.
# An example of what is generated is below (not all of these flags are used):
#       TEST_DESCRIPTION=Simple hello-world sanity test
#       TEST_NAME=hello-world
#       TEST_PROGRAM=hello-world
#       TEST_TEST_DIR=/home/mike/GitHubRepos/MikeOpenHWGroup/core-v-verif/master/cv32e40p/tests/programs/custom/hello-world
#       TEST_UVM_TEST=uvmt_$(CV_CORE_LC)_firmware_test_c

YAML2MAKE = $(CORE_V_VERIF)/bin/yaml2make
TEST_FLAGS_MAKE := $(shell $(YAML2MAKE) --test=$(TEST) --yaml=test.yaml  $(YAML2MAKE_DEBUG) --run-index=$(u) --prefix=TEST --core=$(CV_CORE))
ifeq ($(TEST_FLAGS_MAKE),)
$(error ERROR Could not find test.yaml for test: $(TEST))
endif
include $(TEST_FLAGS_MAKE)

###############################################################################
# Common Makefiles:
#  -Variables for RTL and other dependencies (e.g. RISCV-DV)
include ../ExternalRepos.mk
#  -Core Firmware and the RISCV GCC Toolchain (SDK)
include $(CORE_V_VERIF)/mk/Common.mk

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
VSIM_SCRIPT_DIR	  = ../tools/vsim
VSIM_SCRIPT       = $(VSIM_SCRIPT_DIR)/vsim.tcl

# vcs configuration (hopelessly out of date)
VCS_VERSION             = O-2018.09-SP1-1
VCS_HOME                = /opt/synopsys/vcs-mx/$(VCS_VERSION)
VCS                     = vcs
VCS_FLAGS              ?= # user defined
ALL_VCS_FLAGS           = $(VCS_FLAGS)
VCS_SCRIPT_DIR          = ../tools/vcs
VCS_SCRIPT              = $(VCS_SCRIPT_DIR)/vcs_batch.tcl
VCS_SCRIPT_GUI          = $(VCS_SCRIPT_DIR)/vcs.tcl
SIMV                    = ./simv

# dsim is the Metrics Technologies SystemVerilog simulator  (https://metrics.ca/)
DSIM                    = dsim
DSIM_HOME               = /tools/Metrics/dsim
DSIM_CMP_FLAGS          = +define+CORE_TB -timescale 1ns/1ps $(SV_CMP_FLAGS) -suppress MultiBlockWrite +define+CV32E40P_APU_TRACE
DSIM_RUN_FLAGS          =
DSIM_UVM_ARGS           = +incdir+$(UVM_HOME)/src $(UVM_HOME)/src/uvm_pkg.sv
DSIM_RESULTS           ?= $(PWD)/dsim_results
DSIM_WORK              ?= $(DSIM_RESULTS)/dsim_work
DSIM_IMAGE              = dsim.out

ifneq (${WAVES}, 0)
  DSIM_CMP_FLAGS += +acc
  DSIM_DMP_FILE  ?= dsim.fst
  DSIM_RUN_FLAGS += -waves $(DSIM_DMP_FILE)
endif

# xrun is the Cadence xcelium SystemVerilog simulator (https://cadence.com/)
XRUN              = xrun
XRUN_FLAGS        = -clean -smartorder -sv -top worklib.tb_top -timescale 1ns/1ps +define+CV32E40P_APU_TRACE -uvmhome CDNS-1.2-ML
XRUN_DIR          = xcelium.d

# verilator configuration
VERILATOR           = verilator
VERI_FLAGS         +=
VERI_COMPILE_FLAGS += -Wno-BLKANDNBLK $(SV_CMP_FLAGS) # hope this doesn't hurt us in the long run
VERI_TRACE         ?=
VERI_OBJ_DIR       ?= cobj_dir
#VERI_LOG_DIR       ?= cobj_dir/logs
VERI_LOG_DIR       ?= $(SIM_TEST_PROGRAM_RESULTS)
VERI_CFLAGS        += -O2

#riviera configuration

ALIB      = "vlib"
AWORK     = work

ALOG          = vlog
ALOG_DEBUG    = -dbg
ALOG_FLAGS    =
ALOG_UVM      = -uvmver 1.2

ASIM              = vsim
ASIM_HOME         = $(ALDEC_PATH)
ASIM_FLAGS       ?=  # user defined
ALL_ASIM_FLAGS    = $(ASIM_FLAGS)
ASIM_DEBUG_FLAGS  = -dbg
ASIM_GUI_FLAGS    = -gui

# TB source files for the CV32E core
TBSRC_HOME  := $(CORE_V_VERIF)/$(CV_CORE_LC)/tb
TBSRC_TOP   := $(TBSRC_HOME)/core/tb_top.sv
TBSRC_CORE  := $(TBSRC_HOME)/core
TBSRC_PKG   := $(TBSRC_CORE)/tb_riscv/include/perturbation_defines.sv
TBSRC       := $(TBSRC_CORE)/tb_top.sv \
               $(TBSRC_CORE)/cv32e40p_tb_wrapper.sv \
               $(TBSRC_CORE)/mm_ram.sv \
               $(TBSRC_CORE)/dp_ram.sv \
               $(TBSRC_CORE)/tb_riscv/riscv_random_stall.sv \
               $(TBSRC_CORE)/tb_riscv/riscv_random_interrupt_generator.sv \
               $(TBSRC_CORE)/tb_riscv/riscv_rvalid_stall.sv \
               $(TBSRC_CORE)/tb_riscv/riscv_gnt_stall.sv

#/tb_riscv/riscv_rvalid_stall.sv

RTLSRC_VLOG_TB_TOP	:= $(basename $(notdir $(TBSRC_TOP)))
RTLSRC_VOPT_TB_TOP	:= $(addsuffix _vopt, $(RTLSRC_VLOG_TB_TOP))

TBSRC_VERI  := $(TBSRC_CORE)/tb_top_verilator.sv \
               $(TBSRC_CORE)/cv32e40p_tb_wrapper.sv \
               $(TBSRC_CORE)/tb_riscv/riscv_rvalid_stall.sv \
               $(TBSRC_CORE)/tb_riscv/riscv_gnt_stall.sv \
               $(TBSRC_CORE)/mm_ram.sv \
               $(TBSRC_CORE)/dp_ram.sv
SIM_LIBS    := $(CORE_V_VERIF)/lib/sim_libs

# RTL source files for the CV32E core
# DESIGN_RTL_DIR is used by CV_CORE_MANIFEST file
CV_CORE_PKG           := $(CORE_V_VERIF)/core-v-cores/$(CV_CORE_LC)
CV_CORE_RTLSRC_INCDIR := $(CV_CORE_PKG)/rtl/include
CV_CORE_RTLSRC_PKG    := $(CV_CORE_PKG)/rtl/fpnew/src/fpnew_pkg.sv \
				$(addprefix $(CV_CORE_RTLSRC_INCDIR)/,\
				CV_CORE_apu_core_package.sv CV_CORE_defines.sv \
				CV_CORE_tracer_defines.sv)
CV_CORE_RTLSRC  := $(filter-out $(CV_CORE_PKG)/rtl/$(CV_CORE_LC)_register_file_latch.sv, \
                $(wildcard $(CV_CORE_PKG)/rtl/*.sv))
# FIXME: temporarily using a local manifest for the core.
#        This is BAD PRACTICE and will be fixed with
#        https://github.com/openhwgroup/CV_CORE/pull/421 is resolved.
CV_CORE_MANIFEST    := $(CV_CORE_PKG)/cv32e40p_manifest.flist
export DESIGN_RTL_DIR = $(CV_CORE_PKG)/rtl

# Shorthand rules for convience
CV_CORE_pkg: clone_$(CV_CORE_LC)_rtl

tbsrc_pkg: $(TBSRC_PKG)

tbsrc: $(TBSRC)

###############################################################################


.PHONY: hello-world
hello-world: $(SIMULATOR)-hello-world

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
dsim-comp: mk_results CV_CORE_pkg tbsrc_pkg tbsrc
		cd $(DSIM_RESULTS) && \
		$(DSIM) \
		$(DSIM_CMP_FLAGS) \
		$(DSIM_UVM_ARGS) \
		-f $(CV_CORE_MANIFEST) \
		$(TBSRC_PKG) \
		$(TBSRC) \
		-work $(DSIM_WORK) \
		-genimage $(DSIM_IMAGE)

dsim-comp-rtl-only: mk_results $(CV_CORE_PKG)
	$(DSIM) \
		$(DSIM_CMP_FLAGS) \
		-f $(CV_CORE_MANIFEST) \
		-work $(DSIM_WORK) \
		-genimage $(DSIM_IMAGE)


# Metrics dsim simulations
.PHONY: dsim-hello-world dsim-firmware

dsim-sanity: dsim-test

dsim-custom:
	@echo "This target is depreciated.  Please use 'make dsim-test TEST=<test-program>'"
	@echo "                             Example:   'make dsim-test TEST=fibonacci'"

dsim-test: dsim-comp $(TEST_PROGRAM_PATH)/$(TEST)/$(TEST).hex
	@echo "$(BANNER)"
	@echo "* Running with Metrics DSIM"
	@echo "$(BANNER)"
	mkdir -p $(DSIM_RESULTS)/$(TEST) && cd $(DSIM_RESULTS)/$(TEST)  && \
	$(DSIM) -l dsim-$(TEST).log \
		-image $(DSIM_IMAGE) \
		-work $(DSIM_WORK) \
		$(DSIM_RUN_FLAGS) \
		-sv_lib $(UVM_HOME)/src/dpi/libuvm_dpi.so \
		+firmware=$(VERI_CUSTOM)/$(TEST)/$(TEST).hex

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
	rm -rf $(SIM_RESULTS)

###############################################################################
# Mentor Questasim


.lib-rtl:
	$(VLIB) $(VWORK)
	touch .lib-rtl


.build-rtl: .lib-rtl $(CV_CORE_PKG) $(TBSRC_PKG) $(TBSRC)
	$(VLOG) \
		-work $(VWORK) \
		$(VLOG_FLAGS) \
		-f $(CV_CORE_MANIFEST) \
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

.PHONY: questa-custom
questa-custom: vsim-all $(CUSTOM)/$(CUSTOM_PROG)/$(CUSTOM_PROG).hex
questa-custom: ALL_VSIM_FLAGS += +firmware=$(CUSTOM)/$(CUSTOM_PROG)/$(CUSTOM_PROG).hex
questa-custom: vsim-run

.PHONY: questa-custom-gui
questa-custom-gui: vsim-all $(CUSTOM)/$(CUSTOM_PROG)/$(CUSTOM_PROG).hex
questa-custom-gui: ALL_VSIM_FLAGS += +firmware=$(CUSTOM)/$(CUSTOM_PROG)/$(CUSTOM_PROG).hex
questa-custom-gui: vsim-run-gui

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
xrun-all: $(CV_CORE_PKG) $(RTLSRC_PKG) $(RTLSRC) $(TBSRC_PKG) $(TBSRC)
	$(XRUN) \
		$(XRUN_FLAGS) \
		-f $(CV_CORE_MANIFEST) \
		$(TBSRC_PKG) $(TBSRC)

xrun-custom:
	@echo "This target is depreciated.  Please use 'make xrun-test TEST=<test-program>'"
	@echo "                             Example:   'make xrun-test TEST=fibonacci'"

.PHONY: xrun-test
xrun-test: xrun-all $(TEST_PROGRAM_PATH)/$(TEST)/$(TEST).hex
	$(XRUN) \
		$(XRUN_FLAGS) \
		-f $(CV_CORE_MANIFEST) \
		$(TBSRC_PKG) $(TBSRC) \
		+firmware=$(TEST_PROGRAM_PATH)/$(TEST)/$(TEST).hex

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
#ifeq ($(findstring +vcd,$(VERI_FLAGS)),+vcd)

ifneq (${WAVES}, 0)
VERI_TRACE="--trace"
VERI_CFLAGS+="-DVCD_TRACE"
endif

verilate: testbench_verilator

sanity-veri-run:
	make veri-test TEST=hello-world

testbench_verilator: CV_CORE_pkg $(TBSRC_VERI) $(TBSRC_PKG)
	@echo "$(BANNER)"
	@echo "* Compiling CORE TB and CV32E40P with Verilator"
	@echo "$(BANNER)"
	$(VERILATOR) --cc --sv --exe \
		$(VERI_TRACE) \
		--Wno-lint --Wno-UNOPTFLAT \
		--Wno-MODDUP --top-module \
		tb_top_verilator $(TBSRC_VERI) \
		-f $(CV_CORE_MANIFEST) \
		$(CV_CORE_PKG)/bhv/$(CV_CORE_LC)_core_log.sv \
		$(TBSRC_CORE)/tb_top_verilator.cpp --Mdir $(VERI_OBJ_DIR) \
		-CFLAGS "-std=gnu++11 $(VERI_CFLAGS)" \
		$(VERI_COMPILE_FLAGS)
	$(MAKE) -C $(VERI_OBJ_DIR) -f Vtb_top_verilator.mk
	mkdir -p $(SIM_RESULTS)
	mkdir -p $(SIM_TEST_RESULTS)
	mv $(VERI_OBJ_DIR)/Vtb_top_verilator $(SIM_TEST_RESULTS)/verilator_executable

veri-test: verilate $(TEST_PROGRAM_PATH)/$(TEST)/$(TEST).hex
	@echo "$(BANNER)"
	@echo "* Running with Verilator: logfile in $(SIM_TEST_RESULTS)/$(TEST).log"
	@echo "$(BANNER)"
	mkdir -p $(VERI_LOG_DIR)
	$(SIM_TEST_RESULTS)/verilator_executable \
		$(VERI_FLAGS) \
		"+firmware=$(TEST_PROGRAM_RELPATH)/$(TEST)/$(TEST).hex" \
		| tee $(VERI_LOG_DIR)/$(TEST).log

# verilator specific cleanup
veri-clean: verilate-clean

verilate-clean: tc-clean
	if [ -d $(SIM_RESULTS) ]; then rm -r $(SIM_RESULTS); fi
	if [ -d $(VERI_OBJ_DIR) ]; then rm -r $(VERI_OBJ_DIR); fi
	rm -rf testbench_verilator
	if [ -e memory_dump.bin ]; then rm memory_dump.bin; fi


###############################################################################
# Synopsys VCS

vcsify: CV_CORE_pkg tbsrc_pkg tbsrc
	$(VCS) +vc -sverilog -race=all -ignore unique_checks -full64 \
		-timescale=1ns/1ps \
		-assert svaext \
		-CC "-I$(VCS_HOME)/include -O3 -march=native" $(VCS_FLAGS) \
		-f $(MAKE_DIR)/$(CV_CORE_MANIFEST) \
		$(TBSRC_PKG) $(TBSRC)

RTLSRC_TB_TOP	:= $(basename $(notdir $(TBSRC_TOP)))

vcs-run: vcsify
	$(SIMV) $(ALL_VCS_FLAGS) -ucli -do $(VCS_SCRIPT)

vcs-run-gui: vcsify
	$(SIMV) $(ALL_VCS_FLAGS) -gui -do $(VCS_SCRIPT_GUI)

.PHONY: vcs-hello-world
vcs-hello-world: vcsify $(CUSTOM)/hello-world.hex
vcs-hello-world: ALL_VCS_FLAGS += +firmware=$(CUSTOM)/hello-world.hex
vcs-hello-world: vcs-run

.PHONY: vcs-custom
vcs-custom: vcsify $(CUSTOM)/$(CUSTOM_PROG).hex
vcs-custom: ALL_VCS_FLAGS += +firmware=$(CUSTOM)/$(CUSTOM_PROG).hex
vcs-custom: vcs-run

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
# Aldec Riviera-PRO

.rvrlib-rtl:
	$(ALIB) $(AWORK)
	touch .rvrlib-rtl

rvr-build-rtl: .rvrlib-rtl CV_CORE_pkg tbsrc_pkg tbsrc
	$(ALOG) \
		-work $(AWORK) \
		$(ALOG_FLAGS) \
		$(ALOG_UVM) \
		-f $(CV_CORE_MANIFEST) \
		$(TBSRC_PKG) $(TBSRC)

asim-all:  .rvr-build-rtl

# run tb and exit
.PHONY: asim-run
asim-run: ALL_ASIM_FLAGS += -c
asim-run: rvr-build-rtl
	$(ASIM) -lib $(AWORK) $(ALL_ASIM_FLAGS)\
	$(RTLSRC_VLOG_TB_TOP) -do "run -all; endsim; quit -force"

# run tb and drop into interactive shell
.PHONY: asim-run-sh
asim-run-sh: ALL_ASIM_FLAGS += -c
asim-run-sh: rvr-build-rtl
	$(ASIM) -lib $(AWORK) $(ALL_ASIM_FLAGS) \
	$(RTLSRC_VLOG_TB_TOP) -do "run -all"

# run tb with simulator gui
.PHONY: asim-run-gui
asim-run-gui: ALL_ASIM_FLAGS += $(ASIM_GUI_FLAGS)
asim-run-gui: rvr-build-rtl
	$(ASIM) -lib $(AWORK) $(ALL_ASIM_FLAGS) \
	$(RTLSRC_VLOG_TB_TOP) -do "run -all"

.PHONY: riviera-hello-world
riviera-hello-world: rvr-build-rtl $(CUSTOM)/hello-world/hello-world.hex
riviera-hello-world: ALL_ASIM_FLAGS += +firmware=$(CUSTOM)/hello-world/hello-world.hex
riviera-hello-world: asim-run

.PHONY: riviera-hello-world-gui
riviera-hello-world-gui: rvr-build-rtl $(CUSTOM)/hello-world/hello-world.hex
riviera-hello-world-gui: ALL_ASIM_FLAGS += +firmware=$(CUSTOM)/hello-world/hello-world.hex
riviera-hello-world-gui: asim-run-gui

.PHONY: riviera-custom
riviera-custom: rvr-build-rtl $(CUSTOM)/$(CUSTOM_PROG)/$(CUSTOM_PROG).hex
riviera-custom: ALL_ASIM_FLAGS += +firmware=$(CUSTOM)/$(CUSTOM_PROG)/$(CUSTOM_PROG).hex
riviera-custom: asim-run

.PHONY: riviera-custom-gui
riviera-custom-gui: rvr-build-rtl $(CUSTOM)/$(CUSTOM_PROG)/$(CUSTOM_PROG).hex
riviera-custom-gui: ALL_ASIM_FLAGS += +firmware=$(CUSTOM)/$(CUSTOM_PROG)/$(CUSTOM_PROG).hex
riviera-custom-gui: asim-run-gui

riviera-clean:
	if [ -d $(AWORK) ]; then rm -r $(AWORK); fi
	rm -f transcript trace_core*.log \
	.build-rtl .rvrlib-rtl *.vcd objdump *.asdb *.cfg dpi_header.h

###############################################################################
# CV_CORE RTL dependencies

clone_$(CV_CORE_LC)_rtl:
	@echo "$(BANNER)"
	@echo "* Cloning CV32E40P RTL model"
	@echo "$(BANNER)"
	$(CLONE_CV_CORE_CMD)




###############################################################################
# general targets
.PHONY: tc-clean

# clean up simulation results
clean-sim-results:
	rm -rf $(SIM_RESULTS)

# clean up toolchain generated files
clean-test-programs:
	find $(CORE_V_VERIF)/$(CV_CORE_LC)/tests/programs -name *.o       -exec rm {} \;
	find $(CORE_V_VERIF)/$(CV_CORE_LC)/tests/programs -name *.hex     -exec rm {} \;
	find $(CORE_V_VERIF)/$(CV_CORE_LC)/tests/programs -name *.elf     -exec rm {} \;
	find $(CORE_V_VERIF)/$(CV_CORE_LC)/tests/programs -name *.map     -exec rm {} \;
	find $(CORE_V_VERIF)/$(CV_CORE_LC)/tests/programs -name *.readelf -exec rm {} \;
	find $(CORE_V_VERIF)/$(CV_CORE_LC)/tests/programs -name *.objdump -exec rm {} \;
	find $(CORE_V_VERIF)/$(CV_CORE_LC)/tests/programs -name corev_*.S -exec rm {} \;

.PHONY: clean clean_all distclean
clean: clean-sim-results clean-test-programs questa-clean verilate-clean vcs-clean firmware-clean dsim-clean xrun-clean vcs-clean riviera-clean

distclean: clean
	rm -rf riscv-fesvr riscv-isa-sim $(CV_CORE_PKG) work

clean_all: distclean
#endend
