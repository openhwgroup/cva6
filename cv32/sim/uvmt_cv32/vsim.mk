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
# VSIM-specific Makefile for the CV32E40P "uvmt_cv32" testbench.
# VSIM is the Mentor Graphics Questa SystemVerilog simulator.
#
###############################################################################

USES_DPI=1

ifeq ($(USES_DPI),1)
  DPILIB_VLOG_OPT = 
  DPILIB_VSIM_OPT = -sv_lib $(UVM_HOME)/../../uvm-1.2/linux_x86_64/uvm_dpi
  DPILIB_TARGET = dpi_lib$(BITS)
else
  DPILIB_VLOG_OPT = +define+UVM_NO_DPI 
  DPILIB_VSIM_OPT = 
  DPILIB_TARGET =
endif

LIBDIR  = $(UVM_HOME)/lib
LIBNAME = uvm_dpi

VLIB      = vlib
VWORK     = work

VLOG          = vlog
VLOG_FLAGS    = -pedanticerrors -suppress 2577 -suppress 2583 \
        $(DPILIB_VLOG_OPT) \
	-timescale "1ns/1ps" \
        -mfcu \
        -suppress 2181 \
	-suppress 13262 \
        +acc=rb \
        -writetoplevels  uvmt_cv32_tb \
        +incdir+$(UVM_HOME)/src \
        $(UVM_HOME)/src/uvm.sv

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

VSIM_UVM_ARGS           = +incdir+$(UVM_HOME)/src $(UVM_HOME)/src/uvm_pkg.sv

no_rule:
	@echo 'makefile: SIMULATOR is set to $(SIMULATOR), but no rule/target specified.'
	@echo 'try "make SIMULATOR=vsim sanity" (or just "make sanity" if shell ENV variable SIMULATOR is already set).'

help:
	vsim -help

.lib-rtl:
	$(VLIB) $(VWORK)
	touch .lib-rtl


.build-rtl: .lib-rtl $(CV32E40P_PKG) $(TBSRC_PKG) $(TBSRC)
	$(VLOG) \
		-work $(VWORK) \
		$(VLOG_FLAGS) \
		+incdir+$(DV_UVME_CV32_PATH) \
		+incdir+$(DV_UVMT_CV32_PATH) \
		-f $(CV32E40P_MANIFEST) \
		-f $(DV_UVMT_CV32_PATH)/uvmt_cv32.flist \
		$(TBSRC_PKG) $(TBSRC)
		

vsim-all:  .opt-rtl
	

.opt-rtl: .build-rtl
	$(VOPT) -work $(VWORK) $(VOPT_FLAGS) $(RTLSRC_VLOG_TB_TOP) -o $(RTLSRC_VOPT_TB_TOP)
	touch .opt-rtl

# run tb and exit
.PHONY: vsim-run
vsim-run: ALL_VSIM_FLAGS += -c +UVM_TESTNAME=uvmt_cv32_firmware_test_c 
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
vsim-run-gui: ALL_VSIM_FLAGS += $(VSIM_GUI_FLAGS) +UVM_TESTNAME=uvmt_cv32_firmware_test_c +firmware=$(FIRMWARE)/firmware.hex
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

##############################################################################
# Placeholder for future testing via Google ISG (riscv-dv)
# These targets are defined in ./Makefile
corev-dv: clean_riscv-dv \
	  clone_riscv-dv

###############################################################################
# Clean up your mess!

clean:
	if [ -d $(VWORK) ]; then rm -r $(VWORK); fi
	rm -f transcript vsim.wlf vsim.dbg trace_core*.log \
	.build-rtl .opt-rtl .lib-rtl *.vcd objdump

# All generated files plus the clone of the RTL
clean_all: clean clean_core_tests
	rm -rf $(CV32E40P_PKG)
