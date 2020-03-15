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
# DSIM-specific Makefile for the CV32E40P "uvmt_cv32" testbench.
# DSIM is the Metrics Technologies SystemVerilog simulator  (https://metrics.ca/)
#
###############################################################################

DSIM                    = dsim
DSIM_HOME               = /tools/Metrics/dsim
DSIM_CMP_FLAGS          = -timescale 1ns/1ps $(SV_CMP_FLAGS)
DSIM_UVM_ARGS           = +incdir+$(UVM_HOME)/src $(UVM_HOME)/src/uvm_pkg.sv
DSIM_RESULTS           ?= $(PWD)/dsim_results
DSIM_WORK              ?= $(DSIM_RESULTS)/dsim_work
DSIM_IMAGE              = dsim.out

.DEFAULT_GOAL: no_rule 
.PHONY: sim

no_rule:
	@echo '$(SIMULATOR): no rule/target specified.'

all: clean_all hello-world

help:
	dsim -help

mk_results: 
	$(MKDIR_P) $(DSIM_RESULTS)
	$(MKDIR_P) $(DSIM_WORK)

# DSIM compile target
#      - TODO: cd $(DSIM_RESULTS) - incompatible with pkg file
comp: mk_results $(CV32E40P_PKG)
	$(DSIM) \
		$(DSIM_CMP_FLAGS) \
		$(DSIM_UVM_ARGS) \
		-sv_lib $(UVM_HOME)/src/dpi/libuvm_dpi.so \
		+incdir+$(DV_UVME_CV32_PATH) \
		+incdir+$(DV_UVMT_CV32_PATH) \
		-f $(CV32E40P_MANIFEST) \
		-f $(DV_UVMT_CV32_PATH)/uvmt_cv32.flist \
		-work $(DSIM_WORK) \
		+$(UVM_PLUSARGS) \
		-genimage $(DSIM_IMAGE)

no-firmware: comp
	mkdir -p $(DSIM_RESULTS)/hello_world && cd $(DSIM_RESULTS)/hello_world  && \
	$(DSIM) -l dsim-$(UVM_TESTNAME).log -image $(DSIM_IMAGE) \
		-work $(DSIM_WORK) $(DSIM_RUN_FLAGS) \
		-sv_lib $(UVM_HOME)/src/dpi/libuvm_dpi.so \
		+UVM_TESTNAME=$(UVM_TESTNAME)
#		+verbose

hello-world: comp $(CUSTOM)/hello_world.hex
	mkdir -p $(DSIM_RESULTS)/hello_world && cd $(DSIM_RESULTS)/hello_world  && \
	$(DSIM) -l dsim-hello_world.log -image $(DSIM_IMAGE) \
		-work $(DSIM_WORK) $(DSIM_RUN_FLAGS) \
		-sv_lib $(UVM_HOME)/src/dpi/libuvm_dpi.so \
		+UVM_TESTNAME=uvmt_cv32_firmware_test_c \
		+firmware=$(CUSTOM)/hello_world.hex
#		+verbose

# Runs tests in riscv_tests/ only
cv32-riscv-tests: comp $(CV32_RISCV_TESTS_FIRMWARE)/cv32_riscv_tests_firmware.hex
	mkdir -p $(DSIM_RESULTS)/riscv-tests && cd $(DSIM_RESULTS)/riscv-tests && \
	$(DSIM) -l dsim-riscv_tests.log -image $(DSIM_IMAGE) \
		-work $(DSIM_WORK) $(DSIM_RUN_FLAGS) \
		-sv_lib $(UVM_HOME)/src/dpi/libuvm_dpi.so \
		+UVM_TESTNAME=uvmt_cv32_firmware_test_c \
		+firmware=$(CV32_RISCV_TESTS_FIRMWARE)/cv32_riscv_tests_firmware.hex

# Runs tests in riscv_compliance_tests/ only
cv32-riscv-compliance-tests: comp $(CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE)/cv32_riscv_compliance_tests_firmware.hex
	mkdir -p $(DSIM_RESULTS)/riscv-compliance && cd $(DSIM_RESULTS)/riscv-compliance && \
	$(DSIM) -l dsim-riscv_compliance_tests.log -image $(DSIM_IMAGE) \
		-work $(DSIM_WORK) $(DSIM_RUN_FLAGS) \
		-sv_lib $(UVM_HOME)/src/dpi/libuvm_dpi.so \
		+UVM_TESTNAME=uvmt_cv32_firmware_test_c \
		+firmware=$(CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE)/cv32_riscv_compliance_tests_firmware.hex

# Runs all tests in riscv_tests/ and riscv_compliance_tests/
firmware: comp $(FIRMWARE)/firmware.hex
	mkdir -p $(DSIM_RESULTS)/firmware && cd $(DSIM_RESULTS)/firmware && \
	$(DSIM) -l dsim-firmware.log -image $(DSIM_IMAGE) \
		-work $(DSIM_WORK) \
		-sv_lib $(UVM_HOME)/src/dpi/libuvm_dpi.so \
		+UVM_TESTNAME=uvmt_cv32_firmware_test_c \
		+firmware=$(FIRMWARE)/firmware.hex

# DSIM UNIT TESTS: run each test individually.
# DO NOT INVOKE rule "dsim-firmware-unit-test" directly.   It is a support
# rule for rule "dsim-unit-test" (in included ../Common.mk).
#
# Example: to run the ADDI test `make SIMULATOR=dsim dsim-unit-test addi`
dsim-unit-test: comp
	mkdir -p $(DSIM_RESULTS)/firmware && cd $(DSIM_RESULTS)/firmware && \
	$(DSIM) -l dsim-$(UNIT_TEST).log -image $(DSIM_IMAGE) \
		-work $(DSIM_WORK) \
		-sv_lib $(UVM_HOME)/src/dpi/libuvm_dpi.so \
		+UVM_TESTNAME=uvmt_cv32_firmware_test_c \
		+firmware=$(FIRMWARE)/firmware_unit_test.hex


###############################################################################
# Clean up your mess!

# Metrics dsim cleanup
clean:
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

# All generated files plus the clone of the RTL
clean_all: clean clean_core_tests
	rm -rf $(CV32E40P_PKG)
