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
# original from the RI5CY testbench.
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
#ROOT_DIR      = $(PWD)
COREV_PROJ    = cv32
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
VSIM_SCRIPT       = vsim.tcl

# vcs configuration (hopelessly out of date)
VCS               = vcs-2017.03-kgf vcs
VCS_HOME          = /usr/pack/vcs-2017.03-kgf 
VCS_FLAGS         =
SIMV_FLAGS        =

# dsim is the Metrics Technologies SystemVerilog simulator  (https://metrics.ca/)
DSIM                    = dsim
DSIM_HOME               = /tools/Metrics/dsim
DSIM_CMP_FLAGS          = -timescale 1ns/1ps $(SV_CMP_FLAGS)
DSIM_RUN_FLAGS          = -write-sql
DSIM_UVM_ARGS           = +incdir+$(UVM_HOME)/src $(UVM_HOME)/src/uvm_pkg.sv
DSIM_RESULTS           ?= $(PWD)/results
DSIM_WORK              ?= $(DSIM_RESULTS)/dsim_work
DSIM_IMAGE               = dsim.out
ifneq (${WAVES}, 0)
	DSIM_CMP_FLAGS = -timescale 1ns/1ps +acc+b
	DSIM_RUN_FLAGS = -write-xml -waves waves.vcd -wave-scope-specs $(PWD)/dsim-waves-spec
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
VERI_CFLAGS         = -O2

# TB source files for the CV32E core
TBSRC_HOME  := $(PROJ_ROOT_DIR)/$(COREV_PROJ)/tb
TBSRC_PKG   := $(TBSRC_HOME)/tb_riscv/include/perturbation_defines.sv
TBSRC_TOP   := $(TBSRC_HOME)/core/tb_top.sv
TBSRC_CORE  := $(TBSRC_HOME)/core
TBSRC       := $(TBSRC_CORE)/tb_top.sv \
               $(TBSRC_CORE)/riscv_wrapper.sv \
               $(TBSRC_CORE)/mm_ram.sv \
               $(TBSRC_CORE)/dp_ram.sv \
               $(TBSRC_HOME)/tb_riscv/riscv_random_stall.sv \
               $(TBSRC_HOME)/tb_riscv/riscv_random_interrupt_generator.sv
TBSRC_VERI  := $(TBSRC_CORE)/tb_top_verilator.sv \
               $(TBSRC_CORE)/riscv_wrapper.sv \
               $(TBSRC_CORE)/mm_ram.sv \
               $(TBSRC_CORE)/dp_ram.sv
SIM_LIBS    := $(PROJ_ROOT_DIR)/lib/sim_libs

# RTL source files for the CV32E core
CV32E40P_PKG  := $(PROJ_ROOT_DIR)/core-v-cores/cv32e40p
CV32E40P_MANIFEST := $(CV32E40P_PKG)/cv32e40p_manifest.flist
export DESIGN_RTL_DIR = $(CV32E40P_PKG)/rtl

RTLSRC_HOME   := $(CV32E40P_PKG)/rtl
FPNEW_PKG     := $(RTLSRC_HOME)/fpnew
RTLSRC_INCDIR := $(RTLSRC_HOME)/include
RTLSRC_PKG    := $(FPNEW_PKG)/src/fpnew_pkg.sv \
                 $(addprefix $(RTLSRC_HOME)/include/,\
                   apu_core_package.sv \
                   riscv_defines.sv \
                   riscv_tracer_defines.sv)
RTLSRC        := $(filter-out $(RTLSRC_HOME)/riscv_register_file_latch.sv,\
                   $(wildcard $(RTLSRC_HOME)/*.sv))

###############################################################################
# Common Makefile:
#    - Core Firmware and the RISCV GCC Toolchain (SDK)
#    - Variables for RTL dependencies
include ../Common.mk


###############################################################################
# TODO: clean this up
RTLSRC_VLOG_TB_TOP	:= $(basename $(notdir $(TBSRC_TOP)))
RTLSRC_VOPT_TB_TOP	:= $(addsuffix _vopt, $(RTLSRC_VLOG_TB_TOP))

# assume verilator if no target chosen
.DEFAULT_GOAL := firmware-veri-run

all: firmware-veri-run

# vsim testbench compilation and optimization
vlib: .lib-rtl

.lib-rtl:
	$(VLIB) $(VWORK)
	touch .lib-rtl

# rebuild if we change some sourcefile
.build-rtl: .lib-rtl $(RTLSRC_PKG) $(RTLSRC) $(TBSRC_PKG) $(TBSRC)
	$(VLOG) -work $(VWORK) +incdir+$(RTLSRC_INCDIR) $(VLOG_FLAGS) \
	$(RTLSRC_PKG) $(RTLSRC) $(TBSRC_PKG) $(TBSRC)
	touch .build-rtl

vsim-all: $(CV32E40P_PKG) .opt-rtl

.opt-rtl: .build-rtl
	$(VOPT) -work $(VWORK) $(VOPT_FLAGS) $(RTLSRC_VLOG_TB_TOP) -o \
	$(RTLSRC_VOPT_TB_TOP)
	touch .opt-rtl

.PHONY: dpiheader
dpiheader: .build-tb
	$(VLOG) -work $(VWORK) -l $(VLOG_LOG) -dpiheader $(DPINAME) $(DPISRC)

# vcs testbench compilation

vcsify: $(CV32E40P_PKG) $(FPNEW_PKG) $(RTLSRC_PKG) $(RTLSRC) $(TBSRC_PKG) $(TBSRC)
	$(VCS) +vc -sverilog -race=all -ignore unique_checks -full64 \
		-timescale=1ns/1ps \
		-CC "-I$(VCS_HOME)/include -O3 -march=native" $(VCS_FLAGS) \
		$(RTLSRC_PKG) $(RTLSRC) $(TBSRC_PKG) $(TBSRC) \
		+incdir+$(RTLSRC_INCDIR)

vcs-run: vcsify $(FIRMWARE)/firmware.hex
	./simv $(SIMV_FLAGS)

vcs-run-gui: VCS_FLAGS+=-debug_all
vcs-run-gui: vcsify $(FIRMWARE)/firmware.hex
	./simv $(SIMV_FLAGS) -gui

vcs-clean:
	rm -rf simv* *.daidir *.vpd *.db csrc ucli.key vc_hdrs.h

# Metrics dsim testbench compilation 
.PHONY: dsimify dsimify-rtl-only

MKDIR_P = mkdir -p

mk_results: 
	$(MKDIR_P) $(DSIM_RESULTS)
	$(MKDIR_P) $(DSIM_WORK)

dsimify: mk_results $(CV32E40P_PKG) $(FPNEW_PKG) $(RTLSRC_PKG) $(RTLSRC) $(TBSRC_PKG) $(TBSRC)
	cd $(DSIM_RESULTS) && $(DSIM) \
		$(DSIM_CMP_FLAGS) \
		$(DSIM_UVM_ARGS) \
		$(RTLSRC_PKG) $(RTLSRC) $(TBSRC_PKG) $(TBSRC) \
		+incdir+$(RTLSRC_INCDIR) \
		-sv_lib $(UVM_HOME)/src/dpi/libuvm_dpi.so \
		-work $(DSIM_WORK) \
		-genimage $(DSIM_IMAGE)

dsimify-rtl-only: mk_results $(RTLSRC_PKG) $(RTLSRC)
	$(DSIM) \
		$(DSIM_CMP_FLAGS) \
		$(RTLSRC_PKG) $(RTLSRC) \
		-work $(DSIM_WORK) \
		+incdir+$(RTLSRC_INCDIR) \
		-genimage $(DSIM_IMAGE)

dsim-comp: mk_results $(CV32E40P_PKG) $(TBSRC_PKG) $(TBSRC)
	cd $(DSIM_RESULTS) && $(DSIM) \
		$(DSIM_CMP_FLAGS) \
		$(DSIM_UVM_ARGS) \
		$(TBSRC_PKG) $(TBSRC) \
		-f $(CV32E40P_MANIFEST) \
		-sv_lib $(UVM_HOME)/src/dpi/libuvm_dpi.so \
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

# Runs the hello world test
dsim-hello_world: dsimify $(CUSTOM)/hello_world.hex
	mkdir -p $(DSIM_RESULTS)/hello_world && cd $(DSIM_RESULTS)/hello_world  && \
	$(DSIM) -l dsim-hello_world.log -image $(DSIM_IMAGE) \
		-work $(DSIM_WORK) $(DSIM_RUN_FLAGS) \
		-sv_lib $(UVM_HOME)/src/dpi/libuvm_dpi.so \
		+firmware=$(CUSTOM)/hello_world.hex
#		+verbose

# Runs tests in riscv_tests/ only
dsim-cv32_riscv_tests: dsimify $(CV32_RISCV_TESTS_FIRMWARE)/cv32_riscv_tests_firmware.hex
	mkdir -p $(DSIM_RESULTS)/riscv-tests && cd $(DSIM_RESULTS)/riscv-tests && \
	$(DSIM) -l dsim-riscv_tests.log -image $(DSIM_IMAGE) \
		-work $(DSIM_WORK) $(DSIM_RUN_FLAGS) \
		-sv_lib $(UVM_HOME)/src/dpi/libuvm_dpi.so \
		+firmware=$(ROOT_DIR)/$(CV32_RISCV_TESTS_FIRMWARE)/cv32_riscv_tests_firmware.hex

# Runs tests in riscv_compliance_tests/ only
dsim-cv32_riscv_compliance_tests: dsimify $(CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE)/cv32_riscv_compliance_tests_firmware.hex
	mkdir -p $(DSIM_RESULTS)/riscv-compliance && cd $(DSIM_RESULTS)/riscv-compliance && \
	$(DSIM) -l dsim-riscv_compliance_tests.log -image $(DSIM_IMAGE) \
		-work $(DSIM_WORK) $(DSIM_RUN_FLAGS) \
		-sv_lib $(UVM_HOME)/src/dpi/libuvm_dpi.so \
		+firmware=$(ROOT_DIR)/$(CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE)/cv32_riscv_compliance_tests_firmware.hex

# Runs all tests in riscv_tests/ and riscv_compliance_tests/
dsim-firmware: dsimify $(FIRMWARE)/firmware.hex
	mkdir -p $(DSIM_RESULTS)/firmware && cd $(DSIM_RESULTS)/firmware && \
	$(DSIM) -l dsim-firmware.log -image $(DSIM_IMAGE) \
		-work $(DSIM_WORK) \
		-sv_lib $(UVM_HOME)/src/dpi/libuvm_dpi.so \
		+firmware=$(ROOT_DIR)/$(FIRMWARE)/firmware.hex

# Runs a "unit-test" (see rule dsim-unit-test)
dsim-firmware-unit-test: dsimify
	mkdir -p $(DSIM_RESULTS)/firmware && cd $(DSIM_RESULTS)/firmware && \
	$(DSIM) -l dsim-$(UNIT_TEST).log -image $(DSIM_IMAGE) \
		-work $(DSIM_WORK) \
		-sv_lib $(UVM_HOME)/src/dpi/libuvm_dpi.so \
		+firmware=$(ROOT_DIR)/$(FIRMWARE)/firmware_unit_test.hex

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

# Cadence Xcelium xrun testbench compilation
.PHONY: xrun-all
xrun-all: $(CV32E40P_PKG) $(FPNEW_PKG) $(RTLSRC_PKG) $(RTLSRC) $(TBSRC_PKG) $(TBSRC)
	$(XRUN) \
		$(XRUN_FLAGS) \
		$(RTLSRC_PKG) $(RTLSRC) $(TBSRC_PKG) $(TBSRC) \
		+incdir+$(RTLSRC_INCDIR)
.PHONY: xrun-hello_world xrun-firmware
xrun-hello_world: xrun-all $(CUSTOM)/hello_world.hex
	$(XRUN) \
		$(XRUN_FLAGS) \
		$(RTLSRC_PKG) $(RTLSRC) $(TBSRC_PKG) $(TBSRC) \
		+incdir+$(RTLSRC_INCDIR) +firmware=$(CUSTOM)/hello_world.hex
xrun-firmware: xrun-all $(FIRMWARE)/firmware.hex
	$(XRUN) \
		$(XRUN_FLAGS) \
		$(RTLSRC_PKG) $(RTLSRC) $(TBSRC_PKG) $(TBSRC) \
		+incdir+$(RTLSRC_INCDIR) +firmware=$(FIRMWARE)/firmware.hex

# Cadence Xcelium xrun cleanup
.PHONY: xrun-clean xrun-clean-all
xrun-clean:
	rm -vrf $(XRUN_DIR)
xrun-clean-all: xrun-clean
	rm -vrf $(addprefix $(FIRMWARE)/firmware., elf bin hex map) \
		$(FIRMWARE_OBJS) $(FIRMWARE_TEST_OBJS) $(COMPLIANCE_TEST_OBJS)

# verilator testbench compilation

# We first test if the user wants to to vcd dumping. This hacky part is required
# because we need to conditionally compile the testbench (-DVCD_TRACE) and pass
# the --trace flags to the verilator call
ifeq ($(findstring +vcd,$(VERI_FLAGS)),+vcd)
VERI_TRACE="--trace"
VERI_CFLAGS+="-DVCD_TRACE"
endif

verilate: testbench_verilator

testbench_verilator: $(CV32E40P_PKG) $(FPNEW_PKG) $(TBSRC_VERI) $(RTLSRC_PKG) $(RTLSRC)
	$(VERILATOR) --cc --sv --exe \
		$(VERI_TRACE) \
		--Wno-lint --Wno-UNOPTFLAT \
		--Wno-MODDUP +incdir+$(RTLSRC_INCDIR) --top-module \
		tb_top_verilator $(TBSRC_VERI) $(RTLSRC_PKG) $(RTLSRC) \
		$(TBSRC_CORE)/tb_top_verilator.cpp --Mdir $(VERI_OBJ_DIR) \
		-CFLAGS "-std=gnu++11 $(VERI_CFLAGS)" \
		$(VERI_COMPILE_FLAGS)
	$(MAKE) -C $(VERI_OBJ_DIR) -f Vtb_top_verilator.mk
	cp $(VERI_OBJ_DIR)/Vtb_top_verilator testbench_verilator

veri-clean: verilate-clean

verilate-clean: tc-clean
	if [ -d $(VERI_LOG_DIR) ]; then rm -r $(VERI_LOG_DIR); fi
	if [ -d $(VERI_OBJ_DIR) ]; then rm -r $(VERI_OBJ_DIR); fi
	rm -rf testbench_verilator
	if [ -e memory_dump.bin ]; then rm memory_dump.bin; fi

# CV32E40P RTL dependencies
# The variables RTLSRC_PKG and RTLSRC need to be re-evaluated since
# CV32E40P_PKG was null the first time.
# TODO: cmd to eval RTLSRC needs to be replaced with a manifest (flist)
clone_cv32e40p_rtl:
	$(CLONE_CV32E40P_CMD)

clone_fpnew_rtl: clone_cv32e40p_rtl
	$(CLONE_FPNEW_CMD)

$(CV32E40P_PKG):
	$(CLONE_CV32E40P_CMD)
	$(CLONE_FPNEW_CMD)
	$(eval RTLSRC_HOME   = $(CV32E40P_PKG)/rtl)
	$(eval RTLSRC_PKG = $(FPNEW_PKG)/src/fpnew_pkg.sv \
	                    $(addprefix $(RTLSRC_HOME)/include/,\
	                      apu_core_package.sv \
	                      riscv_defines.sv \
	                      riscv_tracer_defines.sv))
	$(eval RTLSRC = $(RTLSRC_HOME)/riscv_alu_div.sv \
                  $(RTLSRC_HOME)/cv32e40p_sim_clock_gating.sv \
                  $(RTLSRC_HOME)/riscv_controller.sv \
                  $(RTLSRC_HOME)/riscv_ex_stage.sv \
                  $(RTLSRC_HOME)/riscv_id_stage.sv \
                  $(RTLSRC_HOME)/riscv_load_store_unit.sv \
                  $(RTLSRC_HOME)/riscv_prefetch_L0_buffer.sv \
                  $(RTLSRC_HOME)/riscv_alu.sv \
                  $(RTLSRC_HOME)/riscv_core.sv \
                  $(RTLSRC_HOME)/riscv_fetch_fifo.sv \
                  $(RTLSRC_HOME)/riscv_if_stage.sv \
                  $(RTLSRC_HOME)/riscv_mult.sv \
                  $(RTLSRC_HOME)/register_file_test_wrap.sv \
                  $(RTLSRC_HOME)/riscv_apu_disp.sv \
                  $(RTLSRC_HOME)/riscv_cs_registers.sv \
                  $(RTLSRC_HOME)/riscv_hwloop_controller.sv \
                  $(RTLSRC_HOME)/riscv_int_controller.sv \
                  $(RTLSRC_HOME)/riscv_pmp.sv \
                  $(RTLSRC_HOME)/riscv_register_file.sv \
                  $(RTLSRC_HOME)/riscv_alu_basic.sv \
                  $(RTLSRC_HOME)/riscv_compressed_decoder.sv \
                  $(RTLSRC_HOME)/riscv_decoder.sv \
                  $(RTLSRC_HOME)/riscv_hwloop_regs.sv \
                  $(RTLSRC_HOME)/riscv_L0_buffer.sv \
                  $(RTLSRC_HOME)/riscv_prefetch_buffer.sv \
                  $(RTLSRC_HOME)/riscv_tracer.sv)


# general targets
.PHONY: tc-clean  # clean up toolchain generated files
tc-clean:
	find $(CORE_TEST_DIR) -name *.o   -exec rm {} \;
	find $(CORE_TEST_DIR) -name *.hex -exec rm {} \;
	find $(CORE_TEST_DIR) -name *.elf -exec rm {} \;
	find $(CORE_TEST_DIR) -name *.map -exec rm {} \;

.PHONY: clean clean_all distclean
clean: tb-clean tc-clean verilate-clean vcs-clean firmware-clean custom-clean dsim-clean xrun-clean

distclean: clean
	rm -rf riscv-fesvr riscv-isa-sim $(CV32E40P_PKG) work

clean_all: distclean
#endend
