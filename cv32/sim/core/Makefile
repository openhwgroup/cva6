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

MAKE      = make
WAVES     = 0
ROOT_DIR  = $(PWD)

# Compile compile flags for all simulators
SV_CMP_FLAGS = +define+__USE_COREV_SIMULATION_MODELS__ # workaround for https://github.com/openhwgroup/cv32e40p/issues/208

# vsim configuration
VVERSION  = "10.7b"

VLIB      = vlib-$(VVERSION)
VWORK     = work

VLOG          = vlog-$(VVERSION)
VLOG_FLAGS    = -pedanticerrors -suppress 2577 -suppress 2583
VLOG_LOG      = vloggy

VOPT          = vopt-$(VVERSION)
VOPT_FLAGS    = -debugdb -fsmdebug -pedanticerrors +acc #=mnprft

VSIM              = vsim-$(VVERSION)
VSIM_HOME         = /usr/pack/modelsim-$(VVERSION)-kgf/questasim
VSIM_FLAGS       ?=  # user defined
ALL_VSIM_FLAGS    = $(VSIM_FLAGS)
VSIM_DEBUG_FLAGS  = -debugdb
VSIM_GUI_FLAGS    = -gui -debugdb
VSIM_SCRIPT       = vsim.tcl

# vcs configuration
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
TBSRC_HOME  := $(ROOT_DIR)/../../tb
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
SIM_LIBS    := $(ROOT_DIR)/../../../lib/sim_libs

# RTL source files for the CV32E core
CV32E40P_PKG  := $(ROOT_DIR)/../../../core-v-cores/cv32e40p
RTLSRC_HOME   := $(CV32E40P_PKG)/rtl
FPNEW_PKG     := $(RTLSRC_HOME)/fpnew
RTLSRC_INCDIR := $(RTLSRC_HOME)/include
RTLSRC_PKG    := $(FPNEW_PKG)/src/fpnew_pkg.sv \
                 $(SIM_LIBS)/cluster_clock_gating.sv \
                 $(addprefix $(RTLSRC_HOME)/include/,\
                   apu_core_package.sv \
                   riscv_defines.sv \
                   riscv_tracer_defines.sv)
RTLSRC        := $(filter-out $(RTLSRC_HOME)/riscv_register_file_latch.sv,\
                   $(wildcard $(RTLSRC_HOME)/*.sv))

# TODO: clean this up
RTLSRC_VLOG_TB_TOP	:= $(basename $(notdir $(TBSRC_TOP)))
RTLSRC_VOPT_TB_TOP	:= $(addsuffix _vopt, $(RTLSRC_VLOG_TB_TOP))

# riscv toolchain install path
RISCV                   ?= ~/.riscv
RISCV_EXE_PREFIX         = $(RISCV)/bin/riscv32-unknown-elf-

# firmware vars
# TODO: clean this mess up!
CORE_TEST_DIR                        = ../../tests/core
FIRMWARE                             = $(CORE_TEST_DIR)/firmware
CUSTOM                               = $(CORE_TEST_DIR)/custom
CV32_RISCV_TESTS_FIRMWARE            = $(CORE_TEST_DIR)/cv32_riscv_tests_firmware
CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE = $(CORE_TEST_DIR)/cv32_riscv_compliance_tests_firmware
RISCV_TESTS                          = $(CORE_TEST_DIR)/riscv_tests
RISCV_COMPLIANCE_TESTS               = $(CORE_TEST_DIR)/riscv_compliance_tests
RISCV_TEST_INCLUDES                  = -I$(CORE_TEST_DIR)/riscv_tests/ \
																			 -I$(CORE_TEST_DIR)/riscv_tests/macros/scalar \
                                       -I$(CORE_TEST_DIR)/riscv_tests/rv64ui \
																			 -I$(CORE_TEST_DIR)/riscv_tests/rv64um
CV32_RISCV_TESTS_FIRMWARE_OBJS       = $(addprefix $(CV32_RISCV_TESTS_FIRMWARE)/, \
                                         start.o print.o sieve.o multest.o stats.o)
CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE_OBJS = $(addprefix $(CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE)/, \
                                              start.o print.o sieve.o multest.o stats.o)
RISCV_TESTS_OBJS         = $(addsuffix .o, \
                             $(basename $(wildcard $(RISCV_TESTS)/rv32ui/*.S)) \
                             $(basename $(wildcard $(RISCV_TESTS)/rv32um/*.S)) \
                             $(basename $(wildcard $(RISCV_TESTS)/rv32uc/*.S)))
FIRMWARE_OBJS            = $(addprefix $(FIRMWARE)/, \
                             start.o print.o sieve.o multest.o stats.o)
FIRMWARE_TEST_OBJS       = $(addsuffix .o, \
                             $(basename $(wildcard $(RISCV_TESTS)/rv32ui/*.S)) \
                             $(basename $(wildcard $(RISCV_TESTS)/rv32um/*.S)) \
                             $(basename $(wildcard $(RISCV_TESTS)/rv32uc/*.S)))
FIRMWARE_SHORT_TEST_OBJS = $(addsuffix .o, \
                             $(basename $(wildcard $(RISCV_TESTS)/rv32ui/*.S)) \
                             $(basename $(wildcard $(RISCV_TESTS)/rv32um/*.S)))
COMPLIANCE_TEST_OBJS     = $(addsuffix .o, \
                             $(basename $(wildcard $(RISCV_COMPLIANCE_TESTS)/*.S)))

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

vsim-all: .opt-rtl

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

vcs-run: vcsify firmware/firmware.hex
	./simv $(SIMV_FLAGS)

vcs-run-gui: VCS_FLAGS+=-debug_all
vcs-run-gui: vcsify firmware/firmware.hex
	./simv $(SIMV_FLAGS) -gui

vcs-clean:
	rm -rf simv* *.daidir *.vpd *.db csrc ucli.key vc_hdrs.h

# Metrics dsim testbench compilation 
.PHONY: dsimify dsimify-rtl-only

MKDIR_P = mkdir -p

mk_results: 
	$(MKDIR_P) $(DSIM_RESULTS)
	$(MKDIR_P) $(DSIM_WORK)

#	cd $(DSIM_RESULTS) && $(DSIM)
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

# Metrics dsim simulations
.PHONY: dsim-hello_world dsim-cv32_riscv_tests dsim-cv32_riscv_compliance_tests dsim-firmware

# Runs the hello world test
dsim-hello_world: dsimify $(CUSTOM)/hello_world.hex
	mkdir -p $(DSIM_RESULTS)/hello_world && cd $(DSIM_RESULTS)/hello_world  && \
	$(DSIM) -l dsim-hello_world.log -image $(DSIM_IMAGE) \
		-work $(DSIM_WORK) $(DSIM_RUN_FLAGS) \
		-sv_lib $(UVM_HOME)/src/dpi/libuvm_dpi.so \
		+firmware=$(ROOT_DIR)/$(CUSTOM)/hello_world.hex
#		+verbose +firmware=$(ROOT_DIR)/$(CUSTOM)/hello_world.hex

# Runs tests in riscv_tests/ only
dsim-cv32_riscv_tests: dsimify $(CV32_RISCV_TESTS_FIRMWARE)/cv32_riscv_tests_firmware.hex
	mkdir -p $(DSIM_RESULTS)/riscv-tests && cd $(DSIM_RESULTS)/riscv-tests && \
	$(DSIM) -l dsim-riscv_tests.log -image $(DSIM_IMAGE) \
		-work $(DSIM_WORK) $(DSIM_RUN_FLAGS) \
		+firmware=$(ROOT_DIR)/$(CV32_RISCV_TESTS_FIRMWARE)/cv32_riscv_tests_firmware.hex

# Runs tests in riscv_compliance_tests/ only
dsim-cv32_riscv_compliance_tests: dsimify $(CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE)/cv32_riscv_compliance_tests_firmware.hex
	mkdir -p $(DSIM_RESULTS)/riscv-compliance && cd $(DSIM_RESULTS)/riscv-compliance && \
	$(DSIM) -l dsim-riscv_compliance_tests.log -image $(DSIM_IMAGE) \
		-work $(DSIM_WORK) $(DSIM_RUN_FLAGS) \
		+firmware=$(ROOT_DIR)/$(CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE)/cv32_riscv_compliance_tests_firmware.hex

# Runs all tests in riscv_tests/ and riscv_compliance_tests/
dsim-firmware: dsimify $(FIRMWARE)/firmware.hex
	mkdir -p $(DSIM_RESULTS)/firmware && cd $(DSIM_RESULTS)/firmware && \
	$(DSIM) -l dsim-firmware.log -image $(DSIM_IMAGE) \
		-work $(DSIM_WORK) \
		+firmware=$(ROOT_DIR)/$(FIRMWARE)/firmware.hex

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
$(CV32E40P_PKG):
	git clone https://github.com/openhwgroup/cv32e40p --recurse $(CV32E40P_PKG)
	git clone https://github.com/pulp-platform/fpnew --recurse $(FPNEW_PKG)
	$(eval RTLSRC_HOME   = $(CV32E40P_PKG)/rtl)
	$(eval RTLSRC_PKG = $(FPNEW_PKG)/src/fpnew_pkg.sv \
	                    $(SIM_LIBS)/cluster_clock_gating.sv \
	                    $(addprefix $(RTLSRC_HOME)/include/,\
	                      apu_core_package.sv \
	                      riscv_defines.sv \
	                      riscv_tracer_defines.sv))
	$(eval RTLSRC = $(RTLSRC_HOME)/riscv_alu_div.sv \
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
	
	echo $(RTLSRC_PKG)
	echo $(RTLSRC)

# run tb and exit
.PHONY: vsim-run
vsim-run: ALL_VSIM_FLAGS += -c
vsim-run: vsim-all
	$(VSIM) -work $(VWORK) $(ALL_VSIM_FLAGS) \
	$(RTLSRC_VOPT_TB_TOP) -do 'source $(VSIM_SCRIPT); exit -f'

# run tb and drop into interactive shell
.PHONY: vsim-run-sh
vsim-run-sh: ALL_VSIM_FLAGS += -c
vsim-run-sh: vsim-all
	$(VSIM) -work $(VWORK) $(ALL_VSIM_FLAGS) \
	$(RTLSRC_VOPT_TB_TOP) -do $(VSIM_SCRIPT)

# run tb with simulator gui
.PHONY: vsim-run-gui
vsim-run-gui: ALL_VSIM_FLAGS += $(VSIM_GUI_FLAGS)
vsim-run-gui: vsim-all
	$(VSIM) -work $(VWORK) $(ALL_VSIM_FLAGS) \
	$(RTLSRC_VOPT_TB_TOP) -do $(VSIM_SCRIPT)

.PHONY: tb-clean
tb-clean:
	if [ -d $(VWORK) ]; then rm -r $(VWORK); fi
	rm -f transcript vsim.wlf vsim.dbg trace_core*.log \
	.build-rtl .opt-rtl .lib-rtl *.vcd objdump

# rules to generate hex (loadable by simulators) from elf
%.hex: %.elf
	$(RISCV_EXE_PREFIX)objcopy -O verilog $< $@

# Running custom programs:
# This is an example for running a hello world in the testbench
# We link with our custom crt0.s and syscalls.c against newlib so that we can
# use the c standard library
$(CUSTOM)/hello_world.elf: $(CUSTOM)/hello_world.c
	$(RISCV_EXE_PREFIX)gcc -march=rv32imc -o $@ -w -Os -g -nostdlib \
		-T $(CUSTOM)/link.ld  \
		-static \
		$(CUSTOM)/crt0.S \
		$^ $(CUSTOM)/syscalls.c $(CUSTOM)/vectors.S \
		-I $(RISCV)/riscv32-unknown-elf/include \
		-L $(RISCV)/riscv32-unknown-elf/lib \
		-lc -lm -lgcc
custom-clean:
	rm -rf $(CUSTOM)/hello_world.elf $(CUSTOM)/hello_world.hex

.PHONY: custom-vsim-run
custom-vsim-run: vsim-all $(CUSTOM)/hello_world.hex
custom-vsim-run: ALL_VSIM_FLAGS += "+firmware=$(CUSTOM)/hello_world.hex"
custom-vsim-run: vsim-run

.PHONY: custom-vsim-run-gui
custom-vsim-run-gui: vsim-all $(CUSTOM)/hello_world.hex
custom-vsim-run-gui: ALL_VSIM_FLAGS += "+firmware=$(CUSTOM)/hello_world.hex"
custom-vsim-run-gui: vsim-run-gui


.PHONY: custom-veri-run
custom-veri-run: verilate $(CUSTOM)/hello_world.hex
	mkdir -p $(VERI_LOG_DIR)
	./testbench_verilator $(VERI_FLAGS) \
		"+firmware=$(CUSTOM)/hello_world.hex" \
		| tee $(VERI_LOG_DIR)/$(CUSTOM)-veri-run.log

# compile and dump RISCV_TESTS only
$(CV32_RISCV_TESTS_FIRMWARE)/cv32_riscv_tests_firmware.elf: $(CV32_RISCV_TESTS_FIRMWARE_OBJS) $(RISCV_TESTS_OBJS) \
							$(CV32_RISCV_TESTS_FIRMWARE)/link.ld
	$(RISCV_EXE_PREFIX)gcc -g -Os -march=rv32imc -ffreestanding -nostdlib -o $@ \
		$(RISCV_TEST_INCLUDES) \
		-Wl,-Bstatic,-T,$(CV32_RISCV_TESTS_FIRMWARE)/link.ld,-Map,$(CV32_RISCV_TESTS_FIRMWARE)/cv32_riscv_tests_firmware.map,--strip-debug \
		$(CV32_RISCV_TESTS_FIRMWARE_OBJS) $(RISCV_TESTS_OBJS) -lgcc

$(CV32_RISCV_TESTS_FIRMWARE)/start.o: $(CV32_RISCV_TESTS_FIRMWARE)/start.S
	$(RISCV_EXE_PREFIX)gcc -c -march=rv32imc -g -o $@ $<

$(CV32_RISCV_TESTS_FIRMWARE)/%.o: $(CV32_RISCV_TESTS_FIRMWARE)/%.c
	$(RISCV_EXE_PREFIX)gcc -c -march=rv32ic -g -Os --std=c99 -Wall \
		$(RISCV_TEST_INCLUDES) \
		-ffreestanding -nostdlib -o $@ $<

# compile and dump RISCV_COMPLIANCE_TESTS only
$(CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE)/cv32_riscv_compliance_tests_firmware.elf: $(CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE_OBJS) $(COMPLIANCE_TEST_OBJS) \
							$(CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE)/link.ld
	$(RISCV_EXE_PREFIX)gcc -g -Os -march=rv32imc -ffreestanding -nostdlib -o $@ \
		-D RUN_COMPLIANCE \
		$(RISCV_TEST_INCLUDES) \
		-Wl,-Bstatic,-T,$(CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE)/link.ld,-Map,$(CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE)/cv32_riscv_compliance_tests_firmware.map,--strip-debug \
		$(CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE_OBJS) $(COMPLIANCE_TEST_OBJS) -lgcc

$(CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE)/start.o: $(CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE)/start.S
	$(RISCV_EXE_PREFIX)gcc -c -march=rv32imc -D RUN_COMPLIANCE -g -o $@ $<

$(CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE)/%.o: $(CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE)/%.c
	$(RISCV_EXE_PREFIX)gcc -c -march=rv32ic -g -Os --std=c99 -Wall \
		$(RISCV_TEST_INCLUDES) \
		-ffreestanding -nostdlib -o $@ $<

# compile and dump picorv firmware
$(FIRMWARE)/firmware.elf: $(FIRMWARE_OBJS) $(FIRMWARE_TEST_OBJS) $(COMPLIANCE_TEST_OBJS) \
				$(FIRMWARE)/link.ld
	$(RISCV_EXE_PREFIX)gcc -g -Os -march=rv32imc -ffreestanding -nostdlib -o $@ \
		$(RISCV_TEST_INCLUDES) \
		-D RUN_COMPLIANCE \
		-Wl,-Bstatic,-T,$(FIRMWARE)/link.ld,-Map,$(FIRMWARE)/firmware.map,--strip-debug \
		$(FIRMWARE_OBJS) $(FIRMWARE_TEST_OBJS) $(COMPLIANCE_TEST_OBJS) -lgcc

$(FIRMWARE)/start.o: $(FIRMWARE)/start.S
	$(RISCV_EXE_PREFIX)gcc -c -march=rv32imc -g -D RUN_COMPLIANCE -o $@ $<

$(FIRMWARE)/%.o: $(FIRMWARE)/%.c
	$(RISCV_EXE_PREFIX)gcc -c -march=rv32ic -g -Os --std=c99 -Wall \
		$(RISCV_TEST_INCLUDES) \
		-ffreestanding -nostdlib -o $@ $<

$(RISCV_TESTS)/rv32ui/%.o: $(RISCV_TESTS)/rv32ui/%.S $(RISCV_TESTS)/riscv_test.h \
			$(RISCV_TESTS)/macros/scalar/test_macros.h
	$(RISCV_EXE_PREFIX)gcc -c -march=rv32im -g -o $@ \
		$(RISCV_TEST_INCLUDES) \
		-DTEST_FUNC_NAME=$(notdir $(basename $<)) \
		-DTEST_FUNC_TXT='"$(notdir $(basename $<))"' \
		-DTEST_FUNC_RET=$(notdir $(basename $<))_ret $<

$(RISCV_TESTS)/rv32um/%.o: $(RISCV_TESTS)/rv32um/%.S $(RISCV_TESTS)/riscv_test.h \
			$(RISCV_TESTS)/macros/scalar/test_macros.h
	$(RISCV_EXE_PREFIX)gcc -c -march=rv32im -g -o $@ \
		$(RISCV_TEST_INCLUDES) \
		-DTEST_FUNC_NAME=$(notdir $(basename $<)) \
		-DTEST_FUNC_TXT='"$(notdir $(basename $<))"' \
		-DTEST_FUNC_RET=$(notdir $(basename $<))_ret $<

$(RISCV_TESTS)/rv32uc/%.o: $(RISCV_TESTS)/rv32uc/%.S $(RISCV_TESTS)/riscv_test.h \
			$(RISCV_TESTS)/macros/scalar/test_macros.h
	$(RISCV_EXE_PREFIX)gcc -c -march=rv32im -g -o $@ \
		$(RISCV_TEST_INCLUDES) \
		-DTEST_FUNC_NAME=$(notdir $(basename $<)) \
		-DTEST_FUNC_TXT='"$(notdir $(basename $<))"' \
		-DTEST_FUNC_RET=$(notdir $(basename $<))_ret $<

# Build riscv_compliance_test. Make sure to escape dashes to underscores
$(RISCV_COMPLIANCE_TESTS)/%.o: $(RISCV_COMPLIANCE_TESTS)/%.S $(RISCV_COMPLIANCE_TESTS)/riscv_test.h \
			$(RISCV_COMPLIANCE_TESTS)/test_macros.h $(RISCV_COMPLIANCE_TESTS)/compliance_io.h \
			$(RISCV_COMPLIANCE_TESTS)/compliance_test.h
	$(RISCV_EXE_PREFIX)gcc -c -march=rv32im -g -o $@ \
		-DTEST_FUNC_NAME=$(notdir $(subst -,_,$(basename $<))) \
		-DTEST_FUNC_TXT='"$(notdir $(subst -,_,$(basename $<)))"' \
		-DTEST_FUNC_RET=$(notdir $(subst -,_,$(basename $<)))_ret $<

# run picorv firmware
# in verilator
.PHONY: firmware-veri-run
firmware-veri-run: verilate $(FIRMWARE)/firmware.hex
	mkdir -p $(VERI_LOG_DIR)
	./testbench_verilator $(VERI_FLAGS) \
		"+firmware=$(FIRMWARE)/firmware.hex" \
		| tee $(VERI_LOG_DIR)/firmware-veri-run.log

# in vsim
.PHONY: firmware-vsim-run
firmware-vsim-run: vsim-all firmware/firmware.hex
firmware-vsim-run: ALL_VSIM_FLAGS += "+firmware=firmware/firmware.hex"
firmware-vsim-run: vsim-run

.PHONY: firmware-vsim-run-gui
firmware-vsim-run-gui: vsim-all firmware/firmware.hex
firmware-vsim-run-gui: ALL_VSIM_FLAGS += "+firmware=firmware/firmware.hex"
firmware-vsim-run-gui: vsim-run-gui

# in vcs
.PHONY: firmware-vcs-run
firmware-vcs-run: vcsify firmware/firmware.hex
	./simv $(SIMV_FLAGS) "+firmware=firmware/firmware.hex"

.PHONY: firmware-vcs-run-gui
firmware-vcs-run-gui: VCS_FLAGS+=-debug_all
firmware-vcs-run-gui: vcsify firmware/firmware.hex
	./simv $(SIMV_FLAGS) -gui "+firmware=firmware/firmware.hex"

.PHONY: firmware-clean
firmware-clean:
	rm -vrf $(addprefix firmware/firmware., elf bin hex map) \
		$(FIRMWARE_OBJS) $(FIRMWARE_TEST_OBJS) $(COMPLIANCE_TEST_OBJS)

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
