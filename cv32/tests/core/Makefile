# Copyright 2019 OpenHW Group
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

# Original Author: Robert Balas (balasr@iis.ee.ethz.ch)
# Description: All in one. Uses parts of picorv32's makefile for handling the
# firmware and handling csmith programs

MAKE			= make
CTAGS			= ctags
CSMITH    = csmith

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
DSIM              = dsim
DSIM_HOME         = /tools/Metrics/dsim
DSIM_FLAGS        = -timescale 1ns/1ps
DSIM_IMAGE        = dsim.out

# xrun is the Cadence xcelium SystemVerilog simulator (https://cadence.com/)
XRUN              = xrun
XRUN_FLAGS        = -clean -smartorder -sv -top worklib.tb_top -timescale 1ns/1ps
XRUN_DIR          = xcelium.d

# verilator configuration
VERILATOR           = verilator
VERI_FLAGS         +=
VERI_COMPILE_FLAGS += -Wno-BLKANDNBLK # hope this doesn't hurt us in the long run
VERI_TRACE          =
VERI_OBJ_DIR       ?= cobj_dir
VERI_LOG_DIR       ?= cobj_dir/logs
VERI_CFLAGS         = -O2

# TB source files for the CV32E core (TODO: fix the TBSRC variable)
TBSRC_HOME  := ../../tb
TBSRC_PKG		:= $(TBSRC_HOME)/tb_riscv/include/perturbation_defines.sv
TBSRC_TOP		:= $(TBSRC_HOME)/core/tb_top.sv
TBSRC_CORE	:= $(TBSRC_HOME)/core
#TBSRC       := $(filter-out riscv_tb_pkg.sv tb_top_verilator.sv, $(wildcard *.sv))
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

# RTL source files for the CV32E core
RTLSRC_HOME   := ../../../rtl
RTLSRC_INCDIR := $(RTLSRC_HOME)/include
RTLSRC_PKG		:= $(addprefix $(RTLSRC_HOME)/include/,\
				         apu_core_package.sv fpnew_pkg.sv \
				         riscv_defines.sv riscv_tracer_defines.sv)
RTLSRC			  := $(filter-out $(RTLSRC_HOME)/riscv_register_file_latch.sv,\
				         $(wildcard $(RTLSRC_HOME)/*.sv))

# TODO: clean this up
RTLSRC_VLOG_TB_TOP	:= $(basename $(notdir $(TBSRC_TOP)))
RTLSRC_VOPT_TB_TOP	:= $(addsuffix _vopt, $(RTLSRC_VLOG_TB_TOP))

# riscv toolchain install path
RISCV                   ?= ~/.riscv
RISCV_EXE_PREFIX         = $(RISCV)/bin/riscv32-unknown-elf-

# firmware vars
FIRMWARE                 = firmware/
RISCV_TEST_INCLUDES      = -Iriscv_tests/ -Iriscv_tests/macros/scalar \
                           -Iriscv_tests/rv64ui -Iriscv_tests/rv64um
CV32_RISCV_TESTS_FIRMWARE_OBJS = $(addprefix cv32_riscv_tests_firmware/, start.o \
                                             print.o sieve.o multest.o stats.o)
CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE_OBJS = $(addprefix cv32_riscv_compliance_tests_firmware/, start.o \
                                                        print.o sieve.o multest.o stats.o)
RISCV_TESTS_OBJS         = $(addsuffix .o, \
				                     $(basename $(wildcard riscv_tests/rv32ui/*.S)) \
				                     $(basename $(wildcard riscv_tests/rv32um/*.S)) \
				                     $(basename $(wildcard riscv_tests/rv32uc/*.S)))
FIRMWARE_OBJS		         = $(addprefix firmware/, start.o \
				                     print.o sieve.o multest.o stats.o)
FIRMWARE_TEST_OBJS       = $(addsuffix .o, \
				                     $(basename $(wildcard riscv_tests/rv32ui/*.S)) \
				                     $(basename $(wildcard riscv_tests/rv32um/*.S)) \
				                     $(basename $(wildcard riscv_tests/rv32uc/*.S)))
FIRMWARE_SHORT_TEST_OBJS = $(addsuffix .o, \
				                     $(basename $(wildcard riscv_tests/rv32ui/*.S)) \
				                     $(basename $(wildcard riscv_tests/rv32um/*.S)))
COMPLIANCE_TEST_OBJS	   = $(addsuffix .o, \
				                     $(basename $(wildcard riscv_compliance_tests/*.S)))

# csmith vars
CSMITH_INCLUDE           = ~/.local/include/csmith-2.4.0
CSMITH_TIMEOUT_REF       = 2
CSMITH_TIMEOUT_VSIM      = 3000
CSMITH_TIMEOUT_VERI      = 100

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

vcsify: $(RTLSRC_PKG) $(RTLSRC) $(TBSRC_PKG) $(TBSRC)
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

dsimify: $(RTLSRC_PKG) $(RTLSRC) $(TBSRC_PKG) $(TBSRC)
	$(DSIM) \
		$(DSIM_FLAGS) \
		$(RTLSRC_PKG) $(RTLSRC) $(TBSRC_PKG) $(TBSRC) \
		+incdir+$(RTLSRC_INCDIR) \
		-genimage $(DSIM_IMAGE)

dsimify-rtl-only: $(RTLSRC_PKG) $(RTLSRC)
	$(DSIM) \
		$(DSIM_FLAGS) \
		$(RTLSRC_PKG) $(RTLSRC) \
		+incdir+$(RTLSRC_INCDIR) \
		-genimage $(DSIM_IMAGE)

# Metrics dsim simulations
.PHONY: dsim-hellow_world dsim-cv32_riscv_tests dsim-cv32_riscv_compliance_tests dsim-firmware

# Runs the hello world test
dsim-hello_world: dsimify custom/hello_world.hex
	$(DSIM) -l dsim-hello_world.log -image $(DSIM_IMAGE) \
		+firmware=custom/hello_world.hex

# Runs tests in riscv_tests/ only
dsim-cv32_riscv_tests: dsimify cv32_riscv_tests_firmware/cv32_riscv_tests_firmware.hex
	$(DSIM) -l dsim-riscv_tests.log -image $(DSIM_IMAGE) \
		+firmware=cv32_riscv_tests_firmware/cv32_riscv_tests_firmware.hex

# TODO: Runs tests in riscv_compliance_tests/ only
dsim-cv32_riscv_compliance_tests: dsimify cv32_riscv_compliance_tests_firmware/cv32_riscv_compliance_tests_firmware.hex
	$(DSIM) -l dsim-riscv_compliance_tests.log -image $(DSIM_IMAGE) \
		+firmware=cv32_riscv_compliance_tests_firmware/cv32_riscv_compliance_tests_firmware.hex

# Runs all tests in riscv_tests/ and riscv_compliance_tests/
dsim-firmware: dsimify firmware/firmware.hex
	$(DSIM) -l dsim-firmware.log -image $(DSIM_IMAGE) \
		+firmware=firmware/firmware.hex

# Metrics dsim cleanup
.PHONY: dsim-clean

dsim-clean:
	rm -f dsim.log
	rm -f dsim-*.log
	rm -f metrics_history.db
	rm -f metrics.xml
	rm -f trace_core_00_0.log
	rm -rf dsim_work
	rm -f dsim.env
	rm -f $(DSIM_IMAGE)
	find ./ -name *.o   -exec rm {} \;
	find ./ -name *.hex -exec rm {} \;
	find ./ -name *.elf -exec rm {} \;
	find ./ -name *.map -exec rm {} \;

# Cadence Xcelium xrun testbench compilation
.PHONY: xrun-all
xrun-all: $(RTLSRC_PKG) $(RTLSRC) $(TBSRC_PKG) $(TBSRC)
	$(XRUN) \
		$(XRUN_FLAGS) \
		$(RTLSRC_PKG) $(RTLSRC) $(TBSRC_PKG) $(TBSRC) \
		+incdir+$(RTLSRC_INCDIR)
.PHONY: xrun-hello_world xrun-firmware
xrun-hello_world: xrun-all custom/hello_world.hex
	$(XRUN) \
		$(XRUN_FLAGS) \
		$(RTLSRC_PKG) $(RTLSRC) $(TBSRC_PKG) $(TBSRC) \
		+incdir+$(RTLSRC_INCDIR) +firmware=custom/hello_world.hex
xrun-firmware: xrun-all firmware/firmware.hex
	$(XRUN) \
		$(XRUN_FLAGS) \
		$(RTLSRC_PKG) $(RTLSRC) $(TBSRC_PKG) $(TBSRC) \
		+incdir+$(RTLSRC_INCDIR) +firmware=firmware/firmware.hex

# Cadence Xcelium xrun cleanup
.PHONY: xrun-clean xrun-clean-all
xrun-clean:
	rm -vrf $(XRUN_DIR)
xrun-clean-all: xrun-clean
	rm -vrf $(addprefix firmware/firmware., elf bin hex map) \
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

testbench_verilator: $(TBSRC_VERI) $(RTLSRC_PKG) $(RTLSRC)
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

verilate-clean:
	if [ -d $(VERI_LOG_DIR) ]; then rm -r $(VERI_LOG_DIR); fi
	if [ -d $(VERI_OBJ_DIR) ]; then rm -r $(VERI_OBJ_DIR); fi
	rm -rf testbench_verilator
	find ./ -name *.o   -exec rm {} \;
	find ./ -name *.hex -exec rm {} \;
	find ./ -name *.elf -exec rm {} \;
	find ./ -name *.map -exec rm {} \;

# fpnew dependencies (no longer needed - fpnew_pkg.sv commited to rtl/include)
#fpnew/src/fpnew_pkg.sv:
#	git clone https://github.com/pulp-platform/fpnew --recurse

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
custom/hello_world.elf: custom/hello_world.c
	$(RISCV_EXE_PREFIX)gcc -march=rv32imc -o $@ -w -Os -g -nostdlib \
		-T custom/link.ld  \
		-static \
		custom/crt0.S \
		$^ custom/syscalls.c custom/vectors.S \
		-I $(RISCV)/riscv32-unknown-elf/include \
		-L $(RISCV)/riscv32-unknown-elf/lib \
		-lc -lm -lgcc
custom-clean:
	rm -rf custom/hello_world.elf custom/hello_world.hex

.PHONY: custom-vsim-run
custom-vsim-run: vsim-all custom/hello_world.hex
custom-vsim-run: ALL_VSIM_FLAGS += "+firmware=custom/hello_world.hex"
custom-vsim-run: vsim-run

.PHONY: custom-vsim-run-gui
custom-vsim-run-gui: vsim-all custom/hello_world.hex
custom-vsim-run-gui: ALL_VSIM_FLAGS += "+firmware=custom/hello_world.hex"
custom-vsim-run-gui: vsim-run-gui


.PHONY: custom-veri-run
custom-veri-run: verilate custom/hello_world.hex
	mkdir -p $(VERI_LOG_DIR)
	./testbench_verilator $(VERI_FLAGS) \
		"+firmware=custom/hello_world.hex" \
		| tee $(VERI_LOG_DIR)/custom-veri-run.log

# compile and dump RISCV_TESTS only
cv32_riscv_tests_firmware/cv32_riscv_tests_firmware.elf: $(CV32_RISCV_TESTS_FIRMWARE_OBJS) $(RISCV_TESTS_OBJS) \
							cv32_riscv_tests_firmware/link.ld
	$(RISCV_EXE_PREFIX)gcc -g -Os -march=rv32imc -ffreestanding -nostdlib -o $@ \
		$(RISCV_TEST_INCLUDES) \
		-Wl,-Bstatic,-T,cv32_riscv_tests_firmware/link.ld,-Map,cv32_riscv_tests_firmware/cv32_riscv_tests_firmware.map,--strip-debug \
		$(CV32_RISCV_TESTS_FIRMWARE_OBJS) $(RISCV_TESTS_OBJS) -lgcc

cv32_riscv_tests_firmware/start.o: cv32_riscv_tests_firmware/start.S
	$(RISCV_EXE_PREFIX)gcc -c -march=rv32imc -g -o $@ $<

cv32_riscv_tests_firmware/%.o: cv32_riscv_tests_firmware/%.c
	$(RISCV_EXE_PREFIX)gcc -c -march=rv32ic -g -Os --std=c99 -Wall \
		$(RISCV_TEST_INCLUDES) \
		-ffreestanding -nostdlib -o $@ $<

# compile and dump RISCV_COMPLIANCE_TESTS only
cv32_riscv_compliance_tests_firmware/cv32_riscv_compliance_tests_firmware.elf: $(CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE_OBJS) $(COMPLIANCE_TEST_OBJS) \
							cv32_riscv_compliance_tests_firmware/link.ld
	$(RISCV_EXE_PREFIX)gcc -g -Os -march=rv32imc -ffreestanding -nostdlib -o $@ \
		-D RUN_COMPLIANCE \
		$(RISCV_TEST_INCLUDES) \
		-Wl,-Bstatic,-T,cv32_riscv_compliance_tests_firmware/link.ld,-Map,cv32_riscv_compliance_tests_firmware/cv32_riscv_compliance_tests_firmware.map,--strip-debug \
		$(CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE_OBJS) $(COMPLIANCE_TEST_OBJS) -lgcc

cv32_riscv_compliance_tests_firmware/start.o: cv32_riscv_compliance_tests_firmware/start.S
	$(RISCV_EXE_PREFIX)gcc -c -march=rv32imc -D RUN_COMPLIANCE -g -o $@ $<

cv32_riscv_compliance_tests_firmware/%.o: cv32_riscv_compliance_tests_firmware/%.c
	$(RISCV_EXE_PREFIX)gcc -c -march=rv32ic -g -Os --std=c99 -Wall \
		$(RISCV_TEST_INCLUDES) \
		-ffreestanding -nostdlib -o $@ $<

# compile and dump picorv firmware
firmware/firmware.elf: $(FIRMWARE_OBJS) $(FIRMWARE_TEST_OBJS) $(COMPLIANCE_TEST_OBJS) \
				firmware/link.ld
	$(RISCV_EXE_PREFIX)gcc -g -Os -march=rv32imc -ffreestanding -nostdlib -o $@ \
		$(RISCV_TEST_INCLUDES) \
		-D RUN_COMPLIANCE \
		-Wl,-Bstatic,-T,firmware/link.ld,-Map,firmware/firmware.map,--strip-debug \
		$(FIRMWARE_OBJS) $(FIRMWARE_TEST_OBJS) $(COMPLIANCE_TEST_OBJS) -lgcc

firmware/start.o: firmware/start.S
	$(RISCV_EXE_PREFIX)gcc -c -march=rv32imc -g -D RUN_COMPLIANCE -o $@ $<

firmware/%.o: firmware/%.c
	$(RISCV_EXE_PREFIX)gcc -c -march=rv32ic -g -Os --std=c99 -Wall \
		$(RISCV_TEST_INCLUDES) \
		-ffreestanding -nostdlib -o $@ $<

riscv_tests/rv32ui/%.o: riscv_tests/rv32ui/%.S riscv_tests/riscv_test.h \
			riscv_tests/macros/scalar/test_macros.h
	$(RISCV_EXE_PREFIX)gcc -c -march=rv32im -g -o $@ \
		$(RISCV_TEST_INCLUDES) \
		-DTEST_FUNC_NAME=$(notdir $(basename $<)) \
		-DTEST_FUNC_TXT='"$(notdir $(basename $<))"' \
		-DTEST_FUNC_RET=$(notdir $(basename $<))_ret $<

riscv_tests/rv32um/%.o: riscv_tests/rv32um/%.S riscv_tests/riscv_test.h \
			riscv_tests/macros/scalar/test_macros.h
	$(RISCV_EXE_PREFIX)gcc -c -march=rv32im -g -o $@ \
		$(RISCV_TEST_INCLUDES) \
		-DTEST_FUNC_NAME=$(notdir $(basename $<)) \
		-DTEST_FUNC_TXT='"$(notdir $(basename $<))"' \
		-DTEST_FUNC_RET=$(notdir $(basename $<))_ret $<

riscv_tests/rv32uc/%.o: riscv_tests/rv32uc/%.S riscv_tests/riscv_test.h \
			riscv_tests/macros/scalar/test_macros.h
	$(RISCV_EXE_PREFIX)gcc -c -march=rv32im -g -o $@ \
		$(RISCV_TEST_INCLUDES) \
		-DTEST_FUNC_NAME=$(notdir $(basename $<)) \
		-DTEST_FUNC_TXT='"$(notdir $(basename $<))"' \
		-DTEST_FUNC_RET=$(notdir $(basename $<))_ret $<

# Build riscv_compliance_test. Make sure to escape dashes to underscores
riscv_compliance_tests/%.o: riscv_compliance_tests/%.S riscv_compliance_tests/riscv_test.h \
			riscv_compliance_tests/test_macros.h riscv_compliance_tests/compliance_io.h \
			riscv_compliance_tests/compliance_test.h
	$(RISCV_EXE_PREFIX)gcc -c -march=rv32im -g -o $@ \
		-DTEST_FUNC_NAME=$(notdir $(subst -,_,$(basename $<))) \
		-DTEST_FUNC_TXT='"$(notdir $(subst -,_,$(basename $<)))"' \
		-DTEST_FUNC_RET=$(notdir $(subst -,_,$(basename $<)))_ret $<

# run picorv firmware
# in verilator
.PHONY: firmware-veri-run
firmware-veri-run: verilate firmware/firmware.hex
	mkdir -p $(VERI_LOG_DIR)
	./testbench_verilator $(VERI_FLAGS) \
		"+firmware=firmware/firmware.hex" \
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

# csmith targets
csmith/test.c:
	echo "integer size = 4" > csmith/platform.info
	echo "pointer size = 4" >> csmith/platform.info
	$(CSMITH) --no-packed-struct -o csmith/test.c
	gawk '/Seed:/ {print$$2,$$3;}' csmith/test.c

csmith/test_ref: csmith/test.c
	gcc -m32 -o csmith/test_ref -w -Os -I $(CSMITH_INCLUDE) csmith/test.c

csmith/test.elf: csmith/test.c csmith/syscalls.c csmith/start.S
	$(RISCV_EXE_PREFIX)gcc -march=rv32imc -o csmith/test.elf -w -Os \
		-I $(CSMITH_INCLUDE) \
		-T csmith/link.ld  \
		csmith/test.c csmith/syscalls.c csmith/start.S -Wl,--verbose
	chmod u+x csmith/test.elf

csmith-clean:
	rm -rf $(addprefix csmith/, test.c test.elf test.hex test_ref)

# simulators and fesvr for csmith
riscv-fesvr/build.ok:
	rm -rf riscv-fesvr
	git clone https://github.com/riscv/riscv-fesvr.git riscv-fesvr
	+cd riscv-fesvr && git checkout 1c02bd6 && \
		./configure && make && touch build.ok

riscv-isa-sim/build.ok: riscv-fesvr/build.ok
	rm -rf riscv-isa-sim
	git clone https://github.com/riscv/riscv-isa-sim.git riscv-isa-sim
	cd riscv-isa-sim && git checkout 10ae74e
	cd riscv-isa-sim && patch -p1 < ../csmith/riscv-isa-sim.diff
	cd riscv-isa-sim && \
		LDFLAGS="-L../riscv-fesvr" ./configure --with-isa=RV32IMC
	+cd riscv-isa-sim \
		&& ln -s ../riscv-fesvr/fesvr . && make && touch build.ok

.PHONY: csmith-spike
csmith-spike: riscv-fesvr/build.ok riscv-isa-sim/build.ok csmith/test_ref \
		 csmith/test.elf
	timeout $(CSMITH_TIMEOUT_REF) ./csmith/test_ref > csmith/output_ref.txt \
		&& cat csmith/output_ref.txt
	LD_LIBRARY_PATH="./riscv-isa-sim:./riscv-fesvr" \
		./riscv-isa-sim/spike csmith/test.elf > csmith/output_sim.txt
	diff -u csmith/output_ref.txt csmith/output_sim.txt

# run verilator on csmith/test.compliance_hex and only return the checksum, if any. We also have
# a timeout mechanism in place to prevent infinite loops
.PHONY: csmith-veri-rtl
csmith-veri-rtl: verilate csmith/test.hex
csmith-veri-rtl: VERI_FLAGS += "+firmware=csmith/test.hex"
csmith-veri-rtl:
	timeout $(CSMITH_TIMEOUT_VERI) ./testbench_verilator $(VERI_FLAGS) \
	| grep 'checksum' > csmith/output_sim.txt

# run vsim on csmith/test.hex and only return the checksum, if any. We also have
# a timeout mechanism in place to prevent infinite loops
.PHONY: csmith-vsim-rtl
csmith-vsim-rtl: vsim-all csmith/test.hex
csmith-vsim-rtl: ALL_VSIM_FLAGS += "-GBOOT_ADDR=128"
csmith-vsim-rtl: ALL_VSIM_FLAGS += "+firmware=csmith/test.hex"
csmith-vsim-rtl:
	timeout $(CSMITH_TIMEOUT_VSIM) $(VSIM) -work $(VWORK) \
	$(ALL_VSIM_FLAGS) \
	$(RTLSRC_VOPT_TB_TOP) -do 'source $(VSIM_SCRIPT); exit -f' \
	| grep 'checksum' | cut -c 3- > csmith/output_sim.txt

.PHONY: csmith-loop
csmith-loop: riscv-fesvr/build.ok riscv-isa-sim/build.ok
# Check if the reference program terminates and if spike produces the same
# result. Otherwise we just skip the test. Then we check if we produce the same
# output with the rtl model (ri5cy). Stop on first failed test
	+set -e; \
	x() { echo "$$*" >&2; "$$@"; }; \
	i=1; j=0; k=0;\
	while true; do \
		echo; echo; \
		echo "--- test#$$((i++)) passed:$${j} skipped:$${k} ---"; \
		x rm -f $(addprefix csmith/, test.hex test.elf \
			test.c test_ref output_ref.txt output_sim.txt); \
		x make csmith-spike csmith/test.hex || \
			{ \
				echo SKIP; \
				! ((k++)); \
				continue; \
			}; \
		x rm -f csmith/output_sim.txt; \
		x make csmith-veri-rtl; \
		x diff -u csmith/output_ref.txt csmith/output_sim.txt; \
			echo OK; ! ((j++)); \
	done


# general targets
.PHONY: clean
clean: tb-clean verilate-clean vcs-clean firmware-clean csmith-clean custom-clean dsim-clean

.PHONY: distclean
distclean: clean
	rm -rf riscv-fesvr riscv-isa-sim fpnew work
