# Copyright 2026 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Enrico Zelioli <ezelioli@iis.ee.ethz.ch>

# Variables
MAKEFILE_DIR  := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
ROOT_DIR      := $(abspath $(MAKEFILE_DIR)/..)
TEST_DIR      := $(ROOT_DIR)/test
VSIM_DIR      := $(TEST_DIR)/vsim
VERILATOR_DIR := $(TEST_DIR)/verilator

# Tools
BENDER    ?= bender --suppress E31 -d $(ROOT_DIR)
QUESTA    ?=
VERILATOR ?= verilator

# Target CVA6 configuration
CVA6_CONFIG   ?= cv64a6_imafdchsclic_sv39_wb
HEXFILE       ?= $(TEST_DIR)/sw/out/hello.hex
MAX_CYCLES    ?= 10000
# Main memory delay per AXI channel, 0 to 100, passed as +MemDelay when set
MEM_DELAY     ?=
# Extra plusargs forwarded to the simulation, e.g. SIM_ARGS="+fst"
SIM_ARGS      ?=
TEST          ?= test_simple
ALLOWED_TESTS := test_simple
DEBUG         ?= 0
WAVES         ?= 0
# Verilator threads for the simulation model, a BUILD time choice. The default
# suits one simulation at a time, which is the usual case.
# For running many simulations at once, build with THREADS=1 instead.
THREADS       ?= 2
# CVA6's legacy tracer
LEGACY_TRACE  ?= 0
# Instruction tracer
TRACER        ?= 0
TRACER_DIR    := $(TEST_DIR)/hw/tracer
TRACER_SRC    := $(TRACER_DIR)/cva6tb_tracer.cc $(TRACER_DIR)/rv_disasm.cc \
                 $(TRACER_DIR)/rv_disasm_spike.cc $(TRACER_DIR)/rv_format.cc \
                 $(TRACER_DIR)/rv_stats.cc $(TRACER_DIR)/rv_symbols.cc \
                 $(TRACER_DIR)/rv_trigger.cc
TRACER_HDR    := $(TRACER_DIR)/cva6tb_tracer_dpi.h $(TRACER_DIR)/rv_disasm.h \
                 $(TRACER_DIR)/rv_format.h $(TRACER_DIR)/rv_stats.h \
                 $(TRACER_DIR)/rv_symbols.h $(TRACER_DIR)/rv_trigger.h
# Instruction tracer settings, each passed as the plusarg of the same name when
# set; see hw/tracer/. Files are made absolute, since the simulation runs in its
# build directory. Symbols default to the program's own ELF beside HEXFILE and
# the boot ROM's, where they exist, outside the legacy format, which stays byte
# compatible with instr_tracer's logs; TRACE_SYMBOLS= turns annotation off.
TRACE_FORMAT  ?=
TRACE_VERBOSE ?=
TRACE_FILE    ?=
TRACE_START   ?=
TRACE_STOP    ?=
TRACE_STATS   ?=
TRACE_SYMBOLS ?= $(if $(filter legacy,$(TRACE_FORMAT)),, \
                   $(wildcard $(basename $(abspath $(HEXFILE))).elf \
                              $(TEST_DIR)/hw/bootrom/cva6tb_bootrom.elf))

# Goals that must work without a resolved dependency tree.
NODEPS_GOALS := info default %clean
NEEDS_DEPS   := $(filter-out $(NODEPS_GOALS),$(MAKECMDGOALS))

ifneq ($(NEEDS_DEPS),)
ifeq ($(filter $(TEST),$(ALLOWED_TESTS)),)
$(error TEST must be one of: $(ALLOWED_TESTS) (got '$(TEST)'))
endif
endif

.PHONY: default
default: info

.PHONY: clean
clean: vsim-clean verilator-clean

.PHONY: info
info:
	@echo "########################## INFO ##########################"
	@echo "MAKEFILE_DIR  : $(MAKEFILE_DIR)"
	@echo "ROOT_DIR      : $(ROOT_DIR)"
	@echo "TEST_DIR      : $(TEST_DIR)"
	@echo "VSIM_DIR      : $(VSIM_DIR)"
	@echo "VERILATOR_DIR : $(VERILATOR_DIR)"
	@echo "##########################################################"

##################################
############ Bender ##############
##################################

BENDER_FLAGS := -t rtl -t simulation -t cva6 -t $(CVA6_CONFIG) -t cva6tb -t $(TEST)

ifeq ($(ZERO_SIM_MEM),1)
BENDER_FLAGS += -D ZERO_SIM_MEM
endif

ifeq ($(TRACER),1)
BENDER_FLAGS += -t tracer
endif

# Plusargs set through variables, the testbench's and the tracer's. They follow
# SIM_ARGS on the command line, and the first occurrence of a plusarg is the one
# that counts, so SIM_ARGS overrides them.
comma := ,
space := $(subst ,, )
TB_ARGS = $(if $(MEM_DELAY),+MemDelay=$(MEM_DELAY))
ifeq ($(TRACER),1)
TRACER_ARGS = $(if $(TRACE_FORMAT),+trace_format=$(TRACE_FORMAT)) \
              $(if $(TRACE_VERBOSE),+trace_verbose=$(TRACE_VERBOSE)) \
              $(if $(TRACE_FILE),+trace_file=$(abspath $(TRACE_FILE))) \
              $(if $(TRACE_START),+trace_start=$(TRACE_START)) \
              $(if $(TRACE_STOP),+trace_stop=$(TRACE_STOP)) \
              $(if $(TRACE_STATS),+trace_stats=$(abspath $(TRACE_STATS))) \
              $(if $(strip $(TRACE_SYMBOLS)),+trace_symbols=$(subst $(space),$(comma),$(strip $(abspath $(TRACE_SYMBOLS)))))
endif

ifeq ($(WAVES),1)
BENDER_FLAGS += -D CVA6TB_WAVES
endif

ifneq ($(LEGACY_TRACE),1)
BENDER_FLAGS += -D CVA6_NO_LEGACY_TRACE
endif

##################################
##### Hardware dependencies ######
##################################

ifeq ($(shell test -d $(ROOT_DIR)/.bender || echo 1),)

CLINTROOT := $(shell $(BENDER) path clint)
REGTOOL   := $(shell $(BENDER) path register_interface)/vendor/lowrisc_opentitan/util/regtool.py
OTPROOT   := $(shell $(BENDER) path opentitan_peripherals)

CLINTCORES := 1
include $(CLINTROOT)/clint.mk
$(CLINTROOT)/.generated:
	flock -x $@ $(MAKE) clint && touch $@ || (rm -f $@; false)

include $(OTPROOT)/otp.mk
$(OTPROOT)/.generated: $(TEST_DIR)/hw/rv_plic.cfg.hjson
	flock -x $@ sh -c "cp $< $(dir $@)/src/rv_plic/; $(MAKE) -j1 otp" && touch $@ || (rm -f $@; false)

HW_DEPS := $(CLINTROOT)/.generated $(OTPROOT)/.generated

else ifneq ($(NEEDS_DEPS),)
$(error Bender dependencies are not initialized. Run 'bender checkout' in $(ROOT_DIR))
endif

##################################
########### Bootrom ##############
##################################

ifndef RV_BINROOT
RV_BINROOT := $(dir $(shell which riscv64-unknown-elf-gcc 2>/dev/null))
endif
RV_AR      := $(RV_BINROOT)/riscv64-unknown-elf-ar
RV_CC      := $(RV_BINROOT)/riscv64-unknown-elf-gcc
RV_OBJCOPY := $(RV_BINROOT)/riscv64-unknown-elf-objcopy
RV_OBJDUMP := $(RV_BINROOT)/riscv64-unknown-elf-objdump

BROM_CC_FLAGS = -DOT_PLATFORM_RV32 -march=rv64gc_zifencei -mabi=lp64d \
                -mstrict-align -O2 -Wall -Wextra -static -ffunction-sections \
                -fdata-sections -frandom-seed=cheshire -fuse-linker-plugin \
                -nostartfiles -Os -fno-zero-initialized-in-bss \
                -fwhole-program -flto -Wl,-flto -Wl,--gc-sections

$(TEST_DIR)/hw/bootrom/cva6tb_bootrom.bin: $(TEST_DIR)/hw/bootrom/cva6tb_bootrom.ld $(TEST_DIR)/hw/bootrom/cva6tb_bootrom.S $(RV_CC)
	$(RV_CC) -T$< $(BROM_CC_FLAGS) -o $(TEST_DIR)/hw/bootrom/cva6tb_bootrom.elf $(TEST_DIR)/hw/bootrom/cva6tb_bootrom.S
	cd $(@D) && $(RV_OBJDUMP) -d cva6tb_bootrom.elf > cva6tb_bootrom.dump
	$(RV_OBJCOPY) -O binary $(TEST_DIR)/hw/bootrom/cva6tb_bootrom.elf $@

$(TEST_DIR)/hw/bootrom/cva6tb_bootrom.sv: $(TEST_DIR)/hw/bootrom/cva6tb_bootrom.bin $(TEST_DIR)/util/gen_bootrom.py
	$(TEST_DIR)/util/gen_bootrom.py --sv-module cva6tb_bootrom $< > $@

.PHONY: bootrom
bootrom: $(TEST_DIR)/hw/bootrom/cva6tb_bootrom.sv

.PHONY: bootrom-clean
bootrom-clean:
	cd $(TEST_DIR)/hw/bootrom && rm -f *.sv *.elf *.bin *.dump


##################################
########## QuestaSim #############
##################################

VSIM_BUILD_DIR := $(VSIM_DIR)/build

# C++ compiler path
# Caution: Questasim requires this to point to the *actual* compiler install path
CXX_PATH := $(shell which $(CXX))

# Silence warning 13314 on input ports defaulting to 'wire' due to -svinputport=relaxed
# Silence warning 2583 on extra checking for conflicts between processes is done at vopt time
VLOG_FLAGS := -timescale 1ns/1ps -suppress 13314 -suppress 2583
VOPT_FLAGS := -suppress 3009 -suppress 8386 -suppress 7061 -error 7 -cpppath $(CXX_PATH)
VSIM_FLAGS :=

ifeq ($(DEBUG),0)
VSIM_FLAGS += -c -do "run -all; quit"
else
VOPT_FLAGS += +acc
VSIM_FLAGS += -wlf cva6tb.wlf -do "log -r /*; run -all"
endif

$(VSIM_BUILD_DIR):
	@mkdir -p $(VSIM_BUILD_DIR)

$(VSIM_BUILD_DIR)/vsim_compile.tcl: $(ROOT_DIR)/Bender.lock $(HW_DEPS) | $(VSIM_BUILD_DIR)
	$(BENDER) script vsim $(BENDER_FLAGS) --vlog-arg="$(VLOG_FLAGS)" > $@
ifeq ($(TRACER),1)
	@echo 'vlog -ccflags "-std=c++17 -O2" $(TRACER_SRC)' >> $@
endif
	@echo 'vopt $(VOPT_FLAGS) test -o test_opt' >> $@

$(VSIM_BUILD_DIR)/vsim_compile.log: $(VSIM_BUILD_DIR)/vsim_compile.tcl
	cd $(VSIM_BUILD_DIR) && $(QUESTA) vsim -c -do "quit -code [source $<]" | tee $@

$(VSIM_BUILD_DIR)/vsim_compile.err: $(VSIM_BUILD_DIR)/vsim_compile.log
	@echo "--- QuestaSim compilation report ---" > $@
	@echo "Errors:" >> $@
	@grep "Error:" $< >> $@ || true
	@echo "" >> $@
	@echo "Warnings:" >> $@
	@grep "Warning:" $< >> $@ || true
	@cat $@

.PHONY: vsim-build
vsim-build: $(VSIM_BUILD_DIR)/vsim_compile.err

.PHONY: vsim-run
vsim-run: $(VSIM_BUILD_DIR)/vsim_compile.err
	cd $(VSIM_BUILD_DIR) && $(QUESTA) vsim $(VSIM_FLAGS) test_opt +binary=$(abspath $(HEXFILE)) +MaxCycles=$(MAX_CYCLES) $(strip $(SIM_ARGS) $(TB_ARGS) $(TRACER_ARGS))

.PHONY: vsim-clean
vsim-clean:
	rm -rf $(VSIM_BUILD_DIR)

##################################
########## Verilator #############
##################################

ifeq ($(WAVES),1)
VERILATOR_TRACE := --trace-fst --trace-structs --trace-threads 2
else
VERILATOR_TRACE :=
endif

ifneq ($(THREADS),1)
VERILATOR_THREADS := --threads $(THREADS)
else
VERILATOR_THREADS :=
endif

VERILATOR_JOBS      ?= 0
VERILATOR_BUILD_DIR := $(VERILATOR_DIR)/build
VERILATOR_LOG_DIR   := $(VERILATOR_DIR)/logs
VERILATOR_FLIST     := $(VERILATOR_DIR)/cva6tb.flist
VERILATOR_WARNINGS  := -Wall -Wno-fatal -Wno-style -Wno-BLKANDNBLK -Wno-WIDTHEXPAND -Wno-WIDTHTRUNC -Wno-WIDTHCONCAT -Wno-ASCRANGE -Wno-IMPLICITSTATIC
VERILATOR_FLAGS     := --binary -j $(VERILATOR_JOBS) --Mdir $(VERILATOR_BUILD_DIR) $(VERILATOR_WARNINGS) -O3 -f $(VERILATOR_FLIST) --assert --timing \
	$(VERILATOR_TRACE) $(VERILATOR_THREADS) --x-assign fast --x-initial fast

ifeq ($(TRACER),1)
VERILATOR_FLAGS += $(TRACER_SRC)
endif

$(VERILATOR_LOG_DIR):
	@mkdir -p $(VERILATOR_LOG_DIR)

$(VERILATOR_FLIST): $(ROOT_DIR)/Bender.lock $(HW_DEPS)
	$(BENDER) script verilator $(BENDER_FLAGS) -D ASSERTS_OFF -t verilator > $@

$(VERILATOR_BUILD_DIR)/Vtest: $(VERILATOR_FLIST) | $(VERILATOR_LOG_DIR)
	cd $(VERILATOR_DIR) && $(VERILATOR) $(VERILATOR_FLAGS) --top-module test 2>&1 | tee $(VERILATOR_LOG_DIR)/build.log

.PHONY: verilator-build
verilator-build: $(VERILATOR_BUILD_DIR)/Vtest

.PHONY: verilator-run
verilator-run: $(VERILATOR_BUILD_DIR)/Vtest | $(VERILATOR_LOG_DIR)
	cd $(VERILATOR_DIR) && ./$(notdir $(VERILATOR_BUILD_DIR))/Vtest +binary=$(abspath $(HEXFILE)) +MaxCycles=$(MAX_CYCLES) $(strip $(SIM_ARGS) $(TB_ARGS) $(TRACER_ARGS)) 2>&1 | tee $(VERILATOR_LOG_DIR)/$(basename $(notdir $(HEXFILE))).log

.PHONY: verilator-clean
verilator-clean:
	rm -rf $(VERILATOR_BUILD_DIR) $(VERILATOR_LOG_DIR)
	rm -f $(VERILATOR_FLIST)
	cd $(VERILATOR_DIR) && rm -f *.fst *.fst.hier *.flist *.json *.dasm *.csv *.log cva6tb_trace_hart_*
