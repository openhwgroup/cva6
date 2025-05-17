##
#  Copyright 2023,2024 CEA*
#  *Commissariat a l'Energie Atomique et aux Energies Alternatives (CEA)
#
#  SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
#
#  Licensed under the Solderpad Hardware License v 2.1 (the “License”); you
#  may not use this file except in compliance with the License, or, at your
#  option, the Apache License version 2.0. You may obtain a copy of the
#  License at
#
#  https://solderpad.org/licenses/SHL-2.1/
#
#  Unless required by applicable law or agreed to in writing, any work
#  distributed under the License is distributed on an “AS IS” BASIS, WITHOUT
#  WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
#  License for the specific language governing permissions and limitations
#  under the License.
##
##
#  Author     : Cesar Fuguet
#  Date       : October, 2024
#  Description: HPDCACHE Test Makefile
##
-include user_conf.mk

TB_DIR              := $(shell dirname $(realpath $(firstword $(MAKEFILE_LIST))))
HPDCACHE_DIR        ?= $(TB_DIR)/../..

ifndef SYSTEMC_LIBDIR
$(error "SYSTEMC_LIBDIR not defined")
endif

VERILATOR           ?= verilator
VERILATOR_COV       ?= verilator_coverage
TOUCH               := touch
RM                  := rm -f
MKDIR               := mkdir -p
GDB                 := gdb
ECHO                := echo
SCANLOG             := $(TB_DIR)/scripts/scan_logs.pl -listwarnings -listerrors
SHELL               := bash

Q                   ?= @
NTRANSACTIONS       ?= 10000
TIMEOUT             ?= $$(( $(NTRANSACTIONS)*1000 ))
SEQUENCE            ?= random
LOG_LEVEL           ?= 1
SEED                ?= 1234
NTESTS              ?= 128
TRACE               ?= 0

BUILD_DIR           := build
LOG_DIR             := logs
COV_DIR             := coverage
VERILATE_LOG        := $(BUILD_DIR)/verilate.log
BUILD_LOG           := $(BUILD_DIR)/build.log

RUN_LOG             ?= $(LOG_DIR)/run_$(SEQUENCE)_$(SEED).log
TRACE_FILE          ?= $(LOG_DIR)/run_$(SEQUENCE)_$(SEED).vcd
COV_FILE            ?= $(COV_DIR)/cov_$(SEQUENCE)_$(SEED).dat
COV_MERGEFILE       ?= $(COV_DIR)/cov_result.dat
DATE_TIME           ?= $(shell date "+%Y_%m_%d-%H%M")

export CXX             := $(CXX)
export LINK            := $(CXX)
export CC              := $(CC)
export PERL5LIB        := $(TB_DIR)/scripts/perl5

CONF_DEFINES =

ifdef CONFIG
include $(CONFIG)
else
include default_config.mk
endif

include rtl_conf.mk

USER_CPPFLAGS       += -I$(TB_DIR) \
                       -I$(TB_DIR)/sc_verif_lib/include \
                       -I$(TB_DIR)/sc_verif_lib/modules/generic_cache/include \
                       -I$(TB_DIR)/sc_verif_lib/modules/mem_model/include \
                       -DDEBUG_HPDCACHE_TEST_SCOREBOARD=1 \
                       -DDEBUG_HPDCACHE_TEST_MEM_RESP_MODEL=1 \
                       $(if $(filter 1,$(DEBUG)),-DDEBUG) \
                       $(CONF_DEFINES)

VERILATOR_FLAGS     += -Wall -Wno-fatal \
                       -Werror-PINMISSING \
                       -Werror-IMPLICIT \
                       -Werror-UNDRIVEN \
                       -Werror-MULTIDRIVEN \
                       -Wno-PINCONNECTEMPTY \
                       --report-unoptflat \
                       -O3 -I$(HPDCACHE_DIR)/rtl/src \
                       --x-assign unique --x-initial unique \
                       $(if $(filter 1,$(DISABLE_TRACE)),\
                                    $(info make: Tracing support disabled), \
                                    $(info make: Tracing support enabled) \
                                    --trace --trace-structs) \
                       $(if $(filter 1,$(DISABLE_ASSERT)),\
                                    $(info make: Assertion support disabled), \
                                    $(info make: Assertion support enabled) \
                                    --assert) \
                       $(if $(filter 1,$(PROF)),\
                                    $(info make: Profiling support enabled) \
                                    --prof-cfuncs -CFLAGS "-g -pg", \
                                    $(info make: Profiling support disabled) \
                                    -CFLAGS "-O3") \
                       $(if $(filter 1,$(COV)),\
                                    $(info make: Coverage support enabled) --coverage, \
                                    $(info make: Coverage support disabled)) \
                       $(CONF_DEFINES)

VERILATOR_MAKEFLAGS += USER_CPPFLAGS="$(USER_CPPFLAGS)" \
                       USER_LDFLAGS="-Wl,-rpath,$(SYSTEMC_LIBDIR)" \
                       USER_LDLIBS="-lscv"

VERILATOR_RUNFLAGS  += +verilator+seed+$(SEED) \
                       +verilator+rand+reset+1 \
                       +verilator+error+limit+50 \
                       -m $(TIMEOUT) \
                       -n $(NTRANSACTIONS) \
                       -s $(SEQUENCE) \
                       -l $(LOG_LEVEL) \
                       -r $(SEED) \
                       $(if $(filter 1,$(TRACE)), +trace -t $(TRACE_FILE)) \
                       $(if $(filter 1,$(COV)),-c $(COV_FILE))

TB_TOP              := hpdcache_tb
DUT                 := hpdcache_wrapper

export SC_COPYRIGHT_MESSAGE=DISABLE

.PHONY: all
all: help

.PHONY: verilate build run
verilate: $(VERILATE_LOG)
build: $(BUILD_LOG)
run: $(RUN_LOG)

define help_message
help: make [target] [arguments]

This is a Verilator (with SystemC) testbench for the HPDcache block.

It is a standalone testbench where the HPDcache is not connected to a processor
core. Requests are generated by agents using a sequence defined by the user.
Some sequences are already provided in the sequence_lib subdirectory.

The testbench also implements a memory response model that acts as the main
memory of the system.

All the requests and responses to/from the HPDcache are validated automatically
by the testbench scoreboard.

targets:

verilate                     Convert RTL into C++/SystemC sources

build <options>              Compile DUT and testbench sources

    -j<jobs>

run <options>                Execute the specified test sequence on the
                             testbench

    [SEQUENCE=$(SEQUENCE)] - test sequence
    [TRACE=$(TRACE)] - generate waveform (on VCD format)
    [TIMEOUT=$(TIMEOUT)] - maximum nb of run cycles
    [LOG_LEVEL=$(LOG_LEVEL)] - level of log verbosity (low = 0, 1, 2, high = 3)
    [NTRANSACTIONS=$(NTRANSACTIONS)] - nb of transactions during the test
    [SEED=$(SEED)] - random seed

nonregression <options>      Execute a a non-regression test suite.
                             This suite executes the specified sequence
                             NTESTS nb of times. Each time a
                             different random seed is used

    [SEQUENCE=$(SEQUENCE)]
    [TIMEOUT=$(TIMEOUT)]
    [LOG_LEVEL=$(LOG_LEVEL)]
    [NTRANSACTIONS=$(NTRANSACTIONS)]
    [NTESTS=$(NTESTS)] - nb of times the sequence is executed
endef

SVLOG_SOURCES=\
$(subst $${HPDCACHE_DIR},$(HPDCACHE_DIR),\
$(shell sed -n -e '/.*\.sv/p' \
    $(HPDCACHE_DIR)/rtl/hpdcache.Flist hpdcache.vlt.Flist))

export help_message

.PHONY: help
help:
	$(Q)$(ECHO) "$${help_message}"


.PHONY: $(RUN_LOG)
$(RUN_LOG):
	$(Q)$(ECHO) "make: run (LOG: $@)"
	$(Q)$(MKDIR) $(dir $@)
	$(Q)$(RM) $(TRACE_FILE)
	$(Q)$(BUILD_DIR)/V$(DUT) $(VERILATOR_RUNFLAGS) >& $@
	$(Q)$(ECHO) "RUN FINISHED" >> $@
	$(Q)$(SCANLOG) -pat scripts/scan_patterns/run_patterns.pat \
	    -att scripts/scan_patterns/run_attributes.pat \
	    -nowarn $@  >$@.scan 2>&1

.PHONY: debug
debug: build
	$(Q)$(MKDIR) $(LOG_DIR)
	$(Q)$(RM) $(TRACE_FILE)
	$(Q)$(GDB) $(BUILD_DIR)/V$(DUT) -ex "b sc_main" -ex "run $(VERILATOR_RUNFLAGS)"

.PHONY: cov
cov: $(COV_MERGEFILE)
	$(Q)$(ECHO) "make: compile coverage data"
	$(Q)$(MKDIR) $(COV_DIR)
	$(Q)$(VERILATOR_COV) --annotate $(COV_DIR)/result $<

.PHONY: nonreg
nonreg: nonregression

.PHONY: nonregression
nonregression:
	$(Q)$(ECHO) "Running non-regression testsuite with SEQUENCE=$(SEQUENCE)..."
	$(Q)$(MKDIR) $(LOG_DIR)/nonreg_$(DATE_TIME)
	$(Q)i=1 ; \
	for s in $(shell head -n $(NTESTS) scripts/random_numbers.dat | tr '\n' ' ') ; do \
	    $(ECHO) "[$$i/$(NTESTS)] Running sequence $(SEQUENCE) SEED=$$s" ; \
	    ((i++)) ; \
	    $(MAKE) -s run SEED=$$s \
	            RUN_LOG=$(LOG_DIR)/nonreg_$(DATE_TIME)/$(SEQUENCE)_$$s.log ; \
	done ;
	$(Q)$(SCANLOG) -pat scripts/scan_patterns/run_patterns.pat \
	        -att scripts/scan_patterns/run_attributes.pat \
	        -nowarn $(LOG_DIR)/nonreg_$(DATE_TIME)/$(SEQUENCE)_*.log \
	        |& tee $(LOG_DIR)/nonreg_$(DATE_TIME)/nonreg.scan.log

$(COV_MERGEFILE): $(filter-out $(COV_MERGEFILE), $(wildcard $(COV_DIR)/*.dat))
	$(Q)$(MKDIR) $(COV_DIR)
	$(Q)$(ECHO) "Merging coverage data into the $@ file"
	$(Q)$(VERILATOR_COV) --write $@ $^

$(VERILATE_LOG): print_config $(SVLOG_SOURCES) $(TB_TOP).cpp
	$(Q)$(ECHO) "Verilating the RTL sources... (LOG: $@)"
	$(Q)$(MKDIR) $(dir $@)
	$(Q)$(VERILATOR) --sc $(VERILATOR_FLAGS) -Mdir $(BUILD_DIR) \
	        $(if $(filter $(DISABLE_WAIVERS),1),,scripts/verilate_waivers.vlt) \
	        +incdir+$(HPDCACHE_DIR)/rtl/include \
	        $(SVLOG_SOURCES) \
	        --exe $(TB_TOP).cpp --top-module $(DUT) >& $@
	$(Q)$(ECHO) "VERILATE FINISHED" >> $@
	$(Q)$(SCANLOG) -pat scripts/scan_patterns/verilate_patterns.pat \
	        -nowarn $@ |& tee $@.scan
	$(Q)$(ECHO) "Verilate done"

$(BUILD_LOG): print_config $(VERILATE_LOG) $(TB_TOP).cpp
	$(Q)$(ECHO) "Build the testbench... (LOG: $@)"
	$(Q)$(MKDIR) $(dir $@)
	$(Q)$(MAKE) -C $(BUILD_DIR) -f "V$(DUT).mk" "V$(DUT)" $(VERILATOR_MAKEFLAGS) >& $@
	$(Q)$(ECHO) "BUILD FINISHED" >> $@
	$(Q)$(SCANLOG) -pat scripts/scan_patterns/build_patterns.pat \
	        -nowarn $@ |& tee $@.scan
	$(Q)$(ECHO) "Build done"

.PHONY: clean clean_log clean_cover clean_all distclean
clean:
	$(Q)$(ECHO) "Cleaning build directory..."
	$(Q)$(RM) -r $(BUILD_DIR)

clean_log:
	$(Q)$(ECHO) "Cleaning logs directory..."
	$(Q)$(RM) -r $(LOG_DIR)

clean_cover:
	$(Q)$(ECHO) "Cleaning coverage directory..."
	$(Q)$(RM) -r $(COV_DIR)

clean_all: clean clean_log clean_cover
distclean: clean_all

print_config:
	@printf "CONF_HPDCACHE_PA_WIDTH=$(CONF_HPDCACHE_PA_WIDTH)\n"
	@printf "CONF_HPDCACHE_SETS=$(CONF_HPDCACHE_SETS)\n"
	@printf "CONF_HPDCACHE_WAYS=$(CONF_HPDCACHE_WAYS)\n"
	@printf "CONF_HPDCACHE_WORD_WIDTH=$(CONF_HPDCACHE_WORD_WIDTH)\n"
	@printf "CONF_HPDCACHE_CL_WORDS=$(CONF_HPDCACHE_CL_WORDS)\n"
	@printf "CONF_HPDCACHE_REQ_WORDS=$(CONF_HPDCACHE_REQ_WORDS)\n"
	@printf "CONF_HPDCACHE_REQ_TRANS_ID_WIDTH=$(CONF_HPDCACHE_REQ_TRANS_ID_WIDTH)\n"
	@printf "CONF_HPDCACHE_REQ_SRC_ID_WIDTH=$(CONF_HPDCACHE_REQ_SRC_ID_WIDTH)\n"
	@printf "CONF_HPDCACHE_VICTIM_SEL=$(CONF_HPDCACHE_VICTIM_SEL)\n"
	@printf "CONF_HPDCACHE_DATA_WAYS_PER_RAM_WORD=$(CONF_HPDCACHE_DATA_WAYS_PER_RAM_WORD)\n"
	@printf "CONF_HPDCACHE_DATA_SETS_PER_RAM=$(CONF_HPDCACHE_DATA_SETS_PER_RAM)\n"
	@printf "CONF_HPDCACHE_DATA_RAM_WBYTEENABLE=$(CONF_HPDCACHE_DATA_RAM_WBYTEENABLE)\n"
	@printf "CONF_HPDCACHE_ACCESS_WORDS=$(CONF_HPDCACHE_ACCESS_WORDS)\n"
	@printf "CONF_HPDCACHE_WBUF_DIR_ENTRIES=$(CONF_HPDCACHE_WBUF_DIR_ENTRIES)\n"
	@printf "CONF_HPDCACHE_WBUF_DATA_ENTRIES=$(CONF_HPDCACHE_WBUF_DATA_ENTRIES)\n"
	@printf "CONF_HPDCACHE_WBUF_WORDS=$(CONF_HPDCACHE_WBUF_WORDS)\n"
	@printf "CONF_HPDCACHE_WBUF_TIMECNT_WIDTH=$(CONF_HPDCACHE_WBUF_TIMECNT_WIDTH)\n"
	@printf "CONF_HPDCACHE_WBUF_SEND_FEEDTHROUGH=$(CONF_HPDCACHE_WBUF_SEND_FEEDTHROUGH)\n"
	@printf "CONF_HPDCACHE_MSHR_SETS=$(CONF_HPDCACHE_MSHR_SETS)\n"
	@printf "CONF_HPDCACHE_MSHR_WAYS=$(CONF_HPDCACHE_MSHR_WAYS)\n"
	@printf "CONF_HPDCACHE_MSHR_WAYS_PER_RAM_WORD=$(CONF_HPDCACHE_MSHR_WAYS_PER_RAM_WORD)\n"
	@printf "CONF_HPDCACHE_MSHR_SETS_PER_RAM=$(CONF_HPDCACHE_MSHR_SETS_PER_RAM)\n"
	@printf "CONF_HPDCACHE_MSHR_RAM_WBYTEENABLE=$(CONF_HPDCACHE_MSHR_RAM_WBYTEENABLE)\n"
	@printf "CONF_HPDCACHE_MSHR_USE_REGBANK=$(CONF_HPDCACHE_MSHR_USE_REGBANK)\n"
	@printf "CONF_HPDCACHE_REFILL_FIFO_DEPTH=$(CONF_HPDCACHE_REFILL_FIFO_DEPTH)\n"
	@printf "CONF_HPDCACHE_REFILL_CORE_RSP_FEEDTHROUGH=$(CONF_HPDCACHE_REFILL_CORE_RSP_FEEDTHROUGH)\n"
	@printf "CONF_HPDCACHE_RTAB_ENTRIES=$(CONF_HPDCACHE_RTAB_ENTRIES)\n"
	@printf "CONF_HPDCACHE_FLUSH_ENTRIES=$(CONF_HPDCACHE_FLUSH_ENTRIES)\n"
	@printf "CONF_HPDCACHE_FLUSH_FIFO_DEPTH=$(CONF_HPDCACHE_FLUSH_FIFO_DEPTH)\n"
	@printf "CONF_HPDCACHE_MEM_ADDR_WIDTH=$(CONF_HPDCACHE_MEM_ADDR_WIDTH)\n"
	@printf "CONF_HPDCACHE_MEM_ID_WIDTH=$(CONF_HPDCACHE_MEM_ID_WIDTH)\n"
	@printf "CONF_HPDCACHE_MEM_DATA_WIDTH=$(CONF_HPDCACHE_MEM_DATA_WIDTH)\n"
	@printf "CONF_HPDCACHE_WT_ENABLE=$(CONF_HPDCACHE_WT_ENABLE)\n"
	@printf "CONF_HPDCACHE_WB_ENABLE=$(CONF_HPDCACHE_WB_ENABLE)\n"
