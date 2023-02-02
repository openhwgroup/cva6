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
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
#
###############################################################################
#
# Common code for simulation Makefiles.
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

###############################################################################
# Common functions

# Map multiple flag values to "YES" or NO
# Use like this, to test variable MYVAR
# ifeq ($(call IS_YES($(MYVAR)),YES)
YES_VALS=Y YES 1 y yes TRUE true
IS_YES=$(if $(filter $(YES_VALS),$(1)),YES,NO)
NO_VALS=N NO 0 n no FALSE false
IS_NO=$(if $(filter $(NO_VALS),$(1)),NO,YES)

# Resolve flags for tool options in precdence order
# Call as: MY_FLAG=$(call RESOLVE_FLAG3,$(FIRST),$(SECOND))
# The first resolved variable in order of FIRST,SECOND will be assigned to MY_FLAG
RESOLVE_FLAG2=$(if $(1),$(1),$(2))

###############################################################################
# Common variables
BANNER=*******************************************************************************************

###############################################################################
# Fetch commands
ifndef CV_CORE_REPO
$(error Must define a CV_CORE_REPO to use the common makefile)
endif

ifndef RISCVDV_REPO
$(error Must define a RISCVDV_REPO to use the common makefile)
endif

ifndef EMBENCH_REPO
$(warning Must define a EMBENCH_REPO to use the common makefile)
endif

ifndef COMPLIANCE_REPO
$(error Must define a COMPLIANCE_REPO to use the common makefile)
endif

ifndef DPI_DASM_SPIKE_REPO
$(warning Must define a DPI_DASM_SPIKE_REPO to use the common makefile)
endif

###############################################################################
# Generate command to clone or symlink the core RTL
ifeq ($(CV_CORE_PATH),)
  ifeq ($(CV_CORE_BRANCH), master)
    TMP = git clone $(CV_CORE_REPO) $(CV_CORE_PKG)
  else
    TMP = git clone -b $(CV_CORE_BRANCH) --single-branch $(CV_CORE_REPO) $(CV_CORE_PKG)
  endif

  # If a TAG is specified, the HASH is not considered
  ifeq ($(CV_CORE_TAG), none)
    ifeq ($(CV_CORE_HASH), head)
      CLONE_CV_CORE_CMD = $(TMP)
    else
      CLONE_CV_CORE_CMD = $(TMP); cd $(CV_CORE_PKG); git checkout $(CV_CORE_HASH)
    endif
  else
    CLONE_CV_CORE_CMD = $(TMP); cd $(CV_CORE_PKG); git checkout tags/$(CV_CORE_TAG)
  endif
else
  CLONE_CV_CORE_CMD = ln -s $(CV_CORE_PATH) $(CV_CORE_PKG)
endif

###############################################################################
# Generate command to clone RISCV-DV (Google's random instruction generator)
ifeq ($(RISCVDV_BRANCH), master)
  TMP3 = git clone $(RISCVDV_REPO) --recurse $(RISCVDV_PKG)
else
  TMP3 = git clone -b $(RISCVDV_BRANCH) --single-branch $(RISCVDV_REPO) --recurse $(RISCVDV_PKG)
endif

ifeq ($(RISCVDV_HASH), head)
  CLONE_RISCVDV_CMD = $(TMP3)
else
  CLONE_RISCVDV_CMD = $(TMP3); cd $(RISCVDV_PKG); git checkout $(RISCVDV_HASH)
endif
# RISCV-DV repo var end

###############################################################################
# Generate command to clone the RISCV Compliance Test-suite
ifeq ($(COMPLIANCE_BRANCH), master)
  TMP4 = git clone $(COMPLIANCE_REPO) --recurse $(COMPLIANCE_PKG)
else
  TMP4 = git clone -b $(COMPLIANCE_BRANCH) --single-branch $(COMPLIANCE_REPO) --recurse $(COMPLIANCE_PKG)
endif

ifeq ($(COMPLIANCE_HASH), head)
  CLONE_COMPLIANCE_CMD = $(TMP4)
else
  CLONE_COMPLIANCE_CMD = $(TMP4); cd $(COMPLIANCE_PKG); sleep 2; git checkout $(COMPLIANCE_HASH)
endif
# RISCV Compliance repo var end

###############################################################################
# Generate command to clone EMBench (Embedded Benchmarking suite)
ifeq ($(EMBENCH_BRANCH), master)
  TMP5 = git clone $(EMBENCH_REPO) --recurse $(EMBENCH_PKG)
else
  TMP5 = git clone -b $(EMBENCH_BRANCH) --single-branch $(EMBENCH_REPO) --recurse $(EMBENCH_PKG)
endif

ifeq ($(EMBENCH_HASH), head)
  CLONE_EMBENCH_CMD = $(TMP5)
else
  CLONE_EMBENCH_CMD = $(TMP5); cd $(EMBENCH_PKG); git checkout $(EMBENCH_HASH)
endif
# EMBench repo var end

###############################################################################
# Generate command to clone Spike for the Disassembler DPI (used in the isacov model)
ifeq ($(DPI_DASM_SPIKE_BRANCH), master)
  TMP7 = git clone $(DPI_DASM_SPIKE_REPO) --recurse $(DPI_DASM_SPIKE_PKG)
else
  TMP7 = git clone -b $(DPI_DASM_SPIKE_BRANCH) --single-branch $(DPI_DASM_SPIKE_REPO) --recurse $(DPI_DASM_SPIKE_PKG)
endif

ifeq ($(DPI_DASM_SPIKE_HASH), head)
  CLONE_DPI_DASM_SPIKE_CMD = $(TMP7)
else
  CLONE_DPI_DASM_SPIKE_CMD = $(TMP7); cd $(DPI_DASM_SPIKE_PKG); git checkout $(DPI_DASM_SPIKE_HASH)
endif
# DPI_DASM Spike repo var end

###############################################################################
# Generate command to clone Verilab SVLIB
ifeq ($(SVLIB_BRANCH), master)
  TMP8 = git clone $(SVLIB_REPO) --recurse $(SVLIB_PKG)
else
  TMP8 = git clone -b $(SVLIB_BRANCH) --single-branch $(SVLIB_REPO) --recurse $(SVLIB_PKG)
endif

ifeq ($(SVLIB_HASH), head)
  CLONE_SVLIB_CMD = $(TMP8)
else
  CLONE_SVLIB_CMD = $(TMP8); cd $(SVLIB_PKG); git checkout $(SVLIB_HASH)
endif
# SVLIB repo var end

###############################################################################
# Imperas Instruction Set Simulator

DV_OVPM_HOME    = $(CORE_V_VERIF)/vendor_lib/imperas
DV_OVPM_MODEL   = $(DV_OVPM_HOME)/imperas_DV_COREV
DV_OVPM_DESIGN  = $(DV_OVPM_HOME)/design
OVP_MODEL_DPI   = $(DV_OVPM_MODEL)/bin/Linux64/imperas_CV32.dpi.so
#OVP_CTRL_FILE   = $(DV_OVPM_DESIGN)/riscv_CV32E40P.ic

###############################################################################
# Run the yaml2make scripts

ifeq ($(VERBOSE),1)
YAML2MAKE_DEBUG = --debug
else
YAML2MAKE_DEBUG =
endif

# If the gen_corev-dv target is defined then read in a test defintions file
YAML2MAKE = $(CORE_V_VERIF)/bin/yaml2make
ifneq ($(filter gen_corev-dv,$(MAKECMDGOALS)),)
ifeq ($(TEST),)
$(error ERROR must specify a TEST variable with gen_corev-dv target)
endif
GEN_FLAGS_MAKE := $(shell $(YAML2MAKE) --test=$(TEST) --yaml=corev-dv.yaml $(YAML2MAKE_DEBUG) --prefix=GEN --core=$(CV_CORE))
ifeq ($(GEN_FLAGS_MAKE),)
$(error ERROR Could not find corev-dv.yaml for test: $(TEST))
endif
include $(GEN_FLAGS_MAKE)
endif

# If the test target is defined then read in a test defintions file
TEST_YAML_PARSE_TARGETS=test waves cov hex clean_hex veri-test dsim-test xrun-test bsp
ifneq ($(filter $(TEST_YAML_PARSE_TARGETS),$(MAKECMDGOALS)),)
ifeq ($(TEST),)
$(error ERROR! must specify a TEST variable)
endif
TEST_FLAGS_MAKE := $(shell $(YAML2MAKE) --test=$(TEST) --yaml=test.yaml  $(YAML2MAKE_DEBUG) --run-index=$(u) --prefix=TEST --core=$(CV_CORE))
ifeq ($(TEST_FLAGS_MAKE),)
$(error ERROR Could not find test.yaml for test: $(TEST))
endif
include $(TEST_FLAGS_MAKE)
endif

###############################################################################
# cfg
CFGYAML2MAKE = $(CORE_V_VERIF)/bin/cfgyaml2make
CFG_YAML_PARSE_TARGETS=comp ldgen comp_corev-dv gen_corev-dv test hex clean_hex corev-dv sanity-veri-run bsp
ifneq ($(filter $(CFG_YAML_PARSE_TARGETS),$(MAKECMDGOALS)),)
ifneq ($(CFG),)
CFG_FLAGS_MAKE := $(shell $(CFGYAML2MAKE) --yaml=$(CFG).yaml $(YAML2MAKE_DEBUG) --prefix=CFG --core=$(CV_CORE))
ifeq ($(CFG_FLAGS_MAKE),)
$(error ERROR Error finding or parsing configuration: $(CFG).yaml)
endif
include $(CFG_FLAGS_MAKE)
endif
endif

###############################################################################
# Determine the values of the CV_SW_ variables.
# The priority order is ENV > TEST > CFG.

ifndef CV_SW_TOOLCHAIN
ifdef  TEST_CV_SW_TOOLCHAIN
CV_SW_TOOLCHAIN = $(TEST_CV_SW_TOOLCHAIN)
else
ifdef  CFG_CV_SW_TOOLCHAIN
CV_SW_TOOLCHAIN = $(CFG_CV_SW_TOOLCHAIN)
else
$(error CV_SW_TOOLCHAIN not defined in either the shell environment, test.yaml or cfg.yaml)
endif
endif
endif

ifndef CV_SW_PREFIX
ifdef  TEST_CV_SW_PREFIX
CV_SW_PREFIX = $(TEST_CV_SW_PREFIX)
else
ifdef  CFG_CV_SW_PREFIX
CV_SW_PREFIX = $(CFG_CV_SW_PREFIX)
else
$(error CV_SW_PREFIX not defined in either the shell environment, test.yaml or cfg.yaml)
endif
endif
endif

ifndef CV_SW_MARCH
ifdef  TEST_CV_SW_MARCH
CV_SW_MARCH = $(TEST_CV_SW_MARCH)
else
ifdef  CFG_CV_SW_MARCH
CV_SW_MARCH = $(CFG_CV_SW_MARCH)
else
CV_SW_MARCH = rv32imc
$(warning CV_SW_MARCH not defined in either the shell environment, test.yaml or cfg.yaml)
endif
endif
endif

ifndef CV_SW_CC
ifdef  TEST_CV_SW_CC
CV_SW_CC = $(TEST_CV_SW_CC)
else
ifdef  CFG_CV_SW_CC
CV_SW_CC = $(CFG_CV_SW_CC)
else
CV_SW_CC = gcc
$(warning CV_SW_CC not defined in either the shell environment, test.yaml or cfg.yaml)
endif
endif
endif

ifndef CV_SW_CFLAGS
ifdef  TEST_CV_SW_CFLAGS
CV_SW_CFLAGS = $(TEST_CV_SW_CFLAGS)
else
ifdef  CFG_CV_SW_CFLAGS
CV_SW_CFLAGS = $(CFG_CV_SW_CFLAGS)
else
$(warning CV_SW_CFLAGS not defined in either the shell environment, test.yaml or cfg.yaml)
endif
endif
endif

RISCV            = $(CV_SW_TOOLCHAIN)
RISCV_PREFIX     = $(CV_SW_PREFIX)
RISCV_EXE_PREFIX = $(RISCV)/bin/$(RISCV_PREFIX)

RISCV_MARCH      = $(CV_SW_MARCH)
RISCV_CC         = $(CV_SW_CC)
RISCV_CFLAGS     = $(CV_SW_CFLAGS)

CFLAGS ?= -Os -g -static -mabi=ilp32 -march=$(RISCV_MARCH) -Wall -pedantic $(RISCV_CFLAGS)

$(warning RISCV set to $(RISCV))
$(warning RISCV_PREFIX set to $(RISCV_PREFIX))
$(warning RISCV_EXE_PREFIX set to $(RISCV_EXE_PREFIX))
$(warning RISCV_MARCH set to $(RISCV_MARCH))
$(warning RISCV_CC set to $(RISCV_CC))
$(warning RISCV_CFLAGS set to $(RISCV_CFLAGS))
#$(error STOP IT!)

# Keeping this around just in case it is needed again
#ifeq ($(firstword $(subst _, ,$(TEST))),pulp)
#  CFLAGS = -Os -g -D__riscv__=1 -D__LITTLE_ENDIAN__=1 -march=rv32imcxpulpv2 -Wa,-march=rv32imcxpulpv2 -fdata-sections -ffunction-sections -fdiagnostics-color=always
#endif

ASM       ?= ../../tests/asm
ASM_DIR   ?= $(ASM)

# CORE FIRMWARE vars. The C and assembler test-programs
# were once collectively known as "Core Firmware".
#
# Note that the DSIM targets allow for writing the log-files to arbitrary
# locations, so all of these paths are absolute, except those used by Verilator.
CORE_TEST_DIR                        = $(CORE_V_VERIF)/$(CV_CORE_LC)/tests/programs
BSP                                  = $(CORE_V_VERIF)/$(CV_CORE_LC)/bsp
FIRMWARE                             = $(CORE_TEST_DIR)/firmware
VERI_FIRMWARE                        = ../../tests/core/firmware
ASM_PROG                            ?= my_hello_world
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


# Thales verilator testbench compilation start

SUPPORTED_COMMANDS := vsim-firmware-unit-test questa-unit-test questa-unit-test-gui dsim-unit-test vcs-unit-test
SUPPORTS_MAKE_ARGS := $(filter $(firstword $(MAKECMDGOALS)), $(SUPPORTED_COMMANDS))

ifneq "$(SUPPORTS_MAKE_ARGS)" ""
  UNIT_TEST := $(wordlist 2,$(words $(MAKECMDGOALS)),$(MAKECMDGOALS))
  $(eval $(UNIT_TEST):;@:)
  UNIT_TEST_CMD := 1
else
 UNIT_TEST_CMD := 0
endif

COMPLIANCE_UNIT_TEST = $(subst _,-,$(UNIT_TEST))

FIRMWARE_UNIT_TEST_OBJS   =  	$(addsuffix .o, \
				$(basename $(wildcard $(RISCV_TESTS)/rv32*/$(UNIT_TEST).S)) \
				$(basename $(wildcard $(RISCV_COMPLIANCE_TESTS)*/$(COMPLIANCE_UNIT_TEST).S)))

# Thales verilator testbench compilation end

###############################################################################
# The sanity rule runs whatever is currently deemed to be the minimal test that
# must be able to run (and pass!) prior to generating a pull-request.
sanity: hello-world


###############################################################################
# Code generators
# New agent is pulled from moore.io temp site
new-agent:
	mkdir -p $(CORE_V_VERIF)/temp
	wget --no-check-certificate -q https://mooreio.com/packages/uvm_gen.tgz -P $(CORE_V_VERIF)/temp
	tar xzf $(CORE_V_VERIF)/temp/uvm_gen.tgz -C $(CORE_V_VERIF)/temp
	cd $(CORE_V_VERIF)/temp && ./src/new_agent_basic.py $(CORE_V_VERIF)/lib/uvm_agents "OpenHW Group"
	rm -rf $(CORE_V_VERIF)/temp



# corev-dv tests needs an added run_index_suffix, blank for other tests
ifeq ($(shell echo $(TEST) | head -c 6),corev_)
export OPT_RUN_INDEX_SUFFIX=_$(RUN_INDEX)
endif

###############################################################################
# Rule to generate hex (loadable by simulators) from elf
#    $@ is the file being generated.
#    $< is first prerequiste.
#    $^ is all prerequistes.
#    $* is file_name (w/o extension) of target
%.hex: %.elf
	@echo "$(BANNER)"
	@echo "* Generating hexfile, readelf and objdump files"
	@echo "$(BANNER)"
	$(RISCV_EXE_PREFIX)objcopy -O verilog \
		$< \
		$@
	$(RISCV_EXE_PREFIX)readelf -a $< > $*.readelf
	$(RISCV_EXE_PREFIX)objdump \
		-d \
		-M no-aliases \
		-M numeric \
		-S \
		$*.elf > $*.objdump
	$(RISCV_EXE_PREFIX)objdump \
    	-d \
        -S \
		-M no-aliases \
		-M numeric \
        -l \
		$*.elf | ${CORE_V_VERIF}/bin/objdump2itb - > $*.itb

# Patterned targets to generate ELF.  Used only if explicit targets do not match.
#
.PRECIOUS : %.elf

# Single rule for compiling test source into an ELF file
# For directed tests, TEST_FILES gathers all of the .S and .c files in a test directory
# For corev_ tests, TEST_FILES will only point to the specific .S for the RUN_INDEX and TEST_NAME provided to make
ifeq ($(shell echo $(TEST) | head -c 6),corev_)
TEST_FILES        = $(filter %.c %.S,$(wildcard  $(SIM_TEST_PROGRAM_RESULTS)/$(TEST_NAME)$(OPT_RUN_INDEX_SUFFIX).S))
else
TEST_FILES        = $(filter %.c %.S,$(wildcard  $(TEST_TEST_DIR)/*))
endif

# If a test defines "default_cflags" in its yaml, then it is responsible to define ALL flags
# Otherwise add the default cflags in the variable CFLAGS defined above
ifneq ($(TEST_DEFAULT_CFLAGS),)
TEST_CFLAGS += $(TEST_DEFAULT_CFLAGS)
else
TEST_CFLAGS += $(CFLAGS)
endif

# Optionally use linker script provided in test directory
# this must be evaluated at access time, so ifeq/ifneq does
# not get parsed correctly
TEST_RESULTS_LD = $(addprefix $(SIM_TEST_PROGRAM_RESULTS)/, link.ld)
TEST_LD         = $(addprefix $(TEST_TEST_DIR)/, link.ld)

LD_LIBRARY 	= $(if $(wildcard $(TEST_RESULTS_LD)),-L $(SIM_TEST_PROGRAM_RESULTS),$(if $(wildcard $(TEST_LD)),-L $(TEST_TEST_DIR),))
LD_FILE 	= $(if $(wildcard $(TEST_RESULTS_LD)),$(TEST_RESULTS_LD),$(if $(wildcard $(TEST_LD)),$(TEST_LD),$(BSP)/link.ld))
LD_LIBRARY += -L $(SIM_BSP_RESULTS)

ifeq ($(TEST_FIXED_ELF),1)
%.elf:
	@echo "$(BANNER)"
	@echo "* Copying fixed ELF test program to $(@)"
	@echo "$(BANNER)"
	mkdir -p $(SIM_TEST_PROGRAM_RESULTS)
	cp $(TEST_TEST_DIR)/$(TEST).elf $@
else
%.elf: $(TEST_FILES)
	mkdir -p $(SIM_TEST_PROGRAM_RESULTS)
	make bsp
	@echo "$(BANNER)"
	@echo "* Compiling test-program $@"
	@echo "$(BANNER)"
	$(RISCV_EXE_PREFIX)$(RISCV_CC) \
		$(CFG_CFLAGS) \
		$(TEST_CFLAGS) \
		$(RISCV_CFLAGS) \
		-I $(ASM) \
		-I $(BSP) \
		-o $@ \
		-nostartfiles \
		$(TEST_FILES) \
		-T $(LD_FILE) \
		$(LD_LIBRARY) \
		-lcv-verif
endif

.PHONY: hex

# Shorthand target to only build the firmware using the hex and elf suffix rules above
hex: $(SIM_TEST_PROGRAM_RESULTS)/$(TEST_PROGRAM)$(OPT_RUN_INDEX_SUFFIX).hex

bsp:
	@echo "$(BANNER)"
	@echo "* Compiling the BSP"
	@echo "$(BANNER)"
	mkdir -p $(SIM_BSP_RESULTS)
	cp $(BSP)/Makefile $(SIM_BSP_RESULTS)
	make -C $(SIM_BSP_RESULTS) \
		VPATH=$(BSP) \
		RISCV=$(RISCV) \
		RISCV_PREFIX=$(RISCV_PREFIX) \
		RISCV_EXE_PREFIX=$(RISCV_EXE_PREFIX) \
		RISCV_MARCH=$(RISCV_MARCH) \
		RISCV_CC=$(RISCV_CC) \
		RISCV_CFLAGS="$(RISCV_CFLAGS)" \
		all

vars_bsp:
	make vars -C $(BSP) RISCV=$(RISCV) RISCV_PREFIX=$(RISCV_PREFIX) RISCV_EXE_PREFIX=$(RISCV_EXE_PREFIX) RISCV_MARCH=$(RISCV_MARCH)

clean_bsp:
	make -C $(BSP) clean
	rm -rf $(SIM_BSP_RESULTS)


# compile and dump RISCV_TESTS only
#$(CV32_RISCV_TESTS_FIRMWARE)/cv32_riscv_tests_firmware.elf: $(CV32_RISCV_TESTS_FIRMWARE_OBJS) $(RISCV_TESTS_OBJS) \
#							$(CV32_RISCV_TESTS_FIRMWARE)/link.ld
#	$(RISCV_EXE_PREFIX)gcc -g -Os -mabi=ilp32 -march=rv32imc -ffreestanding -nostdlib -o $@ \
#		$(RISCV_TEST_INCLUDES) \
#		-Wl,-Bstatic,-T,$(CV32_RISCV_TESTS_FIRMWARE)/link.ld,-Map,$(CV32_RISCV_TESTS_FIRMWARE)/cv32_riscv_tests_firmware.map,--strip-debug \
#		$(CV32_RISCV_TESTS_FIRMWARE_OBJS) $(RISCV_TESTS_OBJS) -lgcc

#$(CV32_RISCV_TESTS_FIRMWARE)/cv32_riscv_tests_firmware.elf: $(CV32_RISCV_TESTS_FIRMWARE_OBJS) $(RISCV_TESTS_OBJS) \
#							$(CV32_RISCV_TESTS_FIRMWARE)/link.ld
../../tests/core/cv32_riscv_tests_firmware/cv32_riscv_tests_firmware.elf: $(CV32_RISCV_TESTS_FIRMWARE_OBJS) $(RISCV_TESTS_OBJS)
	$(RISCV_EXE_PREFIX)gcc $(CFLAGS) -ffreestanding -nostdlib -o $@ \
		$(RISCV_TEST_INCLUDES) \
		-Wl,-Bstatic,-T,$(CV32_RISCV_TESTS_FIRMWARE)/link.ld,-Map,$(CV32_RISCV_TESTS_FIRMWARE)/cv32_riscv_tests_firmware.map,--strip-debug \
		$(CV32_RISCV_TESTS_FIRMWARE_OBJS) $(RISCV_TESTS_OBJS) -lgcc

$(CV32_RISCV_TESTS_FIRMWARE)/start.o: $(CV32_RISCV_TESTS_FIRMWARE)/start.S
	$(RISCV_EXE_PREFIX)gcc -c $(CFLAGS) -o $@ $<

$(CV32_RISCV_TESTS_FIRMWARE)/%.o: $(CV32_RISCV_TESTS_FIRMWARE)/%.c
	$(RISCV_EXE_PREFIX)gcc -c $(CFLAGS) --std=c99 -Wall \
		$(RISCV_TEST_INCLUDES) \
		-ffreestanding -nostdlib -o $@ $<

# compile and dump RISCV_COMPLIANCE_TESTS only
$(CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE)/cv32_riscv_compliance_tests_firmware.elf: $(CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE_OBJS) $(COMPLIANCE_TEST_OBJS) \
							$(CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE)/link.ld
	$(RISCV_EXE_PREFIX)gcc $(CFLAGS) -ffreestanding -nostdlib -o $@ \
		-D RUN_COMPLIANCE \
		$(RISCV_TEST_INCLUDES) \
		-Wl,-Bstatic,-T,$(CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE)/link.ld,-Map,$(CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE)/cv32_riscv_compliance_tests_firmware.map,--strip-debug \
		$(CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE_OBJS) $(COMPLIANCE_TEST_OBJS) -lgcc

$(CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE)/start.o: $(CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE)/start.S
	$(RISCV_EXE_PREFIX)gcc -c $(CFLAGS) -D RUN_COMPLIANCE -o $@ $<

$(CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE)/%.o: $(CV32_RISCV_COMPLIANCE_TESTS_FIRMWARE)/%.c
	$(RISCV_EXE_PREFIX)gcc -c $(CFLAGS) --std=c99 -Wall \
		$(RISCV_TEST_INCLUDES) \
		-ffreestanding -nostdlib -o $@ $<

# compile and dump picorv firmware

# Thales start
$(FIRMWARE)/firmware_unit_test.elf: $(FIRMWARE_OBJS) $(FIRMWARE_UNIT_TEST_OBJS) $(FIRMWARE)/link.ld
	$(RISCV_EXE_PREFIX)gcc $(CFLAGS) -ffreestanding -nostdlib -o $@ \
		$(RISCV_TEST_INCLUDES) \
		-D RUN_COMPLIANCE \
		-Wl,-Bstatic,-T,$(FIRMWARE)/link.ld,-Map,$(FIRMWARE)/firmware.map,--strip-debug \
		$(FIRMWARE_OBJS) $(FIRMWARE_UNIT_TEST_OBJS) -lgcc
# Thales end

$(FIRMWARE)/firmware.elf: $(FIRMWARE_OBJS) $(FIRMWARE_TEST_OBJS) $(COMPLIANCE_TEST_OBJS) $(FIRMWARE)/link.ld
	$(RISCV_EXE_PREFIX)gcc $(CFLAGS) -ffreestanding -nostdlib -o $@ \
		$(RISCV_TEST_INCLUDES) \
		-D RUN_COMPLIANCE \
		-Wl,-Bstatic,-T,$(FIRMWARE)/link.ld,-Map,$(FIRMWARE)/firmware.map,--strip-debug \
		$(FIRMWARE_OBJS) $(FIRMWARE_TEST_OBJS) $(COMPLIANCE_TEST_OBJS) -lgcc

#$(FIRMWARE)/start.o: $(FIRMWARE)/start.S
#	$(RISCV_EXE_PREFIX)gcc -c -march=rv32imc -g -D RUN_COMPLIANCE -o $@ $<

# Thales start
$(FIRMWARE)/start.o: $(FIRMWARE)/start.S
ifeq ($(UNIT_TEST_CMD),1)
ifeq ($(FIRMWARE_UNIT_TEST_OBJS),)
$(error no existing unit test in argument )
else
	$(RISCV_EXE_PREFIX)gcc -c $(CFLAGS) -D RUN_COMPLIANCE  -DUNIT_TEST_CMD=$(UNIT_TEST_CMD) -DUNIT_TEST=$(UNIT_TEST) -DUNIT_TEST_RET=$(UNIT_TEST)_ret -o $@ $<
endif
else
	$(RISCV_EXE_PREFIX)gcc -c $(CFLAGS) -D RUN_COMPLIANCE  -DUNIT_TEST_CMD=$(UNIT_TEST_CMD) -o $@ $<
endif
# Thales end

$(FIRMWARE)/%.o: $(FIRMWARE)/%.c
	$(RISCV_EXE_PREFIX)gcc -c $(CFLAGS) --std=c99 \
		$(RISCV_TEST_INCLUDES) \
		-ffreestanding -nostdlib -o $@ $<

$(RISCV_TESTS)/rv32ui/%.o: $(RISCV_TESTS)/rv32ui/%.S $(RISCV_TESTS)/riscv_test.h \
			$(RISCV_TESTS)/macros/scalar/test_macros.h
	$(RISCV_EXE_PREFIX)gcc -c $(CFLAGS) -o $@ \
		$(RISCV_TEST_INCLUDES) \
		-DTEST_FUNC_NAME=$(notdir $(basename $<)) \
		-DTEST_FUNC_TXT='"$(notdir $(basename $<))"' \
		-DTEST_FUNC_RET=$(notdir $(basename $<))_ret $<

$(RISCV_TESTS)/rv32um/%.o: $(RISCV_TESTS)/rv32um/%.S $(RISCV_TESTS)/riscv_test.h \
			$(RISCV_TESTS)/macros/scalar/test_macros.h
	$(RISCV_EXE_PREFIX)gcc -c $(CFLAGS) -o $@ \
		$(RISCV_TEST_INCLUDES) \
		-DTEST_FUNC_NAME=$(notdir $(basename $<)) \
		-DTEST_FUNC_TXT='"$(notdir $(basename $<))"' \
		-DTEST_FUNC_RET=$(notdir $(basename $<))_ret $<

$(RISCV_TESTS)/rv32uc/%.o: $(RISCV_TESTS)/rv32uc/%.S $(RISCV_TESTS)/riscv_test.h \
			$(RISCV_TESTS)/macros/scalar/test_macros.h
	$(RISCV_EXE_PREFIX)gcc -c $(CFLAGS) -o $@ \
		$(RISCV_TEST_INCLUDES) \
		-DTEST_FUNC_NAME=$(notdir $(basename $<)) \
		-DTEST_FUNC_TXT='"$(notdir $(basename $<))"' \
		-DTEST_FUNC_RET=$(notdir $(basename $<))_ret $<

# Build riscv_compliance_test. Make sure to escape dashes to underscores
$(RISCV_COMPLIANCE_TESTS)/%.o: $(RISCV_COMPLIANCE_TESTS)/%.S $(RISCV_COMPLIANCE_TESTS)/riscv_test.h \
			$(RISCV_COMPLIANCE_TESTS)/test_macros.h $(RISCV_COMPLIANCE_TESTS)/compliance_io.h \
			$(RISCV_COMPLIANCE_TESTS)/compliance_test.h
	$(RISCV_EXE_PREFIX)gcc -c $(CFLAGS) -o $@ \
		-DTEST_FUNC_NAME=$(notdir $(subst -,_,$(basename $<))) \
		-DTEST_FUNC_TXT='"$(notdir $(subst -,_,$(basename $<)))"' \
		-DTEST_FUNC_RET=$(notdir $(subst -,_,$(basename $<)))_ret $<

# in dsim
.PHONY: dsim-unit-test
dsim-unit-test:  firmware-unit-test-clean
dsim-unit-test:  $(FIRMWARE)/firmware_unit_test.hex
dsim-unit-test: ALL_VSIM_FLAGS += "+firmware=$(FIRMWARE)/firmware_unit_test.hex +elf_file=$(FIRMWARE)/firmware_unit_test.elf"
dsim-unit-test: dsim-firmware-unit-test

# in vcs
.PHONY: firmware-vcs-run
firmware-vcs-run: vcsify $(FIRMWARE)/firmware.hex
	./simv $(SIMV_FLAGS) "+firmware=$(FIRMWARE)/firmware.hex"

.PHONY: firmware-vcs-run-gui
firmware-vcs-run-gui: VCS_FLAGS+=-debug_all
firmware-vcs-run-gui: vcsify $(FIRMWARE)/firmware.hex
	./simv $(SIMV_FLAGS) -gui "+firmware=$(FIRMWARE)/firmware.hex"

.PHONY: vcs-unit-test
vcs-unit-test:  firmware-unit-test-clean
vcs-unit-test:  $(FIRMWARE)/firmware_unit_test.hex
vcs-unit-test:  vcsify $(FIRMWARE)/firmware_unit_test.hex
vcs-unit-test:  vcs-run

###############################################################################
# Build disassembler

DPI_DASM_SRC    = $(DPI_DASM_PKG)/dpi_dasm.cxx $(DPI_DASM_PKG)/spike/disasm.cc $(DPI_DASM_SPIKE_PKG)/disasm/regnames.cc
DPI_DASM_ARCH   = $(shell uname)$(shell getconf LONG_BIT)
DPI_DASM_LIB    = $(DPI_DASM_PKG)/lib/$(DPI_DASM_ARCH)/libdpi_dasm.so
DPI_DASM_CFLAGS = -shared -fPIC -std=c++11
DPI_DASM_INC    = -I$(DPI_DASM_PKG) -I$(DPI_INCLUDE) -I$(DPI_DASM_SPIKE_PKG)/riscv -I$(DPI_DASM_SPIKE_PKG)/softfloat
DPI_DASM_CXX    = g++

dpi_dasm: $(DPI_DASM_SPIKE_PKG)
	$(DPI_DASM_CXX) $(DPI_DASM_CFLAGS) $(DPI_DASM_INC) $(DPI_DASM_SRC) -o $(DPI_DASM_LIB)

###############################################################################
# Build SVLIB DPI

SVLIB_SRC    = $(SVLIB_PKG)/svlib/src/dpi/svlib_dpi.c
SVLIB_CFLAGS = -shared -fPIC
SVLIB_LIB    = $(SVLIB_PKG)/../svlib_dpi.so
SVLIB_CXX    = gcc

svlib: $(SVLIB_PKG)
	$(SVLIB_CXX) $(SVLIB_CFLAGS) $(SVLIB) $(SVLIB_SRC) -I$(DPI_INCLUDE) -o $(SVLIB_LIB)

.PHONY: firmware-clean
firmware-clean:
	rm -vrf $(addprefix $(FIRMWARE)/firmware., elf bin hex map) \
		$(FIRMWARE_OBJS) $(FIRMWARE_TEST_OBJS) $(COMPLIANCE_TEST_OBJS)

.PHONY: firmware-unit-test-clean
firmware-unit-test-clean:
	rm -vrf $(addprefix $(FIRMWARE)/firmware_unit_test., elf bin hex map) \
		$(FIRMWARE_OBJS) $(FIRMWARE_UNIT_TEST_OBJS)

#endend


