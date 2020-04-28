#
# Copyright (c) 2005-2020 Imperas Software Ltd., www.imperas.com
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#   http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND,
# either express or implied.
#
# See the License for the specific language governing permissions and
# limitations under the License.
#
#
ifndef IMPERAS_HOME
    IMPERAS_ERROR := $(error "Error: IMPERAS_HOME not defined, please setup Imperas/OVP environment")
endif
IMPERAS_HOME := $(shell getpath.exe "$(IMPERAS_HOME)")

# defines the list of available targets
include ../Setup_and_Checks/defines.TARGETS.include

# Run time arguments
PLUSARGS ?=
# System Verilog Compile time arguments
PLUSDEFS ?=

SV_FILES = $(wildcard verilog_OVPmodel/*.sv) $(wildcard verilog_model/*.sv) $(wildcard verilog_testbench/*.sv)
SV_DEFS   = $(PLUSDEFS)
SV_DEFS  += +incdir+verilog_OVPmodel
ifneq ($(COVERAGE),)
# Coverage enabled
#   include coverage class
SV_DEFS  += +incdir+verilog_testbench
#   define COVERAGE to build in coverage code
SV_DEFS  += +define+COVERAGE
endif

#V?=@
V=
ifeq ($(VERBOSE),1)
    V=
endif

# default make target
all: help

help:
	@echo 'Usage:'
	@echo '  Current Settings'
ifeq ($(TARGET),)
	@echo '    TARGET    : Must be set in shell. Valid TARGET settings $(SUPPORTED_TARGETS)'
else
	@echo '    TARGET    : $(TARGET)'
endif
	@echo '    TESTBENCH : $(TESTBENCH)'
	@echo ''
	@echo '    SV_LIB    : $(SV_LIB)'
	@echo '    VCOMPILE  : $(VCOMPILE)'
	@echo '    VELAB     : $(VELAB)'
	@echo '    VCFLAGS   : $(VCFLAGS)'
	@echo '    VRUN      : $(VRUN)'
ifeq ($(COVERAGE),)
	@echo ''
	@echo '    set COVERAGE=1 to add settings to enable coverage analysis'
else
	@echo '    VCOVERAGE : $(VCOVERAGE)'
endif
	@echo ''
	@echo 'Example:'
	@echo ' See provided scripts for examples of how to execute'
	@echo ' Typical build flow with make targets would be:'
	@echo '     make TESTBENCH=tb_single TARGET=$(TARGET) compileVerilog  <PLUSDEFS> '
	@echo '     make                     TARGET=$(TARGET) compileOVPmodel'
	@echo '     make TESTBENCH=tb_single TARGET=$(TARGET) run             <PLUSARGS>'
	@echo '  PLUSARGS can include'
	@echo '       +elf_file=<application elf to execute>'
	@echo '       +nm_file=<application symbol table>'
	@echo '       +stdout_file=<stub for file to record stdout>'
	@echo '       +sig_file=<stub for file to save signature>'
	@echo '       +ovpcfg="<Imperas/OVP simulator command line arguments>"'
	@echo '       +disass'
	@echo '  PLUSDEFS can include'
	@echo '       +define+DEBUG                  : Turn on debug messages in System Verilog'
	@echo '       +define+T0_TYPE=\\\"RV32IM\\\" : Define the processor variant for instance T0'
	@echo '       +define+T1_TYPE=\\\"RV32IM\\\" : Define the processor variant for instance T1'
	@echo ''

ifeq ($(TARGET),)

    IMPERAS_WARNING := $(warning Warning: TARGET not defined, set environment variable TARGET to one of $(SUPPORTED_TARGETS))

else

#
# include the valid setup Makefiles for all TARGETs in SUPPORTED_TARGETS list
#
define Target_Include_Template
    ifeq ($(TARGET),$(1))
        include ../Setup_and_Checks/defines.$(1).Makefile.include
    endif
endef
$(foreach TGT, $(SUPPORTED_TARGETS), $(eval $(call Target_Include_Template,$(TGT))))

ifneq ($(VALIDTARGET),1)
    IMPERAS_ERROR := $(error Error: TARGET="$(TARGET)" unsupported, set environment variable TARGET to one of $(SUPPORTED_TARGETS))
endif


ifeq ($(VCOMPILE),)
compileOVPmodel compileVerilog:
	@echo "# Not Currently available ($@)"
else

compileOVPmodel:
	@echo "#"
	@echo "# Compiling OVP Processor Instantiation"
	@echo "#"
	$(V) $(MAKE) -C C_OVPmodel SRC=riscv_sv.c OTHER_CFLAGS="$(VCFLAGS)" 

compileVerilog:
	@echo "#"
	@echo "# Compiling SystemVerilog $(TESTBENCH)"
	@echo "#"
	$(V) $(VCOMPILE)
ifneq ($(VELAB),)
	$(V) $(VELAB)
endif
endif

ifeq ($(VRUN),)
run:
	@echo "# Not Currently available ($@)"
else
run:
	@echo "#"
	@echo "# Simulating System Verilog Testbench $(TESTBENCH)"
	@echo "#"
	$(V) $(VRUN) $(PLUSARGS)
endif

ifeq ($(COVERAGE),)
coverage:
	@echo "# Warning Coverage not currently enabled. Set COVERAGE=1 to enable."
else
ifeq ($(VCOVERAGE),)
coverage:
	@echo "# Warning Coverage not currently enabled for TARGET=$(TARGET)."
else
coverage:
	$(V) $(VCOVERAGE)
endif
endif

endif

clean::
	$(V) - $(MAKE) -C application clean
	$(V) - $(MAKE) -C C_OVPmodel  clean
ifneq ($(SV_LIB),)
	$(V) - rm -rf $(SV_LIB)
endif

realclean:: clean
	$(V) - rm -f  *.log
	$(V) - rm -f  *.err
	$(V) - rm -f  *.vcd
	$(V) - rm -rf out
