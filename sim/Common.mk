###############################################################################
#
# Copyright 2021 OpenHW Group
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
# Common code for CVA6 simulation Makefiles.  Intended to be included by the
# Makefiles in the "core" and "uvm" dirs.
#
###############################################################################
# Common functions

# Map multiple flag values to "YES" or NO
# Use like this, to test variable MYVAR
# ifeq ($(call IS_YES($(MYVAR)),YES)
YES_VALS=Y YES 1 y yes TRUE true
IS_YES=$(if $(filter $(YES_VALS),$(1)),YES,NO)
NO_VALS=N NO 0 n no FALSE false
IS_NO=$(if $(filter $(NO_VALS),$(1)),NO,YES)

###############################################################################
# Common variables
BANNER=*******************************************************************************************

###############################################################################
# Variables to determine the the command to clone external repositories.
# For each repo there are a set of variables:
#      *_REPO:   URL to the repository in GitHub.
#      *_BRANCH: Name of the branch you wish to clone;
#                Set to 'master' to pull the master branch.
#      *_HASH:   Value of the specific hash you wish to clone;
#                Set to 'head' to pull the head of the branch you want.
# The CVA6 repo also has a variable to clone a specific tag:
#      *_TAG:    Value of the specific tag you wish to clone;
#                Will override the HASH unless set to "none".
#                

export SHELL = /bin/bash

CVA6_REPO   ?= https://github.com/openhwgroup/cva6
CVA6_BRANCH ?= master
CVA6_HASH   ?= head
CVA6_TAG    ?= none

RISCVDV_REPO    ?= https://github.com/google/riscv-dv
RISCVDV_BRANCH  ?= master
RISCVDV_HASH    ?= 10fd4fa8b7d0808732ecf656c213866cae37045a

COMPLIANCE_REPO   ?= https://github.com/riscv/riscv-compliance
COMPLIANCE_BRANCH ?= master
COMPLIANCE_HASH   ?= c21a2e86afa3f7d4292a2dd26b759f3f29cde497

# Generate command to clone the CVA6 RTL.

ifeq ($(CVA6_BRANCH), master)
  TMP = git clone --recursive $(CVA6_REPO) $(CVA6_PKG)
else
  TMP = git clone --recursive -b $(CVA6_BRANCH) --single-branch $(CVA6_REPO) $(CVA6_PKG)
endif

# If a TAG is specified, the HASH is not considered
ifeq ($(CVA6_TAG), none)
  ifeq ($(CVA6_HASH), head)
    CLONE_CVA6_CMD = $(TMP)
  else
    CLONE_CVA6_CMD = $(TMP); cd $(CVA6_PKG); git checkout $(CVA6_HASH)
  endif
else
  CLONE_CVA6_CMD = $(TMP); cd $(CVA6_PKG); git checkout tags/$(CVA6_TAG)
endif

# RTL repo vars end

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

# Generate command to clone the RISCV Compliance Test-suite
ifeq ($(COMPLIANCE_BRANCH), master)
  TMP4 = git clone $(COMPLIANCE_REPO) --recurse $(COMPLIANCE_PKG)
else
  TMP4 = git clone -b $(COMPLIANCE_BRANCH) --single-branch $(COMPLIANCE_REPO) --recurse $(COMPLIANCE_PKG)
endif

ifeq ($(COMPLIANCE_HASH), head)
  CLONE_COMPLIANCE_CMD = $(TMP4)
else
  CLONE_COMPLIANCE_CMD = $(TMP4); cd $(COMPLIANCE_PKG); git checkout $(COMPLIANCE_HASH)
endif
# RISCV Compliance repo var end

###############################################################################
# The sanity rule runs whatever is currently deemed to be the minimal test that
# must be able to run (and pass!) prior to generating a pull-request.
sanity: hello-world

###############################################################################
# Rule to generate hex (loadable by simulators) from elf
# Relocate debugger to last 16KB of mm_ram
#    $@ is the file being generated.
#    $< is first prerequiste.
#    $^ is all prerequistes.
#    $* is file_name (w/o extension) of target
%.hex: %.elf
	$(RISCV_EXE_PREFIX)objcopy -O verilog $< $@ \
		--change-section-address  .debugger=0x3FC000 \
		--change-section-address  .debugger_exception=0x3FC800
	$(RISCV_EXE_PREFIX)readelf -a $< > $*.readelf
	$(RISCV_EXE_PREFIX)objdump -D -S $*.elf > $*.objdump

bsp:
	make -C $(BSP) RISCV=$(RISCV) RISCV_PREFIX=$(RISCV_PREFIX) RISCV_EXE_PREFIX=$(RISCV_EXE_PREFIX)

vars-bsp:
	make vars -C $(BSP) RISCV=$(RISCV) RISCV_PREFIX=$(RISCV_PREFIX) RISCV_EXE_PREFIX=$(RISCV_EXE_PREFIX)

clean-bsp:
	make clean -C $(BSP)

#endend
