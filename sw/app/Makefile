# Copyright (c) 2020 Thales.
# 
# Copyright and related rights are licensed under the Apache
# License, Version 2.0 (the "License"); you may not use this file except in
# compliance with the License.  You may obtain a copy of the License at
# https://www.apache.org/licenses/LICENSE-2.0. Unless required by applicable law
# or agreed to in writing, software, hardware and materials distributed under
# this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
# CONDITIONS OF ANY KIND, either express or implied. See the License for the
# specific language governing permissions and limitations under the License.
#
# Author:         Sebastien Jacq - sjthales on github.com
#                 Kevin Eyssartier - EyssartK on github.com
#
# Additional contributions by:
#
#
# script Name:    Software application makefile
# Project Name:   CVA6 softcore
# Language:       Makefile
#
# Description:    Makefile to compile software application for CVA6 platform
#
# =========================================================================== #
# Revisions  :
# Date        Version  Author       Description
# 2020-10-06  0.1      S.Jacq       Created
# 2020-10-06  0.1      k.Eyssartier Created
# =========================================================================== #

XLEN ?= 32

default: all

utils_dir= ../utils
src_dir = $(abspath .)
bsp_dir = ../bsp


#--------------------------------------------------------------------
# Sources
#--------------------------------------------------------------------

bmarks = \
	coremark \
	helloworld \
	helloworld_printf \
	median \
	qsort \
	rsort \
	towers \
	vvadd \
	multiply \
	dhrystone \
	spmv \
	pmp \
	mnist

#--------------------------------------------------------------------
# Build rules
#--------------------------------------------------------------------

RISCV_PREFIX ?= riscv-none-elf-
RISCV_GCC ?= $(RISCV_PREFIX)gcc
RISCV_OBJCOPY ?= $(RISCV_PREFIX)objcopy
RISCV_AR ?= $(RISCV_PREFIX)ar
RISCV_OBJDUMP ?= $(RISCV_PREFIX)objdump


SRC_BSP_C=$(wildcard $(bsp_dir)/hal/*.c) $(wildcard $(bsp_dir)/drivers/uart/*.c) 
SRC_BSP_S=$(wildcard $(bsp_dir)/hal/*.S)


OBJ_BSP_C=$(SRC_BSP_C:.c=.o)
OBJ_BSP_S=$(SRC_BSP_S:.S=.o)
OBJ_BSP= $(OBJ_BSP_S) $(OBJ_BSP_C)


OBJ_APP=$(wildcard $(src_dir)/*.o) 

INCS += -I$(src_dir)/../bsp/config \
	-I$(src_dir)/../bsp/drivers/uart \
	-I$(src_dir)/../bsp/hal \
	-I$(src_dir)/coremark/simple \
	-I$(src_dir)/common \
	$(addprefix -I$(src_dir)/, $(bmarks))
	
FLAGS_STR:="$(RISCV_CFLAGS)  $(RISCV_LDFLAGS) "


CFLAGS  ?=	-march=rv32im_zicsr \
		-mabi=ilp32 \
		-DPREALLOCATE=1 \
		-fvisibility=hidden \
		-DSTDIO_THRU_UART \
		-O3 \
		-mcmodel=medany \
		-fno-tree-loop-distribute-patterns\
		-funroll-all-loops \
		-falign-jumps=4 \
		-falign-functions=16 \
		-static \
		-Wall \
		-pedantic 

RISCV_CFLAGS :=-DPERFORMANCE_RUN=1 \
		-DITERATIONS=3 \
		-DFLAGS_STR=\"$(FLAGS_STR)\" \
		-march=rv32im_zicsr \
		-mabi=ilp32 \
		-DPREALLOCATE=1 \
		-fvisibility=hidden \
		-DSTDIO_THRU_UART \
		-O3 \
		-mcmodel=medany \
		-fno-tree-loop-distribute-patterns\
		-funroll-all-loops \
		-falign-jumps=4 \
		-falign-functions=16 \
		-static \
		-Wall \
		-pedantic 


RISCV_LDFLAGS=-L./ -lcva6 -static -nostartfiles -T $(src_dir)/../bsp/config/link.ld



incs  += -I$(src_dir)/../env -I$(src_dir)/common $(addprefix -I$(src_dir)/, $(bmarks))
objs  :=


define generate_rules =
$(1)_SRC_DIR = ./$(1)/
$(1)_SRC_FILES = $$(shell find $$($(1)_SRC_DIR) -name "*.c")
$(1)_OBJ_FILES = $$($(1)_SRC_FILES:.c=.o)
ALL_OBJ += $$($(1)_OBJ_FILES)
$(1): $(1).D $(1).riscv
$(1): $(1).hex $(1).riscv
$(1): $(1).bin $(1).riscv
$(1): $(1).mem $(1).bin
$(1): $(1).coe $(1).mem
$(1).riscv: libcva6.a $$($(1)_OBJ_FILES)
	# LINKING
	$$(RISCV_GCC) $$(RISCV_CFLAGS) -o $$@ $$^ $$(RISCV_LDFLAGS)
endef

$(foreach bmark,$(bmarks),$(eval $(call generate_rules,$(bmark))))

%.D: %.riscv 
	$(RISCV_OBJDUMP) -D $< > $@

%.hex: %.riscv
	$(RISCV_OBJCOPY) -O ihex $< $@

%.bin: %.riscv
	$(RISCV_OBJCOPY) -O binary $< $@

libcva6.a: $(OBJ_BSP)
	$(RISCV_AR) rcs libcva6.a $(OBJ_BSP)

%.o: %.c
	$(RISCV_GCC) $(INCS) -o $@ -c $< $(RISCV_CFLAGS)

%.o: %.S
	$(RISCV_GCC) -o $@ -c $< $(CFLAGS)

%.mem: %.bin
	$(utils_dir)/bin2mem.py $(src_dir)/$<

%.coe: %.mem
	$(utils_dir)/mem2coe.py $(src_dir)/$<


all: $(bmarks)


clean:
	rm -rf $(OBJ_BSP) $(ALL_OBJ) libcva6.a *.riscv *.o *.D *.mem *.bin *.coe *.hex


