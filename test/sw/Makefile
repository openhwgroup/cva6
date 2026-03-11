# Copyright 2026 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Enrico Zelioli <ezelioli@iis.ee.ethz.ch>

SW_DIR     := $(realpath .)
LD_DIR     := $(SW_DIR)/link
LIB_DIR    := $(SW_DIR)/lib
SRC_DIR    := $(SW_DIR)/tests
INC_DIR    := $(SW_DIR)/include
OUT_DIR    := $(SW_DIR)/out
DEPS_DIR   := $(SW_DIR)/deps

ifndef RV_BINROOT
RV_BINROOT := $(dir $(shell which riscv64-unknown-elf-gcc 2>/dev/null))
endif
RV_AR      := $(RV_BINROOT)/riscv64-unknown-elf-ar
RV_CC      := $(RV_BINROOT)/riscv64-unknown-elf-gcc
RV_OBJCOPY := $(RV_BINROOT)/riscv64-unknown-elf-objcopy
RV_OBJDUMP := $(RV_BINROOT)/riscv64-unknown-elf-objdump

SW_FLAGS   := -DOT_PLATFORM_RV32 -march=rv64gc_zifencei_zicbom -mabi=lp64d -mstrict-align -O2 -Wall -Wextra -static -ffunction-sections -ffreestanding -fdata-sections -frandom-seed=cheshire -fuse-linker-plugin -flto -Wl,-flto
SW_CCFLAGS := $(SW_FLAGS) -ggdb -mcmodel=medany -mexplicit-relocs -fno-builtin -fverbose-asm -pipe
SW_LDFLAGS := $(SW_FLAGS) -nostartfiles -Wl,--gc-sections -Wl,-L$(LD_DIR)

LIB_SRCS_S  = $(shell find $(LIB_DIR) -name "*.S")
LIB_SRCS_C  = $(shell find $(LIB_DIR) -name "*.c")
LIB_SRCS_O  = $(patsubst $(LIB_DIR)/%,$(OUT_DIR)/lib/%,$(LIB_SRCS_S:.S=.o) $(LIB_SRCS_C:.c=.o))

DEPS_INC    := $(DEPS_DIR)/printf
DEPS_SRCS_C := $(DEPS_DIR)/printf/printf.c
DEPS_SRCS_O := $(patsubst $(DEPS_DIR)/%,$(OUT_DIR)/deps/%,$(DEPS_SRCS_C:.c=.o))

TEST_SRCS_C := $(shell find $(SRC_DIR) -name "*.c")
TEST_SRCS_S := $(shell find $(SRC_DIR) -name "*.S")
TEST_SRCS_O := $(patsubst $(SRC_DIR)/%,$(OUT_DIR)/tests/%,$(TEST_SRCS_C:.c=.o) $(TEST_SRCS_S:.S=.o))
TEST_ELFS   := $(patsubst $(SRC_DIR)/%,$(OUT_DIR)/%,$(TEST_SRCS_C:.c=.elf) $(TEST_SRCS_S:.S=.elf))
TEST_DUMPS  := $(TEST_ELFS:.elf=.dump)
TEST_HEXES  := $(TEST_ELFS:.elf=.hex)

.PRECIOUS: $(OUT_DIR)/%.elf $(OUT_DIR)/tests/%.o

.PHONY: default
default: all

$(DEPS_DIR)/printf:
	git clone -b v4.0.0 https://github.com/mpaland/printf.git $(DEPS_DIR)/printf

RISCV_TESTS_REV := 87b04f07a51f57b134a935c6157222bbd35905d9

$(DEPS_DIR)/riscv-tests/: $(DEPS_DIR)/patches/riscv-tests.patch $(DEPS_DIR)/patches/riscv-tests-env.patch
	git clone https://github.com/riscv-software-src/riscv-tests.git $(DEPS_DIR)/riscv-tests
	cd $(DEPS_DIR)/riscv-tests && git checkout $(RISCV_TESTS_REV)
	cd $(DEPS_DIR)/riscv-tests && git submodule update --init --recursive
	cd $(DEPS_DIR)/riscv-tests && git apply $(DEPS_DIR)/patches/riscv-tests.patch
	cd $(DEPS_DIR)/riscv-tests && git apply $(DEPS_DIR)/patches/riscv-tests-fencet.patch
	cd $(DEPS_DIR)/riscv-tests/env && git apply $(DEPS_DIR)/patches/riscv-tests-env.patch

.PHONY: riscv-tests
riscv-tests: | $(DEPS_DIR)/riscv-tests/
	@mkdir -p $(DEPS_DIR)/riscv-tests/build
	cd $(DEPS_DIR)/riscv-tests/build && ../configure && make isa

.PHONY: deps
deps: $(DEPS_DIR)/printf

.PHONY: lib
lib: $(OUT_DIR)/libcva6.a

.PHONY: all
all: $(DEPS_DIR)/printf $(TEST_DUMPS) $(TEST_HEXES)

.PHONY: clean
clean:
	rm -rf $(OUT_DIR)

$(OUT_DIR)/deps/%.o: $(DEPS_DIR)/%.c
	@mkdir -p $(dir $@)
	$(RV_CC) $(SW_CCFLAGS) -I$(DEPS_INC) -c $< -o $@

$(OUT_DIR)/lib/%.o: $(LIB_DIR)/%.c
	@mkdir -p $(dir $@)
	$(RV_CC) $(SW_CCFLAGS) -I$(INC_DIR) -I$(DEPS_INC) -c $< -o $@

$(OUT_DIR)/lib/%.o: $(LIB_DIR)/%.S
	@mkdir -p $(dir $@)
	$(RV_CC) $(SW_CCFLAGS) -I$(INC_DIR) -I$(DEPS_INC) -c $< -o $@

$(OUT_DIR)/libcva6.a: $(LIB_SRCS_O) $(DEPS_SRCS_O)
	$(RV_AR) rcs $@ $^

$(OUT_DIR)/tests/%.o: $(SRC_DIR)/%.c
	@mkdir -p $(dir $@)
	$(RV_CC) $(SW_CCFLAGS) -I$(INC_DIR) -I$(DEPS_INC) -c $< -o $@

$(OUT_DIR)/tests/%.o: $(SRC_DIR)/%.S
	@mkdir -p $(dir $@)
	$(RV_CC) $(SW_CCFLAGS) -I$(INC_DIR) -I$(DEPS_INC) -c $< -o $@

$(OUT_DIR)/%.elf: $(OUT_DIR)/tests/%.o $(OUT_DIR)/libcva6.a
	$(RV_CC) $(SW_LDFLAGS) -T$(LD_DIR)/link.ld -o $@ $< $(OUT_DIR)/libcva6.a

$(OUT_DIR)/%.dump: $(OUT_DIR)/%.elf
	$(RV_OBJDUMP) -d $< > $@

$(OUT_DIR)/%.hex: $(OUT_DIR)/%.elf
	$(RV_OBJCOPY) -O verilog $< $@
