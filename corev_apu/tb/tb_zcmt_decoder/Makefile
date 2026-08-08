# Copyright 2026 Keerthivasan
#
# Licensed under the Solderpad Hardware Licence, Version 2.0.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0

ROOT := $(abspath ../../..)

VERILATOR ?= verilator
TOP       := tb_zcmt_decoder
OBJ_DIR   := obj_dir

SOURCES := \
	$(ROOT)/core/include/config_pkg.sv \
	$(ROOT)/core/include/cv32a60x_config_pkg.sv \
	$(ROOT)/core/include/riscv_pkg.sv \
	$(ROOT)/core/zcmt_decoder.sv \
	$(CURDIR)/hdl/tb.sv

.PHONY: all build test clean

all: test

build:
	$(VERILATOR) \
		--binary \
		--timing \
		--top-module $(TOP) \
		-Wno-fatal \
		-Wno-WIDTHTRUNC \
		--Mdir $(OBJ_DIR) \
		$(SOURCES)

test: build
	./$(OBJ_DIR)/V$(TOP)

clean:
	rm -rf $(OBJ_DIR)
