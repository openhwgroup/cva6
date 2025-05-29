# SPDX-License-Identifier: Apache-2.0

VERILATOR ?= verilator

all: ecc_encode ecc_decode

ecc_%: test/ecc/ecc_%.cpp test/ecc/ecc.cpp src/ecc_pkg.sv src/ecc_%.sv
	$(VERILATOR) --cc $^ --top-module $@ --trace --exe
	cd obj_dir && make -f V$@.mk > /dev/zero
