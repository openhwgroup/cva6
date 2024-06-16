#   Copyright 2024 Thales DIS France SAS
#   Licensed under the Solderpad Hardware License, Version 2.1 (the "License");
#   you may not use this file except in compliance with the License.
#   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
#   You may obtain a copy of the License at https://solderpad.org/licenses/
#
#   Original Author: Jean-Roch COULON - Thales

ifeq ($(CONFIG),)
$(error CONFIG must be defined)
endif

# Path of current file, intended to be included by a configuration subfolder
riscv-isa_dir := $(dir $(lastword $(MAKEFILE_LIST)))

all: priv-pdf priv-html unpriv-pdf unpriv-html

setup:
	mkdir -p build/riscv-isa-manual
	cp -r $(riscv-isa_dir)/riscv-isa-manual/* build/riscv-isa-manual
	cp -r $(riscv-isa_dir)/src build/riscv-isa-manual
	cp -r src build/riscv-isa-manual

priv-pdf: setup
	cd build/riscv-isa-manual/build; make priv-pdf
	cp ./build/riscv-isa-manual/build/riscv-privileged.pdf priv-isa-$(CONFIG).pdf

priv-html: setup
	cd build/riscv-isa-manual/build; make priv-html
	cp ./build/riscv-isa-manual/build/riscv-privileged.html priv-isa-$(CONFIG).html

unpriv-pdf: setup
	cd build/riscv-isa-manual/build; make unpriv-pdf
	cp ./build/riscv-isa-manual/build/riscv-unprivileged.pdf unpriv-isa-$(CONFIG).pdf

unpriv-html: setup
	cd build/riscv-isa-manual/build; make unpriv-html
	cp ./build/riscv-isa-manual/build/riscv-unprivileged.html unpriv-isa-$(CONFIG).html

clean:
	rm -rf build
