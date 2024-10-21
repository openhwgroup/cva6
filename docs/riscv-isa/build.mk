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

current_dir = $(shell pwd)

# Path of current file, intended to be included by a configuration subfolder
riscv-isa_dir := $(dir $(lastword $(MAKEFILE_LIST)))

all: priv-pdf priv-html unpriv-pdf unpriv-html

setup:
	mkdir -p build/riscv-isa-manual

	cp -r $(riscv-isa_dir)/riscv-isa-manual/* build/riscv-isa-manual
	cp -r $(riscv-isa_dir)/src build/riscv-isa-manual
	cp $(riscv-isa_dir)/../common/*.adoc build/riscv-isa-manual/src

	cd ../.. && python3 scripts/spec_builder.py --target $(CONFIG) --gen-config $(current_dir)/build/riscv-isa-manual/src/config.adoc

priv-pdf: setup
	cd build/riscv-isa-manual; make SKIP_DOCKER=true build/riscv-privileged.pdf
	cp ./build/riscv-isa-manual/build/riscv-privileged.pdf priv-isa-$(CONFIG).pdf

priv-html: setup
	cd build/riscv-isa-manual; make SKIP_DOCKER=true build/riscv-privileged.html
	cp ./build/riscv-isa-manual/build/riscv-privileged.html priv-isa-$(CONFIG).html

unpriv-pdf: setup
	cd build/riscv-isa-manual; make SKIP_DOCKER=true build/riscv-unprivileged.pdf
	cp ./build/riscv-isa-manual/build/riscv-unprivileged.pdf unpriv-isa-$(CONFIG).pdf

unpriv-html: setup
	cd build/riscv-isa-manual; make SKIP_DOCKER=true build/riscv-unprivileged.html
	cp ./build/riscv-isa-manual/build/riscv-unprivileged.html unpriv-isa-$(CONFIG).html

clean:
	rm -rf build
