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
design_dir := $(dir $(lastword $(MAKEFILE_LIST)))

all: design-pdf design-html

setup:
	mkdir -p build
	pwd 
	echo $(design_dir)
	cp -r $(design_dir)/design-manual/* build
	cp -r $(design_dir)/../../config/gen_from_riscv_config/$(CONFIG)/* build/source
	cp -r $(design_dir)/../riscv-isa/riscv-isa-manual/docs-resources build
	cp ../config/config.adoc build/source
	cp $(design_dir)/../common/*.adoc build/source
	cp -rf source build

design-pdf: setup
	cd build; make SKIP_DOCKER=true build/design.pdf
	cp ./build/build/design.pdf design-$(CONFIG).pdf

design-html: setup
	cd build; make SKIP_DOCKER=true build/design.html
	cp ./build/build/design.html design-$(CONFIG).html

clean:
	rm -rf build
