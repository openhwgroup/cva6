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
	mkdir -p build/design-manual
	pwd 
	echo $(design_dir)
	cp -r $(design_dir)/design-manual/* build/design-manual
	cp -r $(design_dir)/../../config/gen_from_riscv_config/$(CONFIG)/* build/design-manual/source
	cp -r $(design_dir)/../riscv-isa/riscv-isa-manual/docs-resources build/design-manual
#cp -r src build/design-manual

design-pdf: setup
	cd build/design-manual; make SKIP_DOCKER=true build/design.pdf
	cp ./build/design-manual/build/design.pdf design-$(CONFIG).pdf

design-html: setup
	cd build/design-manual; make SKIP_DOCKER=true build/design.html
	cp ./build/design-manual/build/design.html design-$(CONFIG).html

clean:
	rm -rf build
