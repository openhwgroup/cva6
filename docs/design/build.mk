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
design_dir := $(dir $(lastword $(MAKEFILE_LIST)))

all: design-pdf design-html

setup:
	mkdir -p build

	cp -r $(design_dir)/design-manual/* build
	cp -r $(design_dir)/../riscv-isa/riscv-isa-manual/docs-resources build
	cp $(design_dir)/../common/*.adoc build/source

	cp -rf source/* build/source

	cd ../../../config/gen_from_riscv_config && python3 scripts/riscv_config_gen.py -s ../riscv-config/$(CONFIG)/generated/isa_gen.yaml -i templates/isa_template.yaml -m updaters/$(CONFIG)/isa_updater.yaml -t $(CONFIG) -f adoc
	cd ../../../config/gen_from_riscv_config && python3 scripts/riscv_config_gen.py -s ../riscv-config/$(CONFIG)/generated/isa_gen.yaml -c ../riscv-config/$(CONFIG)/generated/custom_gen.yaml -m updaters/$(CONFIG)/csr_updater.yaml -t $(CONFIG) -f adoc
	cp -r $(design_dir)/../../config/gen_from_riscv_config/$(CONFIG)/* build/source

	cd ../.. && python3 scripts/spec_builder.py --target $(CONFIG) --gen-config $(current_dir)/build/source/config.adoc --gen-parameters $(current_dir)/build/source/parameters.adoc --gen-ports $(current_dir)/build/source

design-pdf: setup
	cd build; make SKIP_DOCKER=true build/design.pdf
	cp ./build/build/design.pdf design-$(CONFIG).pdf

design-html: setup
	cd build; make SKIP_DOCKER=true build/design.html
	cp ./build/build/design.html design-$(CONFIG).html

clean:
	rm -rf build
