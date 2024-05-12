#   Copyright 2024 Thales DIS France SAS
#   Licensed under the Solderpad Hardware License, Version 2.1 (the "License");
#   you may not use this file except in compliance with the License.
#   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
#   You may obtain a copy of the License at https://solderpad.org/licenses/
#
#   Original Author: Jean-Roch COULON - Thales

all: priv unpriv priv-html

setup:
	mkdir -p build/riscv-isa-manual
	cp -r riscv-isa-manual/* build/riscv-isa-manual
	cp -r src build/riscv-isa-manual

priv: setup
	cd build/riscv-isa-manual/build; make priv
	cp ./build/riscv-isa-manual/build/priv-isa-asciidoc.pdf priv-isa-cv32a65x.pdf

priv-html: setup
	cd build/riscv-isa-manual/build; make priv-html
	cp ./build/riscv-isa-manual/build/priv-isa-asciidoc.html priv-isa-cv32a65x.html

unpriv: setup
	cd build/riscv-isa-manual/build; make unpriv

clean:
	rm -rf build
