# Copyright 2024 Thales DIS France SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Zbigniew CHAMSKI - Thales

FIGDIR=figures
WAVEDIR=wavedrom

# Names of figure files, without directory prefix nor .svg suffix
FIGURES=interrupt-ack-uvm

SVG_FILES=$(patsubst %,$(FIGDIR)/%.svg,$(FIGURES))
WAVE_FILES=$(patsubst %,$(WAVEDIR)/%.wave,$(FIGURES))

all: $(SVG_FILES)

# wavedrom-cli requires a local installation and needs nodejs version >= 14.
# See https://github.com/wavedrom/cli.
$(FIGDIR)/%.svg: $(WAVEDIR)/%.wave
	wavedrom-cli -i $^ -s $@

clean:
	$(RM) $(SVG_FILES)

