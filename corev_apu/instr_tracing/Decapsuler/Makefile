# Copyright 2025 Thales DIS design services SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Author: Maxime Colson - Thales

# Makefile to build the Decapsuler executable

CC = $(GCC_11_5_PATH)/g++
TARGETS = Decapsuler
CFLAGS = -Wall -Wextra -g

all: $(TARGETS)

Decapsuler: Decapsuler.cpp
	$(CC) --version
	$(CC) -o Decapsuler Decapsuler.cpp $(CFLAGS)

.PHONY: clean

clean:
	rm -f $(TARGETS)

clean_all:
	rm -f $(TARGETS)
	rm -rf receiver_data
