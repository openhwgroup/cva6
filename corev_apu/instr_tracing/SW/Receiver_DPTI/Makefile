# Copyright 2025 Thales DIS design services SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Author: Maxime Colson - Thales

# Makefile to build the receiver executable
# You need to properly install Digilent Adept and correctly link adept sdk lib
CC = g++
INC ?= $(HOME)/runtime_adept/digilent.adept.sdk_2.4.2
LIBDIR = /usr/lib64/digilent/adept
TARGETS = Receiver_DPTI
CFLAGS = -I $(INC) -L $(LIBDIR) -ldpti -ldmgr -Wall -Wextra -g

all: $(TARGETS)

Receiver_DPTI: Receiver_DPTI.cpp
	$(CC) -o Receiver_DPTI Receiver_DPTI.cpp $(CFLAGS)

.PHONY: clean

clean:
	rm -f $(TARGETS)

clean_all:
	rm -f $(TARGETS)
	rm -rf receiver_data
