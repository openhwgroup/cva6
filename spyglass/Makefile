# Copyright 2024 Thales DIS France SAS
# Licensed under the Solderpad Hardware Licence, Version 2.1 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Makefile for Spyglass lint
#
# Original Author: Asmaa Kassimi (asmaa.kassimi@external.thalesgroup.com) - Thales
#

## Define variables

# Top design
TOP= cva6

# root path
mkfile_path := $(abspath $(lastword $(MAKEFILE_LIST)))
root-dir := $(dir $(mkfile_path))

# Relevent synthesis and simulation scripts/Makefiles must set the shell
# ENV variable CVA6_REPO_DIR.

ifndef CVA6_REPO_DIR
$(warning must set CVA6_REPO_DIR to point at the root of CVA6 sources -- doing it for you...)
export CVA6_REPO_DIR=$(abspath $(root-dir)../)
endif

ifndef DV_TARGET
$(error must set DV_TARGET to indicate CVA6 target to use)
endif

HPDCACHE_DIR=${CVA6_REPO_DIR}/core/cache_subsystem/hpdcache/

HPDCACHE_TARGET_CFG=${CVA6_REPO_DIR}/core/include/cva6_hpdcache_default_config_pkg.sv

FLIST_CVA6=${CVA6_REPO_DIR}/core/Flist.cva6

# Export List
EXPORT_LIST= CVA6_REPO_DIR=$(CVA6_REPO_DIR) TARGET_CFG=$(DV_TARGET) HPDCACHE_TARGET_CFG=$(HPDCACHE_TARGET_CFG) HPDCACHE_DIR=$(HPDCACHE_DIR)

# Use Spyglass design_read and lint_check commands, other commands could be added to check cdc, sdc and dft

design_read: run_checkvar
	@echo "Building for $(DV_TARGET)"
	@export ${EXPORT_LIST}; aipk_read -top=$(TOP) -srcfile=$(FLIST_CVA6)

lint_check: run_checkvar
	@export ${EXPORT_LIST}; aipk_run -top=$(TOP) -goals=lint_rtl

gui: run_checkvar
	aipk_run -top=$(TOP) -gui&

show_goals:
	aipk_run -showgoals -top=$(TOP) | tee showgoals.log

open_docs:
	firefox ${SPYGLASS_HOME}/htmlhelp/index.html

all: run_checkvar
	make design_read
	make lint_check
	make gui

# clean logs

clean:
	@\rm -rf *.log

run_checkvar:
ifeq (,$(TOP))
	@echo "Variable TOP is undefined...EXITING THE RUN"
	@exit 2
endif
ifeq (,$(CVA6_REPO_DIR))
	@echo "Variable CVA6_REPO_DIR is undefined...EXITING THE RUN"
	@exit 2
endif
ifeq (,$(HPDCACHE_DIR))
	@echo "Variable HPDCACHE_DIR is undefined..."
endif
ifeq (,$(HPDCACHE_TARGET_CFG))
	@echo "Variable HPDCACHE_TARGET_CFG is undefined..."
endif
ifeq (,$(TARGET_CFG))
	@echo "Variable TARGET_CFG is undefined..."
endif
ifeq (,$(FLIST_CVA6))
	@echo "Variable FLIST_CVA6 is undefined..."
endif



