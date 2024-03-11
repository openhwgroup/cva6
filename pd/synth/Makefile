# Copyright 2021 Thales DIS design services SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Jean-Roch COULON - Thales
#

DESIGN_NAME           = cva6
PERIOD               ?= 17
FOUNDRY_PATH         ?=
TECH_NAME            ?=
TARGET_LIBRARY_FILES  = $(TECH_NAME).db
INPUT_DELAY          ?= 0.46
OUTPUT_DELAY         ?= 0.11
DC_SHELL_PATH        ?= /opt/synopsys/syn/Q-2019.12/bin/
NAND2_AREA           ?= 1120
TARGET               ?= cv64a6_imafdc_sv39

EXPORT_LIST=SNPSLMD_QUEUE=TRUE TECH_NAME=$(TECH_NAME) DESIGN_NAME=$(DESIGN_NAME) TARGET=$(TARGET) TERM=vt100 PERIOD=$(PERIOD) FOUNDRY_PATH=$(FOUNDRY_PATH) TARGET_LIBRARY_FILES=$(TARGET_LIBRARY_FILES) INPUT_DELAY=$(INPUT_DELAY) OUTPUT_DELAY=$(OUTPUT_DELAY)

ifndef FOUNDRY_PATH
  $(error "Please provide FOUNDRY techno")
endif
ifndef TECH_NAME
  $(error "Please provide TECH_NAME techno")
endif
# Create Flist with good compilation order for synthesis
#	- config_pkg.sv
#	- hpdcache_params_pkg.sv before hdpcache_pkg.sv
#	- pkg before rtl
pre_cva6_synth:
	grep "{\w*}" ../../core/Flist.cva6|grep -v "instr_tracer"|grep -v "incdir"|grep -v "hpdcache.Flist" > Flist.cva6_synth
	grep "{\w*}" ../../core/cache_subsystem/hpdcache/rtl/hpdcache.Flist|grep -v "incdir" >> Flist.cva6_synth
	grep "hpdcache_pkg.sv" Flist.cva6_synth > hpdcache_pkg.tmp
	grep "HPDCACHE_TARGET_CFG" Flist.cva6_synth > HPDCACHE_TARGET_CFG.tmp
	grep "_pkg.sv" Flist.cva6_synth | grep -v "hpdcache_pkg.sv" > packages.tmp
	grep -v "hpdcache_pkg.sv" Flist.cva6_synth | grep -v "HPDCACHE_TARGET_CFG" | grep -v "_pkg.sv" > rtl.tmp
	cat packages.tmp > Flist.cva6_synth
	cat HPDCACHE_TARGET_CFG.tmp >> Flist.cva6_synth
	cat hpdcache_pkg.tmp >> Flist.cva6_synth
	cat rtl.tmp >> Flist.cva6_synth
	sed -i "s/^/analyze -f sverilog -lib ariane_lib -define HPDCACHE_ASSERT_OFF /" Flist.cva6_synth
	sed -i -e 's/behav/blackbox/g' Flist.cva6_synth

cva6_synth: pre_cva6_synth
	@echo $(PERIOD)
	@export $(EXPORT_LIST); $(DC_SHELL_PATH)/dc_shell -f ./cva6_synth.tcl -output synthesis_batch.log
	python scripts/gate_analysis.py '$(DESIGN_NAME)_$(TARGET)/reports/$(PERIOD)/$(DESIGN_NAME)_$(TECH_NAME)_synth_area.rpt' $(NAND2_AREA)
	mv $(DESIGN_NAME)_synth.v $(DESIGN_NAME)_$(TARGET)_synth.v
	mv $(DESIGN_NAME)_synth.v.sdf $(DESIGN_NAME)_$(TARGET)_synth.v.sdf
	sed -n -e '/module tc_sram_wrapper_256_64_00000008_00000001_00000001_none_0/,/endmodule/!p' $(DESIGN_NAME)_$(TARGET)_synth.v > tmp.v
	sed -n -e '/module tc_sram_wrapper_64_64_00000008_00000001_00000001_none_0/,/endmodule/!p' tmp.v > $(DESIGN_NAME)_$(TARGET)_synth_modified.v
	sed -i 's/cva6_ /cva6 /g' $(DESIGN_NAME)_$(TARGET)_synth_modified.v

cva6_read:
	@export $(EXPORT_LIST); $(DC_SHELL_PATH)/dc_shell -f cva6_read.tcl -gui

clean:
	@rm -rf work alib* *_LIB *log *svf netlist reports ${DESIGN_NAME}_${TARGET}
