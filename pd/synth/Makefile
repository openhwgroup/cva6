# Copyright 2021 Thales DIS design services SAS
#
# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Jean-Roch COULON - Thales
#

DESIGN_NAME          ?= cva6
PERIOD               ?= 17
FOUNDRY_PATH         ?=
LOCAL_LIB_PATH       ?=/shares/common/tools/RAMs/
TARGET_LIBRARY_FILES  = $(TECH_NAME).db
INPUT_DELAY          ?= 0.46
OUTPUT_DELAY         ?= 0.11
DC_SHELL_PATH        ?= /opt/synopsys/syn/Q-2019.12/bin/
NAND2_AREA           ?= 1120
TARGET               ?= cv32a65x

EXPORT_LIST=SNPSLMD_QUEUE=TRUE TECH_NAME=$(TECH_NAME) DESIGN_NAME=$(DESIGN_NAME) TARGET=$(TARGET) TERM=vt100 PERIOD=$(PERIOD) FOUNDRY_PATH=$(FOUNDRY_PATH) LOCAL_LIB_PATH=$(LOCAL_LIB_PATH) TARGET_LIBRARY_FILES=$(TARGET_LIBRARY_FILES) INPUT_DELAY=$(INPUT_DELAY) OUTPUT_DELAY=$(OUTPUT_DELAY)

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
	grep "_pkg.sv" Flist.cva6_synth | grep -v "hpdcache_pkg.sv" > packages.tmp
	grep -v "hpdcache_pkg.sv" Flist.cva6_synth | grep -v "HPDCACHE_TARGET_CFG" | grep -v "_pkg.sv" > rtl.tmp
	cat packages.tmp > Flist.cva6_synth
	cat hpdcache_pkg.tmp >> Flist.cva6_synth
	cat rtl.tmp >> Flist.cva6_synth
	sed -i "s/^/analyze -f sverilog -lib ariane_lib -define HPDCACHE_ASSERT_OFF /" Flist.cva6_synth
	sed -i -e 's/behav/blackbox/g' Flist.cva6_synth

# Deprecated
cva6_synth: pre_cva6_synth
	@echo $(PERIOD)
	@export $(EXPORT_LIST); $(DC_SHELL_PATH)/dc_shell -f ./cva6_synth.tcl -output synthesis_batch.log
	python scripts/gate_analysis.py '$(DESIGN_NAME)_$(TARGET)/$(PERIOD)/reports/$(DESIGN_NAME)_$(TECH_NAME)_synth_area.rpt' $(NAND2_AREA)
	mv $(DESIGN_NAME)_synth.v $(DESIGN_NAME)_$(TARGET)_synth.v
	mv $(DESIGN_NAME)_synth.v.sdf $(DESIGN_NAME)_$(TARGET)_synth.v.sdf
	sed -i 's/cva6_ /cva6 /g' $(DESIGN_NAME)_$(TARGET)_synth.v
	echo $(NAND2_AREA) > $(DESIGN_NAME)_$(TARGET)/nand2area.txt

# Supported for cv32a65x
rm_synth: pre_cva6_synth
	@echo $(PERIOD) 
	cp Flist.cva6_synth ../../$(SYNTH_FLOW_NAME)/synth/
	CVA6_REPO_DIR=$(CVA6_REPO_DIR) make -C ../../$(SYNTH_FLOW_NAME)/synth/ platform_synth_topo
	sed -i -n -e '/module hpdcache_sram_wbyteenable_1rw_00000007_00000040_00000080/,/endmodule/!p' $(DESIGN_NAME)_$(TARGET)_synth.v
	sed -i -n -e '/module hpdcache_sram_1rw_00000006_0000001a_00000040/,/endmodule/!p' $(DESIGN_NAME)_$(TARGET)_synth.v
	echo $(NAND2_AREA) > $(DESIGN_NAME)_$(TARGET)/nand2area.txt

cva6_read:
	@export $(EXPORT_LIST); $(DC_SHELL_PATH)/dc_shell -f cva6_read.tcl -gui

clean:
	@rm -rf work alib* *_LIB *log *svf netlist reports ${DESIGN_NAME}_${TARGET}
