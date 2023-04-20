# Copyright and related rights are licensed under the Solderpad Hardware
# License, Version 0.51 (the "License"); you may not use this file except in
# compliance with the License.  You may obtain a copy of the License at
# http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
# or agreed to in writing, software, hardware and materials distributed under
# this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
# CONDITIONS OF ANY KIND, either express or implied. See the License for the
# specific language governing permissions and limitations under the License.
#
# Authors:
# - Thomas Benz <tbenz@iis.ee.ethz.ch>

# select IIS-internal tool commands if we run on IIS machines
ifneq (,$(wildcard /etc/iis.version))
	VSIM        ?= questa-2022.3 vsim
	SYNOPSYS_DC ?= synopsys-2022.03 dcnxt_shell
else
	VSIM        ?= vsim
	SYNOPSYS_DC ?= dc_shell
endif

TBS         ?= axi_addr_test \
               axi_atop_filter \
               axi_cdc axi_delayer \
               axi_dw_downsizer \
               axi_dw_upsizer \
               axi_fifo \
               axi_isolate \
               axi_iw_converter \
               axi_lite_regs \
               axi_lite_to_apb \
               axi_lite_to_axi \
               axi_lite_mailbox \
               axi_lite_xbar \
               axi_modify_address \
               axi_serializer \
               axi_sim_mem \
               axi_to_axi_lite \
               axi_to_mem_banked \
               axi_xbar

SIM_TARGETS := $(addsuffix .log,$(addprefix sim-,$(TBS)))


.SHELL: bash

.PHONY: help all sim_all clean


help:
	@echo ""
	@echo "elab.log:     elaborates all files using Synopsys DC"
	@echo "compile.log:  compile files using Questasim"
	@echo "sim-#TB#.log: simulates a given testbench, available TBs are:"
	@echo "$(addprefix ###############-#,$(TBS))" | sed -e 's/ /\n/g' | sed -e 's/#/ /g'
	@echo "sim_all:      simulates all available testbenches"
	@echo ""
	@echo "clean:        cleans generated files"
	@echo ""


all: compile.log elab.log sim_all


sim_all: $(SIM_TARGETS)


build:
	mkdir -p $@


elab.log: Bender.yml | build
	export SYNOPSYS_DC="$(SYNOPSYS_DC)"; cd build && ../scripts/synth.sh | tee ../$@
	(! grep -n "Error:" $@)


compile.log: Bender.yml | build
	export VSIM="$(VSIM)"; cd build && ../scripts/compile_vsim.sh | tee ../$@
	(! grep -n "Error:" $@)


sim-%.log: compile.log
	export VSIM="$(VSIM)"; cd build && ../scripts/run_vsim.sh --random-seed $* | tee ../$@
	(! grep -n "Error:" $@)
	(! grep -n "Fatal:" $@)


clean:
	rm -rf build
	rm -f  *.log
