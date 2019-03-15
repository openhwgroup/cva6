# Copyright 2018 ETH Zurich and University of Bologna.
# Copyright and related rights are licensed under the Solderpad Hardware
# License, Version 0.51 (the "License"); you may not use this file except in
# compliance with the License.  You may obtain a copy of the License at
# http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
# or agreed to in writing, software, hardware and materials distributed under
# this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
# CONDITIONS OF ANY KIND, either express or implied. See the License for the
# specific language governing permissions and limitations under the License.
#
# Author: Michael Schaffner <schaffner@iis.ee.ethz.ch>, ETH Zurich
# Date: 15.08.2018
# Description: Makefile for the dcache testbench.

library      ?= work
toplevel     ?= tb
src-list     := tb.list
inc-path     := $(shell pwd)/hdl/
src          := $(shell xargs printf '\n%s' < $(src-list)  | cut -b 1-)
compile_flag += +cover+i_dut -incr -64 -nologo
sim_opts     += -64 -coverage -classdebug -voptargs="+acc"
questa_version ?= ${QUESTASIM_VERSION}
incdir       += ../common/

build: clean
	vlib${questa_version} $(library)
	vlog${questa_version} -work $(library) -pedanticerrors $(src) $(compile_flag) +incdir+$(incdir)
	touch $(library)/.build

# this starts modelsim with gui
sim: build
	vsim${questa_version} -lib $(library) $(toplevel) -do "do wave.do" $(sim_opts)

# batch mode without gui
simc: build
	vsim${questa_version} -lib $(library) $(toplevel) -c -do "run -all; exit" $(sim_opts)

clean:
	rm -rf $(library)

.PHONY: clean simc sim build

