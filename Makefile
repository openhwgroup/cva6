# Author: Florian Zaruba, ETH Zurich
# Date: 03/19/2017
# Description: Makefile for linting and testing Ariane.

# compile everything in the following library
library = work
# Top level module to compile
top_level = core_tb
test_top_level = core_tb

# utility modules
util = $(wildcard src/util/*.sv)
# test targets
tests = alu scoreboard fifo mem_arbiter store_queue lsu core fetch_fifo
# UVM agents
agents = include/ariane_pkg.svh $(wildcard tb/agents/*/*.sv)
# path to interfaces
interfaces = $(wildcard include/*.svh)
# UVM environments
envs = $(wildcard tb/env/*/*.sv)
# UVM Sequences
sequences =  $(wildcard tb/sequences/*/*.sv)
# Test packages
test_pkg = $(wildcard tb/test/*/*sequence_pkg.sv) $(wildcard tb/test/*/*_pkg.sv)

# this list contains the standalone components
src = $(wildcard src/*.sv) $(wildcard tb/common/*.sv)
# look for testbenches
tbs = $(wildcard tb/*_tb.sv)

# Search here for include files (e.g.: non-standalone components)
incdir = ./includes
# Test case to run
test_case = core_test
# QuestaSim Version
questa_version = -10.5c
compile_flag = +cover=bcfst+/dut
# Moore binary
moore = ~fschuiki/bin/moore
# Iterate over all include directories and write them with +incdir+ prefixed
# +incdir+ works for Verilator and QuestaSim
list_incdir = $(foreach dir, ${incdir}, +incdir+$(dir))
# create library if not exists

$(library):
	# Create the library
	vlib${questa_version} ${library}

# Build the TB and module using QuestaSim
build: $(library) build-agents build-interfaces
	# Suppress message that always_latch may not be checked thoroughly by QuestaSim.
	vlog${questa_version} ${compile_flag} -work ${library} -incr ${util} ${list_incdir} -suppress 2583
	# Compile agents, interfaces and environments
	vlog${questa_version} ${compile_flag} -work ${library}  -incr ${envs} ${sequences} ${test_pkg} ${list_incdir} -suppress 2583
	# Compile source files
	vlog${questa_version} ${compile_flag} -work ${library}  -incr ${src} ${tbs}  ${list_incdir} -suppress 2583
	# Optimize top level
	vopt${questa_version} ${compile_flag} -work ${library}  ${test_top_level} -o ${test_top_level}_optimized +acc -check_synthesis

build-agents: ${agents}
	vlog${questa_version} ${compile_flag} -work ${library} -incr ${agents} ${list_incdir} -suppress 2583

build-interfaces: ${interfaces}
	vlog${questa_version} ${compile_flag} -work ${library}  -incr ${interfaces} ${list_incdir} -suppress 2583

# Run the specified test case
sim:
	# vsim${questa_version} ${top_level}_optimized -c -do "run -a"
	vsim${questa_version} -lib ${library} ${top_level}_optimized +UVM_TESTNAME=${test_case} -coverage -classdebug -do "do tb/wave/wave_core.do"

$(tests):
	# Optimize top level
	vopt${questa_version} -work ${library} ${compile_flag} $@_tb -o $@_tb_optimized +acc -check_synthesis
	# vsim${questa_version} $@_tb_optimized
	# vsim${questa_version} +UVM_TESTNAME=$@_test -coverage -classdebug $@_tb_optimized
	vsim${questa_version} +UVM_TESTNAME=$@_test +uvm_set_action="*,_ALL_,UVM_ERROR,UVM_DISPLAY|UVM_STOP" -c -coverage -classdebug -do "coverage save -onexit $@.ucdb; run -a; quit -code [coverage attribute -name TESTSTATUS -concise]" ${library}.$@_tb_optimized

build-moore:
	[ ! -e .moore ] || rm .moore
	# $(moore) compile src/fifo.sv
	$(foreach src_file, $(src), $(moore) compile $(src_file);)

# User Verilator to lint the target
lint:
	verilator ${src} --lint-only \
	${list_incdir}

clean:
	rm -rf work/ *.ucdb

.PHONY:
	build lint build-moore
