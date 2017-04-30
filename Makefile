# Author: Florian Zaruba, ETH Zurich
# Date: 03/19/2017
# Description: Makefile for linting and testing Ariane.

# compile everything in the following library
library = work
# Top level module to compile
top_level = core_tb
test_top_level = core_tb
tests = alu scoreboard fifo mem_arbiter store_queue
# path to agents
agents = tb/agents/fu_if/fu_if.sv tb/agents/fu_if/fu_if_agent_pkg.sv \
	include/ariane_pkg.svh tb/agents/scoreboard_if/scoreboard_if_agent_pkg.sv tb/common/eth_tb_pkg.sv  
#	uvm-scaffold/tmp/agent/mem_if/mem_if_agent_pkg.sv

interfaces = include/debug_if.svh include/mem_if.svh tb/agents/fifo_if/fifo_if.sv \
			 tb/agents/store_queue_if/store_queue_if.sv tb/agents/scoreboard_if/scoreboard_if.sv
# this list contains the standalone components
src = alu.sv tb/sequences/alu/alu_sequence_pkg.sv tb/env/alu/alu_env_pkg.sv tb/test/alu/alu_lib_pkg.sv  \
	  ptw.sv tlb.sv store_queue.sv \
	  if_stage.sv compressed_decoder.sv fetch_fifo.sv commit_stage.sv prefetch_buffer.sv \
	  mmu.sv lsu.sv fifo.sv tb/fifo_tb.sv mem_arbiter.sv \
	  scoreboard.sv issue_read_operands.sv decoder.sv id_stage.sv util/cluster_clock_gating.sv regfile.sv ex_stage.sv ariane.sv

tb =  tb/alu_tb.sv tb/mem_arbiter_tb.sv tb/core_tb.sv tb/scoreboard_tb.sv tb/store_queue_tb.sv

# Search here for include files (e.g.: non-standalone components)
incdir = ./includes
# Test case to run
test_case = alu_test
# QuestaSim Version
questa_version = -10.5c
compile_flag = +cover=bcfst+/dut

# Iterate over all include directories and write them with +incdir+ prefixed
# +incdir+ works for Verilator and QuestaSim
list_incdir = $(foreach dir, ${incdir}, +incdir+$(dir))

# Build the TB and module using QuestaSim
build:
	# Create the library
	vlib${questa_version} ${library}
	# Suppress message that always_latch may not be checked thoroughly bu Questa.
	# Compile agents
	vlog${questa_version} ${compile_flag} -incr ${agents} ${list_incdir} -suppress 2583
	# Compile interfaces
	vlog${questa_version} ${compile_flag} -incr ${interfaces} ${list_incdir} -suppress 2583
	# Compile source files
	vlog${questa_version} ${compile_flag} -incr ${src} ${tb}  ${list_incdir} -suppress 2583
	# Optimize top level
	vopt${questa_version} ${compile_flag} ${test_top_level} -o ${test_top_level}_optimized +acc -check_synthesis

# Run the specified test case
sim:
	# vsim${questa_version} ${top_level}_optimized -c -do "run -a"
	vsim${questa_version} ${top_level}_optimized +UVM_TESTNAME=${test_case}

$(tests):
	# Optimize top level
	vopt${questa_version} ${compile_flag} $@_tb -o $@_tb_optimized +acc -check_synthesis
	# vsim${questa_version} $@_tb_optimized
	vsim${questa_version} -c +UVM_TESTNAME=$@_test -coverage -do "coverage save -onexit $@.ucdb; run -a; quit -code [coverage attribute -name TESTSTATUS -concise]" $@_tb_optimized
# User Verilator to lint the target
lint:
	verilator ${src} --lint-only \
	${list_incdir}

clean:
	rm -rf work/

.PHONY:
	build lint
