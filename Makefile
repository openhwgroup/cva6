# Author: Florian Zaruba, ETH Zurich
# Date: 03/19/2017
# Description: Makefile for linting and testing Ariane.

# compile everything in the following library
library ?= work
# Top level module to compile
top_level ?= ariane_tb
test_top_level ?= ariane_tb
# Maximum amount of cycles for a successful simulation run
max_cycles ?= 10000000
# Test case to run
test_case ?= core_test
# QuestaSim Version
questa_version ?=
# verilator version
verilator ?= verilator
# preset which runs a single test
riscv-test ?= rv64ui-p-add
# Sources
# Ariane PKG
ariane_pkg := include/riscv_pkg.sv src/debug/dm_pkg.sv include/ariane_pkg.sv include/nbdcache_pkg.sv
# utility modules
util := $(wildcard src/util/*.svh) src/util/instruction_tracer_pkg.sv src/util/instruction_tracer_if.sv \
		src/util/generic_fifo.sv src/util/cluster_clock_gating.sv src/util/behav_sram.sv
# test targets
tests := alu scoreboard fifo dcache_arbiter store_queue lsu core fetch_fifo
# UVM agents
agents := $(wildcard tb/agents/*/*.sv*)
# path to interfaces
interfaces := $(wildcard include/*.svh)
# UVM environments
envs := $(wildcard tb/env/*/*.sv*)
# UVM Sequences
sequences := $(wildcard tb/sequences/*/*.sv*)
# Test packages
test_pkg := $(wildcard tb/test/*/*sequence_pkg.sv*) $(wildcard tb/test/*/*_pkg.sv*)
# DPI
dpi := $(wildcard tb/dpi/*)
# this list contains the standalone components
src := $(wildcard src/*.sv) $(wildcard tb/common/*.sv) $(wildcard tb/common/*.v) $(wildcard src/axi2per/*.sv)  \
       $(wildcard src/axi_slice/*.sv)                                                                          \
       $(wildcard src/axi_node/*.sv) $(wildcard src/axi_mem_if/src/*.sv)                                       \
       $(filter-out src/debug/dm_pkg.sv, $(wildcard src/debug/*.sv)) $(wildcard bootrom/*.sv)                  \
       $(wildcard src/debug/debug_rom/*.sv)
# look for testbenches
tbs := tb/alu_tb.sv tb/ariane_tb.sv tb/ariane_testharness.sv tb/dcache_arbiter_tb.sv tb/store_queue_tb.sv tb/scoreboard_tb.sv tb/fifo_tb.sv

# RISCV-tests path
riscv-test-dir := tmp/riscv-tests/build/isa
riscv-tests := rv64ui-p-add rv64ui-p-addi rv64ui-p-slli rv64ui-p-addiw rv64ui-p-addw rv64ui-p-and rv64ui-p-auipc             \
               rv64ui-p-beq rv64ui-p-bge rv64ui-p-bgeu rv64ui-p-andi rv64ui-p-blt rv64ui-p-bltu rv64ui-p-bne                 \
               rv64ui-p-simple rv64ui-p-jal rv64ui-p-jalr rv64ui-p-or rv64ui-p-ori rv64ui-p-sub rv64ui-p-subw                \
               rv64ui-p-xor rv64ui-p-xori rv64ui-p-slliw rv64ui-p-sll rv64ui-p-slli rv64ui-p-sllw                            \
               rv64ui-p-slt rv64ui-p-slti rv64ui-p-sltiu rv64ui-p-sltu rv64ui-p-sra rv64ui-p-srai                            \
               rv64ui-p-sraiw rv64ui-p-sraw rv64ui-p-srl rv64ui-p-srli rv64ui-p-srliw rv64ui-p-srlw                          \
               rv64ui-p-lb rv64ui-p-lbu rv64ui-p-ld rv64ui-p-lh rv64ui-p-lhu rv64ui-p-lui rv64ui-p-lw rv64ui-p-lwu           \
               rv64mi-p-csr rv64mi-p-mcsr rv64mi-p-illegal rv64mi-p-ma_addr rv64mi-p-ma_fetch rv64mi-p-sbreak rv64mi-p-scall \
               rv64si-p-csr rv64si-p-ma_fetch rv64si-p-scall rv64si-p-wfi rv64si-p-sbreak rv64si-p-dirty                     \
               rv64uc-p-rvc                                                                                                  \
               rv64ui-v-add rv64ui-v-addi rv64ui-p-slli rv64ui-v-addiw rv64ui-v-addw rv64ui-v-and rv64ui-v-auipc             \
               rv64ui-v-beq rv64ui-v-bge rv64ui-v-bgeu rv64ui-v-andi rv64ui-v-blt rv64ui-v-bltu rv64ui-v-bne                 \
               rv64ui-v-simple rv64ui-v-jal rv64ui-v-jalr rv64ui-v-or rv64ui-v-ori rv64ui-v-sub rv64ui-v-subw                \
               rv64ui-v-xor rv64ui-v-xori rv64ui-v-slliw rv64ui-v-sll rv64ui-v-slli rv64ui-v-slliw                           \
               rv64ui-v-slt rv64ui-v-slti rv64ui-v-sltiu rv64ui-v-sltu rv64ui-v-sra rv64ui-v-srai                            \
               rv64ui-v-sraiw rv64ui-v-sraw rv64ui-v-srl rv64ui-v-srli rv64ui-v-srliw rv64ui-v-srlw                          \
               rv64ui-v-lb rv64ui-v-lbu rv64ui-v-ld rv64ui-v-lh rv64ui-v-lhu rv64ui-v-lui                                    \
               rv64um-p-mul rv64um-p-mulh rv64um-p-mulhsu rv64um-p-mulhu rv64um-p-div rv64um-p-divu rv64um-p-rem             \
               rv64um-p-remu rv64um-p-mulw rv64um-p-divw rv64um-p-divuw rv64um-p-remw rv64um-p-remuw                         \
               rv64um-v-mul rv64um-v-mulh rv64um-v-mulhsu rv64um-v-mulhu rv64um-v-div rv64um-v-divu rv64um-v-rem             \
               rv64um-v-remu rv64um-v-mulw rv64um-v-divw rv64um-v-divuw rv64um-v-remw rv64um-v-remuw


# failed test directory
failed-tests := $(wildcard failedtests/*.S)
# Search here for include files (e.g.: non-standalone components)
incdir := ./includes
# Compile and sim flags
compile_flag += +cover=bcfst+/dut -incr -64 -nologo -quiet -suppress 13262 -permissive
uvm-flags += +UVM_NO_RELNOTES
# Iterate over all include directories and write them with +incdir+ prefixed
# +incdir+ works for Verilator and QuestaSim
list_incdir := $(foreach dir, ${incdir}, +incdir+$(dir))

# Build the TB and module using QuestaSim
build: $(library) $(library)/.build-agents $(library)/.build-interfaces $(library)/.build-components \
		$(library)/.build-srcs $(library)/.build-tb $(library)/.build-dpi
		# Optimize top level
	vopt$(questa_version) $(compile_flag) -work $(library)  $(test_top_level) -o $(test_top_level)_optimized +acc -check_synthesis

# src files
$(library)/.build-srcs: $(util) $(src)
	vlog$(questa_version) $(compile_flag) -work $(library) $(filter %.sv,$(util)) $(list_incdir) -suppress 2583
	# Suppress message that always_latch may not be checked thoroughly by QuestaSim.
	# Compile agents, interfaces and environments
	vlog$(questa_version) $(compile_flag) -work $(library) -pedanticerrors $(src) $(list_incdir) -suppress 2583
	touch $(library)/.build-srcs

# build TBs
$(library)/.build-tb: $(dpi) $(tbs)
	# Compile top level
	vlog$(questa_version) -sv $(tbs) -work $(library)
	touch $(library)/.build-tb

# compile DPIs
$(library)/.build-dpi: $(dpi)
	# Compile C-code and generate .so file
	# g++ -lfesvr -c -fPIC -m64 -std=c++0x -I$(QUESTASIM_HOME)/include -o $(library)/ariane_dpi.o tb/dpi/SimDTM.cc
	# g++ -shared -m64 -o $(library)/ariane_dpi.so $(library)/ariane_dpi.o -lfesvr
	gcc -shared -fPIC -std=c++0x -Bsymbolic -I$(QUESTASIM_HOME)/include -o work/ariane_dpi.so tb/dpi/SimDTM.cc -lfesvr -lstdc++
	touch $(library)/.build-dpi

# Compile Sequences and Tests
$(library)/.build-components: $(envs) $(sequences) $(test_pkg)
	vlog$(questa_version) $(compile_flag) -work $(library) $(filter %.sv,$(envs)) $(filter %.sv,$(sequences)) \
													$(filter %.sv,$(test_pkg)) ${list_incdir} -suppress 2583
	touch $(library)/.build-components

# Compile Agents
$(library)/.build-agents: $(agents) $(ariane_pkg)
	vlog$(questa_version) $(compile_flag) -work $(library) $(ariane_pkg) $(filter %.sv,$(agents)) $(list_incdir) -suppress 2583
	touch $(library)/.build-agents

# Compile Interfaces
$(library)/.build-interfaces: $(interfaces)
	vlog$(questa_version) $(compile_flag) -work $(library) $(interfaces) $(list_incdir) -suppress 2583
	touch $(library)/.build-interfaces

$(library):
	# Create the library
	vlib${questa_version} ${library}

sim: build
	vsim${questa_version} +permissive -64 -lib ${library} +UVM_TESTNAME=${test_case} +BASEDIR=$(riscv-test-dir) \
	+ASMTEST=$(riscv-test)  $(uvm-flags) +UVM_VERBOSITY=HIGH -coverage -classdebug -gblso $(RISCV)/lib/libfesvr.so \
	-sv_lib $(library)/ariane_dpi \
	-do "do tb/wave/wave_core.do"  +permissive-off ${top_level}_optimized

simc: build
	vsim${questa_version} +permissive -64 -c -lib ${library} +max-cycles=$(max_cycles) +UVM_TESTNAME=${test_case} \
	 +BASEDIR=$(riscv-test-dir) $(uvm-flags) "+UVM_VERBOSITY=HIGH" -coverage -classdebug\
	 -gblso $(RISCV)/lib/libfesvr.so -sv_lib $(library)/ariane_dpi -do "run -all; do tb/wave/wave_core.do; exit" +permissive-off ${top_level}_optimized

run-asm-tests: build
	$(foreach test, $(riscv-tests), vsim$(questa_version) -64 +BASEDIR=$(riscv-test-dir) +max-cycles=$(max_cycles) \
		+UVM_TESTNAME=$(test_case) $(uvm-flags) +ASMTEST=$(test) +uvm_set_action="*,_ALL_,UVM_ERROR,UVM_DISPLAY|UVM_STOP" -c \
		-coverage -classdebug  -sv_lib $(library)/ariane_dpi -do "coverage save -onexit $@.ucdb; run -a; quit -code [coverage attribute -name TESTSTATUS -concise]"  \
		$(library).$(test_top_level)_optimized;)

run-asm-tests-verilator: verilate
	$(foreach test, $(riscv-tests), obj_dir/Variane_testharness --label="Starting: $(riscv-test-dir)/$(test)" $(riscv-test-dir)/$(test);)

run-failed-tests: build
	# make the tests
	cd failedtests && make
	# run the RTL simulation
	$(foreach test, $(failed-tests:.S=), vsim$(questa_version) -64 +BASEDIR=. +max-cycles=$(max_cycles) \
		+UVM_TESTNAME=$(test_case) $(uvm-flags) +ASMTEST=$(test) +signature=$(test).rtlsim.sig +uvm_set_action="*,_ALL_,UVM_ERROR,UVM_DISPLAY|UVM_STOP" -c \
		-coverage -classdebug  -sv_lib $(library)/ariane_dpi -do "coverage save -onexit $@.ucdb; run -a; quit -code [coverage attribute -name TESTSTATUS -concise]" \
		$(library).$(test_top_level)_optimized;)
	# run it on spike
	$(foreach test, $(failed-tests:.S=), spike +signature=$(test).spike.sig $(test);)
	# diff the results
	$(foreach test, $(failed-tests:.S=), diff $(test).spike.sig $(test).rtlsim.sig;)

# Run the specified test case
$(tests): build
	# Optimize top level
	vopt${questa_version} -work ${library} ${compile_flag} $@_tb -o $@_tb_optimized +acc -check_synthesis
	# vsim${questa_version} $@_tb_optimized
	# vsim${questa_version} +UVM_TESTNAME=$@_test -coverage -classdebug $@_tb_optimized
	vsim${questa_version} -64 +UVM_TESTNAME=$@_test +ASMTEST=$(riscv-test-dir)/$(riscv-test) \
	+uvm_set_action="*,_ALL_,UVM_ERROR,UVM_DISPLAY|UVM_STOP" -c -coverage -classdebug -sv_lib $(library)/ariane_dpi \
	-do "coverage save -onexit $@.ucdb; run -a; quit -code [coverage attribute -name TESTSTATUS -concise]" \
	${library}.$@_tb_optimized

# User Verilator, at some point in the future this will be auto-generated
verilate:
	$(verilator)                                                     \
    $(ariane_pkg)                                                    \
    tb/ariane_testharness.sv                                         \
    $(filter-out src/ariane_regfile.sv, $(wildcard src/*.sv))        \
    $(wildcard src/axi_slice/*.sv)                                   \
    $(filter-out src/debug/dm_pkg.sv, $(wildcard src/debug/*.sv))    \
    src/debug/debug_rom/debug_rom.sv                                 \
    src/util/generic_fifo.sv                                         \
    tb/common/SimDTM.sv                                              \
    bootrom/bootrom.sv                                               \
    src/util/cluster_clock_gating.sv                                 \
    src/util/behav_sram.sv                                           \
    src/axi_mem_if/src/axi2mem.sv                                    \
    tb/agents/axi_if/axi_if.sv                                       \
    +incdir+src/axi_node                                             \
    --unroll-count 256                                               \
    -Werror-PINMISSING                                               \
    -Werror-IMPLICIT                                                 \
    -Wno-fatal                                                       \
    -Wno-PINCONNECTEMPTY                                             \
    -Wno-ASSIGNDLY                                                   \
    -Wno-DECLFILENAME                                                \
    -Wno-UNOPTFLAT                                                   \
    -Wno-UNUSED                                                      \
    -Wno-ASSIGNDLY                                                   \
    -LDFLAGS "-lfesvr" -CFLAGS "-std=c++11" -Wall --cc --trace --vpi --trace-structs \
    $(list_incdir) --top-module ariane_testharness --exe tb/ariane_tb.cpp tb/dpi/SimDTM.cc
	cd obj_dir && make -j8 -f Variane_testharness.mk

# -Werror-UNDRIVEN
# -Werror-BLKSEQ

verify:
	qverify vlog -sv src/csr_regfile.sv

clean:
	rm -rf work/ *.ucdb
	rm -rf obj_dir

.PHONY:
	build lint build-moore
