# Author: Florian Zaruba, ETH Zurich
# Date: 03/19/2017
# Description: Makefile for linting and testing Ariane.

# questa library
library        ?= work
# verilator lib
ver-library    ?= work-ver
# library for DPI
dpi-library    ?= work-dpi
# Top level module to compile
top_level      ?= ariane_tb
# Maximum amount of cycles for a successful simulation run
max_cycles     ?= 10000000
# Test case to run
test_case      ?= core_test
# QuestaSim Version
questa_version ?= -10.7b
# verilator version
verilator      ?= verilator
# traget option
target-options ?=
# additional definess
defines        ?= WT_DCACHE
# test name for torture runs (binary name)
test-location  ?= output/test
# set to either nothing or -log
torture-logs   :=
# custom elf bin to run with sim or sim-verilator
elf-bin        ?= tmp/riscv-tests/build/benchmarks/dhrystone.riscv
# root path
mkfile_path := $(abspath $(lastword $(MAKEFILE_LIST)))
root-dir := $(dir $(mkfile_path))

BENDER_BUILD_DIR:=.

ifndef RISCV
$(error RISCV not set - please point your RISCV variable to your RISCV installation)
endif

ifndef QUESTASIM_HOME
$(error QUESTASIM not set - please point to your QUESTA installation)
endif

# spike tandem verification
ifdef spike-tandem
    compile_flag += -define SPIKE_TANDEM
    ifndef preload
        $(error Tandem verification requires preloading)
    endif
endif


ifdef spike-tandem
    util += tb/common/spike.sv
endif

util := $(addprefix $(root-dir), $(util))
# Test packages
test_pkg := $(wildcard tb/test/*/*sequence_pkg.sv*) \
			$(wildcard tb/test/*/*_pkg.sv*)

# DPI
dpi := $(patsubst tb/dpi/%.cc, ${dpi-library}/%.o, $(wildcard tb/dpi/*.cc))

# filter spike stuff if tandem is not activated
ifndef spike-tandem
    dpi := $(filter-out ${dpi-library}/spike.o ${dpi-library}/sim_spike.o, $(dpi))
endif

# filter dromajo stuff if dromajo is not activated
ifndef DROMAJO
    dpi := $(filter-out ${dpi-library}/dromajo_cosim_dpi.o, $(dpi))
endif

dpi_hdr := $(wildcard tb/dpi/*.h)
dpi_hdr := $(addprefix $(root-dir), $(dpi_hdr))
CFLAGS := -I$(QUESTASIM_HOME)/include         \
          -I$(RISCV)/include                  \
          -I$(SPIKE_ROOT)/include             \
          $(if $(DROMAJO), -I../tb/dromajo/src,) \
          -std=c++11 -I../tb/dpi -O3

ifdef XCELIUM_HOME
CFLAGS += -I$(XCELIUM_HOME)/tools/include
else
$(warning XCELIUM_HOME not set which is necessary for compiling DPIs when using XCELIUM)
endif

ifdef spike-tandem
    CFLAGS += -Itb/riscv-isa-sim/install/include/spike
endif

# Compile and sim flags
compile_flag     += +cover=bcfst+/dut -incr -64 -nologo -quiet -suppress 13262 -permissive +define+$(defines)
uvm-flags        += +UVM_NO_RELNOTES +UVM_VERBOSITY=LOW
questa-flags     += -t 1ns -64 -coverage -classdebug $(gui-sim) $(QUESTASIM_FLAGS)
compile_flag_vhd += -64 -nologo -quiet -2008

compile_flag_bender   += +cover=bcfst+/dut -incr -64 -nologo -quiet -suppress 13262 -permissive 


# Iterate over all include directories and write them with +incdir+ prefixed
# +incdir+ works for Verilator and QuestaSim
list_incdir := $(foreach dir, ${incdir}, +incdir+$(dir))

# if defined, calls the questa targets in batch mode
ifdef batch-mode
	questa-flags += -c
	questa-cmd   := -do "coverage save -onexit tmp/$@.ucdb; run -a; quit -code [coverage attribute -name TESTSTATUS -concise]"
	questa-cmd   += -do " log -r /*; run -all;"
else
	questa-cmd   := -do " log -r /*; run -all;"
endif
# we want to preload the memories
ifdef preload
	questa-cmd += +PRELOAD=$(preload)
	elf-bin = none
endif

ifdef spike-tandem
    questa-cmd += -gblso tb/riscv-isa-sim/install/lib/libriscv.so
endif

# remote bitbang is enabled
ifdef rbb
	questa-cmd += +jtag_rbb_enable=1
else
	questa-cmd += +jtag_rbb_enable=0
endif

bender:
	curl --proto '=https' --tlsv1.2 https://fabianschuiki.github.io/bender/init -sSf | sh

update:
	./bender update

libbender:
	@vlib work
	vmap work ./work


scripts:
	./bender script vsim \
		--vlog-arg="$(compile_flag)  -work  $(library) -suppress 2583 -suppress 13314" --vcom-arg="$(compile_flag_vhd) -work  $(library) -pedanticerrors" \
    -t rtl -t test > compile.tcl

benderrun: libbender $(util) $(library)
	@test -f Bender.lock || { echo "ERROR: Bender.lock file does not exist. Did you run make checkout in bender mode?"; exit 1; }
	vsim -c -do 'source compile.tcl; quit'
	touch $(library)/.build-srcs

bendertb: benderrun $(dpi)
	touch $(library)/.build-tb

build: bendertb 	$(dpi-library)/ariane_dpi.so
	vopt $(compile_flag) -work $(library)  $(top_level) -o $(top_level)_optimized +acc -check_synthesis


$(library):
	vlib${questa_version} $(library)

# compile DPIs
$(dpi-library)/%.o: tb/dpi/%.cc $(dpi_hdr)
	mkdir -p $(dpi-library)
	$(CXX) -shared -fPIC -std=c++0x -Bsymbolic $(CFLAGS) -c $< -o $@

$(dpi-library)/ariane_dpi.so: $(dpi)
	mkdir -p $(dpi-library)
	# Compile C-code and generate .so file
	$(CXX) -shared -m64 -o $(dpi-library)/ariane_dpi.so $? -L$(RISCV)/lib -L$(SPIKE_ROOT)/lib -Wl,-rpath,$(RISCV)/lib -Wl,-rpath,$(SPIKE_ROOT)/lib -lfesvr

# single test runs on Questa can be started by calling make <testname>, e.g. make towers.riscv
# the test names are defined in ci/riscv-asm-tests.list, and in ci/riscv-benchmarks.list
# if you want to run in batch mode, use make <testname> batch-mode=1
# alternatively you can call make sim elf-bin=<path/to/elf-bin> in order to load an arbitrary binary		
 
generate-trace-vsim:
	make sim preload=$(preload) elf-bin= batch-mode=1
	make generate-trace

run: 
	vsim${questa_version} +permissive $(questa-flags) $(questa-cmd) -lib $(library) +MAX_CYCLES=$(max_cycles) +UVM_TESTNAME=$(test_case) \
	+BASEDIR=$(riscv-test-dir) $(uvm-flags) $(QUESTASIM_FLAGS) -gblso $(SPIKE_ROOT)/lib/libfesvr.so -sv_lib $(dpi-library)/ariane_dpi  \
	${top_level}_optimized +permissive-off ++$(elf-bin) ++$(target-options) | tee sim.log


sim: build run

clean:
	rm -rf $(riscv-torture-dir)/output/test*
	rm -rf $(library)/ $(dpi-library)/ $(ver-library)/
	rm -f tmp/*.ucdb tmp/*.log *.wlf *vstf wlft* *.ucdb
	rm -f *log
	rm -f transcript
	rm -f uart
