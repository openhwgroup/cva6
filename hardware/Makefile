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

ifndef RISCV
$(error RISCV not set - please point your RISCV variable to your RISCV installation)
endif



# spike tandem verification
ifdef spike-tandem
    compile_flag += -define SPIKE_TANDEM
    ifndef preload
        $(error Tandem verification requires preloading)
    endif
endif

# Sources
# Package files -> compile first
ariane_pkg := include/riscv_pkg.sv                          \
              deps/cva6/riscv-dbg/src/dm_pkg.sv                   \
              include/ariane_pkg.sv                         \
              include/std_cache_pkg.sv                      \
              include/wt_cache_pkg.sv                       \
              deps/cva6/axi/src/axi_pkg.sv                        \
              deps/cva6/register_interface/src/reg_intf.sv        \
              deps/cva6/register_interface/src/reg_intf_pkg.sv    \
              include/axi_intf.sv                           \
              host/ariane_soc_pkg.sv                          \
              host/ariane_axi_soc_pkg.sv                      \
              include/ariane_axi_pkg.sv                     \
              deps/cva6/fpu/src/fpnew_pkg.sv                      \
              deps/cva6/fpu/src/fpu_div_sqrt_mvp/hdl/defs_div_sqrt_mvp.sv
ariane_pkg := $(addprefix $(root-dir), $(ariane_pkg))

# utility modules
util := include/instr_tracer_pkg.sv                         \
        deps/cva6/util/instr_tracer_if.sv                         \
        deps/cva6/util/instr_tracer.sv                            \
        deps/cva6/tech_cells_generic/src/cluster_clock_gating.sv  \
        tb/common/mock_uart.sv                              \
        deps/cva6/util/sram.sv

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

# this list contains the standalone components
src :=  $(filter-out deps/cva6/ariane_regfile.sv, $(wildcard deps/cva6/*.sv))              \
        $(filter-out deps/cva6/fpu/src/fpnew_pkg.sv, $(wildcard deps/cva6/fpu/src/*.sv))   \
        $(filter-out deps/cva6/fpu/src/fpu_div_sqrt_mvp/hdl/defs_div_sqrt_mvp.sv,    \
        $(wildcard deps/cva6/fpu/src/fpu_div_sqrt_mvp/hdl/*.sv))                     \
        $(wildcard deps/cva6/frontend/*.sv)                                          \
        $(filter-out deps/cva6/cache_subsystem/std_no_dcache.sv,                     \
        $(wildcard deps/cva6/cache_subsystem/*.sv))                                  \
        $(wildcard ../bootrom/*.sv)                                               \
        $(wildcard deps/cva6/clint/*.sv)                                             \
        $(wildcard ../fpga/src/axi2apb/src/*.sv)                                  \
        $(wildcard ../fpga/src/apb_timer/*.sv)                                    \
        $(wildcard ../fpga/src/axi_slice/src/*.sv)                                \
        $(wildcard deps/cva6/axi_node/src/*.sv)                                      \
        $(wildcard deps/cva6/axi_riscv_atomics/src/*.sv)                             \
        $(wildcard deps/cva6/axi_mem_if/src/*.sv)                                    \
        $(wildcard deps/cva6/pmp/src/*.sv)                                           \
        deps/cva6/rv_plic/rtl/rv_plic_target.sv                                      \
        deps/cva6/rv_plic/rtl/rv_plic_gateway.sv                                     \
        deps/cva6/rv_plic/rtl/plic_regmap.sv                                         \
        deps/cva6/rv_plic/rtl/plic_top.sv                                            \
        deps/cva6/riscv-dbg/src/dmi_cdc.sv                                           \
        deps/cva6/riscv-dbg/src/dmi_jtag.sv                                          \
        deps/cva6/riscv-dbg/src/dmi_jtag_tap.sv                                      \
        deps/cva6/riscv-dbg/src/dm_csrs.sv                                           \
        deps/cva6/riscv-dbg/src/dm_mem.sv                                            \
        deps/cva6/riscv-dbg/src/dm_sba.sv                                            \
        deps/cva6/riscv-dbg/src/dm_top.sv                                            \
        deps/cva6/riscv-dbg/debug_rom/debug_rom.sv                                   \
        deps/cva6/register_interface/src/apb_to_reg.sv                               \
        deps/cva6/axi/src/axi_multicut.sv                                            \
        deps/cva6/common_cells/src/deprecated/generic_fifo.sv                        \
        deps/cva6/common_cells/src/deprecated/pulp_sync.sv                           \
        deps/cva6/common_cells/src/deprecated/find_first_one.sv                      \
        deps/cva6/common_cells/src/rstgen_bypass.sv                                  \
        deps/cva6/common_cells/src/rstgen.sv                                         \
        deps/cva6/common_cells/src/stream_mux.sv                                     \
        deps/cva6/common_cells/src/stream_demux.sv                                   \
        deps/cva6/common_cells/src/exp_backoff.sv                                    \
        deps/cva6/util/axi_master_connect.sv                                         \
        deps/cva6/util/axi_slave_connect.sv                                          \
        deps/cva6/util/axi_master_connect_rev.sv                                     \
        deps/cva6/util/axi_slave_connect_rev.sv                                      \
        deps/cva6/axi/src/axi_cut.sv                                                 \
        deps/cva6/axi/src/axi_join.sv                                                \
        deps/cva6/axi/src/axi_delayer.sv                                             \
        deps/cva6/axi/src/axi_to_axi_lite.sv                                         \
        deps/cva6/fpga-support/rtl/SyncSpRamBeNx64.sv                                \
        deps/cva6/common_cells/src/unread.sv                                         \
        deps/cva6/common_cells/src/sync.sv                                           \
        deps/cva6/common_cells/src/cdc_2phase.sv                                     \
        deps/cva6/common_cells/src/spill_register.sv                                 \
        deps/cva6/common_cells/src/sync_wedge.sv                                     \
        deps/cva6/common_cells/src/edge_detect.sv                                    \
        deps/cva6/common_cells/src/stream_arbiter.sv                                 \
        deps/cva6/common_cells/src/stream_arbiter_flushable.sv                       \
        deps/cva6/common_cells/src/deprecated/fifo_v1.sv                             \
        deps/cva6/common_cells/src/deprecated/fifo_v2.sv                             \
        deps/cva6/common_cells/src/fifo_v3.sv                                        \
        deps/cva6/common_cells/src/lzc.sv                                            \
        deps/cva6/common_cells/src/popcount.sv                                       \
        deps/cva6/common_cells/src/rr_arb_tree.sv                                    \
        deps/cva6/common_cells/src/deprecated/rrarbiter.sv                           \
        deps/cva6/common_cells/src/stream_delay.sv                                   \
        deps/cva6/common_cells/src/lfsr_8bit.sv                                      \
        deps/cva6/common_cells/src/lfsr_16bit.sv                                     \
        deps/cva6/common_cells/src/delta_counter.sv                                  \
        deps/cva6/common_cells/src/counter.sv                                        \
        deps/cva6/common_cells/src/shift_reg.sv                                      \
        deps/cva6/tech_cells_generic/src/pulp_clock_gating.sv                        \
        deps/cva6/tech_cells_generic/src/cluster_clock_inverter.sv                   \
        deps/cva6/tech_cells_generic/src/pulp_clock_mux2.sv                          \
        deps/cva6/tech_cells_generic/src/generic_memory.sv                           \
        host/host_domain.sv                                               \
        host/ariane_peripherals.sv                                               \
        tb/common/uart.sv                                                      \
        tb/common/SimDTM.sv                                                    \
        tb/common/SimJTAG.sv

src := $(addprefix $(root-dir), $(src))

uart_src := $(wildcard ../fpga/src/apb_uart/src/*.vhd)
uart_src := $(addprefix $(root-dir), $(uart_src))

fpga_src :=  $(wildcard ../fpga/src/*.sv) $(wildcard ../fpga/src/bootrom/*.sv) $(wildcard ../fpga/src/ariane-ethernet/*.sv)
fpga_src := $(addprefix $(root-dir), $(fpga_src))

# look for testbenches
tbs := tb/ariane_tb.sv host/host_domain.sv

# Search here for include files (e.g.: non-standalone components)
incdir := deps/cva6/common_cells/include/
# Compile and sim flags
compile_flag     += +cover=bcfst+/dut -incr -64 -nologo -quiet -suppress 13262 -permissive +define+$(defines)
uvm-flags        += +UVM_NO_RELNOTES +UVM_VERBOSITY=LOW
questa-flags     += -t 1ns -64 -coverage -classdebug $(gui-sim) $(QUESTASIM_FLAGS)
compile_flag_vhd += -64 -nologo -quiet -2008

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

# Build the TB and module using QuestaSim
build: $(library) $(library)/.build-srcs $(library)/.build-tb $(dpi-library)/ariane_dpi.so
	# Optimize top level
	vopt$(questa_version) $(compile_flag) -work $(library)  $(top_level) -o $(top_level)_optimized +acc -check_synthesis

# src files
$(library)/.build-srcs: $(util) $(library)
	vlog$(questa_version) $(compile_flag) -work $(library) $(filter %.sv,$(ariane_pkg)) $(list_incdir) -suppress 2583
	# vcom$(questa_version) $(compile_flag_vhd) -work $(library) -pedanticerrors $(filter %.vhd,$(ariane_pkg))
	vlog$(questa_version) $(compile_flag) -work $(library) $(filter %.sv,$(util)) $(list_incdir) -suppress 2583
	# Suppress message that always_latch may not be checked thoroughly by QuestaSim.
	vcom$(questa_version) $(compile_flag_vhd) -work $(library) -pedanticerrors $(filter %.vhd,$(uart_src))
	# vcom$(questa_version) $(compile_flag_vhd) -work $(library) -pedanticerrors $(filter %.vhd,$(src))
	vlog$(questa_version) $(compile_flag) -work $(library) -pedanticerrors $(filter %.sv,$(src)) $(list_incdir) -suppress 2583
	touch $(library)/.build-srcs

# build TBs
$(library)/.build-tb: $(dpi)
	# Compile top level
	vlog$(questa_version) $(compile_flag) -sv $(tbs) -work $(library)
	touch $(library)/.build-tb

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

sim: build
	vsim${questa_version} +permissive $(questa-flags) $(questa-cmd) -lib $(library) +MAX_CYCLES=$(max_cycles) +UVM_TESTNAME=$(test_case) \
	+BASEDIR=$(riscv-test-dir) $(uvm-flags) $(QUESTASIM_FLAGS) -gblso $(SPIKE_ROOT)/lib/libfesvr.so -sv_lib $(dpi-library)/ariane_dpi  \
	${top_level}_optimized +permissive-off ++$(elf-bin) ++$(target-options) | tee sim.log


clean:
	rm -rf $(riscv-torture-dir)/output/test*
	rm -rf $(library)/ $(dpi-library)/ $(ver-library)/
	rm -f tmp/*.ucdb tmp/*.log *.wlf *vstf wlft* *.ucdb
	rm -f *log
	rm -f transcript
	rm -f uart
