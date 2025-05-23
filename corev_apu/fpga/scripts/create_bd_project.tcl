set partNumber $::env(XILINX_PART)
set boardName  $::env(XILINX_BOARD)
set board  $::env(BOARD)
set add_sources  $::env(ADD_SRC)
set script_file [info script]
set origin_dir [file dirname [file normalize "$script_file/../../../"]]

set proj_dir [get_property directory [current_project]]

set obj [current_project]
set_property -name "default_lib" -value "xil_defaultlib" -objects $obj
set_property -name "enable_resource_estimation" -value "0" -objects $obj
set_property -name "enable_vhdl_2008" -value "1" -objects $obj
set_property -name "ip_cache_permissions" -value "read write" -objects $obj
set_property -name "mem.enable_memory_map_generation" -value "1" -objects $obj
set_property -name "revised_directory_structure" -value "1" -objects $obj
set_property -name "sim.ip.auto_export_scripts" -value "1" -objects $obj
set_property -name "simulator_language" -value "Mixed" -objects $obj
set_property -name "sim_compile_state" -value "1" -objects $obj
set_property -name "webtalk.activehdl_export_sim" -value "1" -objects $obj
set_property -name "webtalk.modelsim_export_sim" -value "1" -objects $obj
set_property -name "webtalk.questa_export_sim" -value "1" -objects $obj
set_property -name "webtalk.riviera_export_sim" -value "1" -objects $obj
set_property -name "webtalk.vcs_export_sim" -value "1" -objects $obj
set_property -name "webtalk.xsim_export_sim" -value "1" -objects $obj
set_property -name "xpm_libraries" -value "XPM_CDC XPM_FIFO XPM_MEMORY" -objects $obj

set nproc [auto_execok "nproc"]
set cores 8
if {[llength $nproc]} {
    if {![catch {exec $nproc "--all"} cores]} {
        if { $cores > 32 } {
            set_param general.maxThreads 32
        } else {
            set_param general.maxThreads $cores
        }
    }
}

# Create 'sources_1' fileset (if not found)
if {[string equal [get_filesets -quiet sources_1] ""]} {
  create_fileset -srcset sources_1
}

# Create 'constrs_1' fileset (if not found)
if {[string equal [get_filesets -quiet constrs_1] ""]} {
  create_fileset -constrset constrs_1
}

# Add all files
source $origin_dir/$add_sources

# Add block design interface files
set obj [get_filesets sources_1]
set cstr [get_filesets constrs_1]

remove_files -fileset $obj "*ariane_xilinx.sv"

add_files -fileset $obj -verbose [file normalize "$origin_dir/core/cache_subsystem/hpdcache/rtl/include/hpdcache_typedef.svh"]
add_files -fileset $obj -verbose [file normalize "$origin_dir/core/cvfpu/src/common_cells/include/common_cells/registers.svh"]
add_files -fileset $obj -verbose [file normalize "$origin_dir/core/include/cvxif_types.svh"]
add_files -fileset $obj -verbose [file normalize "$origin_dir/core/include/rvfi_types.svh"]
add_files -fileset $obj -verbose [file normalize "$origin_dir/corev_apu/fpga/src/$board.svh"]
add_files -fileset $obj -verbose [file normalize "$origin_dir/corev_apu/fpga/src/verilog_wrappers/block_design_wrappers/ariane_xlnx_mapper.svh"]
add_files -fileset $obj -verbose [file normalize "$origin_dir/corev_apu/register_interface/include/register_interface/assign.svh"]
add_files -fileset $obj -verbose [file normalize "$origin_dir/corev_apu/register_interface/include/register_interface/typedef.svh"]
add_files -fileset $obj -verbose [file normalize "$origin_dir/corev_apu/riscv-dbg/debug_rom/debug_rom_one_scratch.sv"]
add_files -fileset $obj -verbose [file normalize "$origin_dir/vendor/pulp-platform/axi/include/axi/assign.svh"]
add_files -fileset $obj -verbose [file normalize "$origin_dir/vendor/pulp-platform/axi/include/axi/typedef.svh"]
add_files -fileset $obj -verbose [file normalize "$origin_dir/vendor/pulp-platform/axi/src/axi_burst_splitter.sv"]
add_files -fileset $obj -verbose [file normalize "$origin_dir/vendor/pulp-platform/axi/src/axi_pkg.sv"]
add_files -fileset $obj -verbose [file normalize "$origin_dir/vendor/pulp-platform/common_cells/include/common_cells/registers.svh"]
add_files -fileset $obj -verbose [file normalize "$origin_dir/vendor/pulp-platform/common_cells/src/fall_through_register.sv"]
add_files -fileset $obj -verbose [file normalize "$origin_dir/vendor/pulp-platform/common_cells/src/id_queue.sv"]
add_files -fileset $obj -verbose [file normalize "$origin_dir/vendor/pulp-platform/common_cells/src/onehot_to_bin.sv"]

set file_obj [get_files -of_objects $obj [list \
    "$origin_dir/corev_apu/fpga/src/$board.svh" \
    "$origin_dir/core/cvfpu/src/common_cells/include/common_cells/registers.svh" \
    "$origin_dir/vendor/pulp-platform/common_cells/include/common_cells/registers.svh" \
    "$origin_dir/corev_apu/register_interface/include/register_interface/assign.svh" \
    "$origin_dir/vendor/pulp-platform/axi/include/axi/assign.svh" \
    "$origin_dir/corev_apu/register_interface/include/register_interface/typedef.svh" \
    "$origin_dir/vendor/pulp-platform/axi/include/axi/typedef.svh" \
    "$origin_dir/core/include/cvxif_types.svh" \
    "$origin_dir/core/include/rvfi_types.svh" \
    "$origin_dir/core/cache_subsystem/hpdcache/rtl/include/hpdcache_typedef.svh" \
    "$origin_dir/corev_apu/fpga/src/verilog_wrappers/block_design_wrappers/ariane_xlnx_mapper.svh" \
]]
set_property -dict { file_type {SystemVerilog} is_global_include 1} -objects $file_obj

add_files -fileset $obj -scan_for_includes -verbose [file normalize "$origin_dir/corev_apu/fpga/src/verilog_wrappers/ariane"]
add_files -fileset $obj -scan_for_includes -verbose [file normalize "$origin_dir/corev_apu/fpga/src/verilog_wrappers/block_design_wrappers"]
add_files -fileset $obj -scan_for_includes -verbose [file normalize "$origin_dir/corev_apu/fpga/src/verilog_wrappers/utils"]

set_property file_type SystemVerilog [get_files *.svh]

# Actually create the block design
source $origin_dir/corev_apu/fpga/scripts/block_designs/$board.tcl

# Wrapper needs to be SystemVerilog not to conflict with global (SV) includes
# and be called "ariane_xilinx"
make_wrapper -files [get_files SoC.bd] -top
exec mv "$origin_dir/corev_apu/fpga/ariane.gen/sources_1/bd/SoC/hdl/SoC_wrapper.v" "$origin_dir/corev_apu/fpga/ariane.gen/sources_1/bd/SoC/hdl/ariane_xilinx.v"
exec sed -i "s/SoC_wrapper/ariane_xilinx/g" "$origin_dir/corev_apu/fpga/ariane.gen/sources_1/bd/SoC/hdl/ariane_xilinx.v"
add_files -norecurse "$origin_dir/corev_apu/fpga/ariane.gen/sources_1/bd/SoC/hdl/ariane_xilinx.v"
set_property FILE_TYPE SystemVerilog [get_files -all ariane_xilinx.v]
set_property top ariane_xilinx [current_fileset]

set_property include_dirs { \
    "src/axi_sd_bridge/include" \
    "../../vendor/pulp-platform/common_cells/include" \
    "../../vendor/pulp-platform/axi/include" \
    "../../core/cache_subsystem/hpdcache/rtl/include" \
    "../register_interface/include" \
    "../../core/include" \
    "src/verilog_wrappers/block_design_wrappers/" \
} [current_fileset]

set_property source_mgmt_mode All [current_project]
update_compile_order -fileset sources_1

set_property STEPS.SYNTH_DESIGN.ARGS.RETIMING true [get_runs synth_1]

open_bd_design { "$origin_dir/corev_apu/fpga/ariane.srcs/sources_1/bd/SoC/SoC.bd" }

generate_target all [get_files "$origin_dir/corev_apu/fpga/ariane.srcs/sources_1/bd/SoC/SoC.bd"]

save_bd_design
close_bd_design SoC

add_files -fileset $cstr -norecurse [file normalize "$origin_dir/corev_apu/fpga/constraints/$board.xdc"]

# Run OOC module synthesis
generate_target all [get_files  "$origin_dir/corev_apu/fpga/ariane.srcs/sources_1/bd/SoC/SoC.bd"]
export_ip_user_files -of_objects [get_files "$origin_dir/corev_apu/fpga/ariane.srcs/sources_1/bd/SoC/SoC.bd"] -no_script -sync -force
create_ip_run [get_files -of_objects [get_fileset sources_1] "$origin_dir/corev_apu/fpga/ariane.srcs/sources_1/bd/SoC/SoC.bd"]
launch_runs [get_runs "*_synth_1"] -jobs $cores
wait_on_runs [get_runs "*_synth_1"]

# Launch synthesis
launch_runs synth_1 -jobs $cores
wait_on_run synth_1
open_run synth_1

# Set for RuntimeOptimized implementation
set_property "steps.place_design.args.directive" "RuntimeOptimized" [get_runs impl_1]
set_property "steps.route_design.args.directive" "RuntimeOptimized" [get_runs impl_1]

launch_runs impl_1
wait_on_run impl_1
launch_runs impl_1 -to_step write_bitstream
wait_on_run impl_1
open_run impl_1

# Output Verilog netlist + SDC for timing simulation
write_verilog -force -mode funcsim work-fpga/${project}_funcsim.v
write_verilog -force -mode timesim work-fpga/${project}_timesim.v
write_sdf     -force work-fpga/${project}_timesim.sdf

# Write reports
exec mkdir -p reports/
exec rm -rf reports/*

check_timing -verbose                                                   -file reports/$project.check_timing.rpt
report_timing -max_paths 100 -nworst 100 -delay_type max -sort_by slack -file reports/$project.timing_WORST_100.rpt
report_timing -nworst 1 -delay_type max -sort_by group                  -file reports/$project.timing.rpt
report_utilization -hierarchical                                        -file reports/$project.utilization.rpt
report_cdc                                                              -file reports/$project.cdc.rpt
report_clock_interaction                                                -file reports/$project.clock_interaction.rpt
