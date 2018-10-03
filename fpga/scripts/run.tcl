set outputDir work-fpga
file mkdir $outputDir

# Read sources

source scripts/add_sources.tcl

read_xdc constraints/ariane.xdc
read_xdc constraints/genesys-2.xdc

read_ip ariane.srcs/sources_1/ip/axi_clock_converter_0/axi_clock_converter_0.xci
read_ip ariane.srcs/sources_1/ip/axi_dwidth_converter_0/axi_dwidth_converter_0.xci
read_ip ariane.srcs/sources_1/ip/axi_protocol_checker_0/axi_protocol_checker_0.xci
read_ip ariane.srcs/sources_1/ip/axi_protocol_converter_0/axi_protocol_converter_0.xci
read_ip ariane.srcs/sources_1/ip/axi_uartlite_1/axi_uartlite_1.xci
read_ip ariane.srcs/sources_1/ip/clk_wiz_0/clk_wiz_0.xci
read_ip ariane.srcs/sources_1/ip/mig_7series_0/mig_7series_0.xci

# Synthesis

synth_design -top ariane_xilinx -part xc7k325tffg900-2 -flatten rebuilt -verilog_define FPGA_TARGET_XILINX=1
write_checkpoint -force $outputDir/post_synth
report_timing_summary -file $outputDir/post_synth_timing_summary.rpt
report_power -file $outputDir/post_synth_power.rpt

# Implementation

opt_design
power_opt_design
place_design
phys_opt_design
write_checkpoint -force $outputDir/post_place
report_timing_summary -file $outputDir/post_place_timing_summary.rpt

route_design
write_checkpoint -force $outputDir/post_route

report_timing_summary -file $outputDir/post_route_timing_summary.rpt
report_timing -sort_by group -max_paths 100 -path_type summary -file $outputDir/post_route_timing.rpt
report_clock_utilization -file $outputDir/clock_util.rpt
report_utilization -file $outputDir/post_route_util.rpt
report_power -file $outputDir/post_route_power.rpt
report_drc -file $outputDir/post_imp_drc.rpt

write_verilog -force $outputDir/ariane.v
# write_xdc -no_fixed_only -force $outputDir/bft_impl.xdc

write_bitstream -force $outputDir/ariane.bit
