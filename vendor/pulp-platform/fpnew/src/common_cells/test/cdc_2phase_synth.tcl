set TIME_NS 1000

analyze -format sv $ROOT/src/cdc_2phase.sv
analyze -format sv $ROOT/test/cdc_2phase_synth.sv
elaborate cdc_2phase_synth

create_clock -name src_clk -period [expr 1 * $TIME_NS]  [get_ports src_clk_i]
create_clock -name dst_clk -period [expr 1 * $TIME_NS]  [get_ports dst_clk_i]

set_ideal_network [get_ports {src_clk_i src_rst_ni dst_clk_i dst_rst_ni}]
set_input_delay [expr 0.5 * $TIME_NS] -clock src_clk [remove_from_collection [get_ports src_*i] {src_clk_i src_rst_ni}]
set_input_delay [expr 0.5 * $TIME_NS] -clock dst_clk [remove_from_collection [get_ports dst_*i] {dst_clk_i dst_rst_ni}]
set_output_delay [expr 0.5 * $TIME_NS] -clock src_clk [get_ports src_*o]
set_output_delay [expr 0.5 * $TIME_NS] -clock dst_clk [get_ports dst_*o]

set_max_delay -from [get_pins -hierarchical async_*_o] -to [get_pins -hierarchical async_*_i] [expr 1 * $TIME_NS]

compile_ultra -gate_clock

change_names -hierarchy -rules verilog
report_clock_gating > cdc_2phase_ckg.rpt
report_timing > cdc_2phase_timing.rpt
report_timing -from [get_nets -hierarchical async*_o] -to [get_nets -hierarchical async*_i] > cdc_2phase_falsepaths.rpt
report_area > cdc_2phase_area.rpt
write -hierarchy -format verilog -output cdc_2phase_synth.v
write -hierarchy -format ddc -output cdc_2phase_synth.ddc
