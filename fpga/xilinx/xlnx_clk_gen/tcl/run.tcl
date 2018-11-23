set partNumber $::env(XILINX_PART)
set boardName  $::env(XILINX_BOARD)

set ipName xlnx_clk_gen

create_project $ipName . -part $partNumber
set_property board_part $boardName [current_project]

create_ip -name clk_wiz -vendor xilinx.com -library ip -module_name $ipName

set_property -dict [list CONFIG.PRIM_IN_FREQ {200.000} CONFIG.CLKOUT2_USED {true} CONFIG.CLKOUT3_USED {true} CONFIG.CLKOUT1_REQUESTED_OUT_FREQ {50} CONFIG.CLKOUT2_REQUESTED_OUT_FREQ {25} CONFIG.CLKIN1_JITTER_PS {50.0} CONFIG.MMCM_DIVCLK_DIVIDE {1} CONFIG.MMCM_CLKFBOUT_MULT_F {5.000} CONFIG.MMCM_CLKIN1_PERIOD {5.000} CONFIG.MMCM_CLKIN2_PERIOD {10.0} CONFIG.MMCM_CLKOUT0_DIVIDE_F {20.000} CONFIG.MMCM_CLKOUT1_DIVIDE {40} CONFIG.MMCM_CLKOUT2_DIVIDE {10} CONFIG.NUM_OUT_CLKS {3} CONFIG.CLKOUT1_JITTER {129.198} CONFIG.CLKOUT1_PHASE_ERROR {89.971} CONFIG.CLKOUT2_JITTER {148.629} CONFIG.CLKOUT2_PHASE_ERROR {89.971} CONFIG.CLKOUT3_JITTER {112.316} CONFIG.CLKOUT3_PHASE_ERROR {89.971}] [get_ips $ipName]

generate_target {instantiation_template} [get_files ./$ipName.srcs/sources_1/ip/$ipName/$ipName.xci]
generate_target all [get_files  ./$ipName.srcs/sources_1/ip/$ipName/$ipName.xci]
create_ip_run [get_files -of_objects [get_fileset sources_1] ./$ipName.srcs/sources_1/ip/$ipName/$ipName.xci]
launch_run -jobs 8 ${ipName}_synth_1
wait_on_run ${ipName}_synth_1