set partNumber $::env(XILINX_PART)
set boardName  $::env(XILINX_BOARD)

if [info exists ::env(BOARD)] {
    set BOARD $::env(BOARD)
} else {
    error "BOARD is not defined. Please source the sourceme.sh file."
    exit
}
if [info exists ::env(XILINX_BOARD)] {
	set boardName  $::env(XILINX_BOARD)
}

# detect target clock
if [info exists ::env(FC_CLK_PERIOD_NS)] {
    set FC_CLK_PERIOD_NS $::env(FC_CLK_PERIOD_NS)
} else {
    set FC_CLK_PERIOD_NS 100.000
}
if [info exists ::env(CL_CLK_PERIOD_NS)] {
    set CL_CLK_PERIOD_NS $::env(CL_CLK_PERIOD_NS)
} else {
    set CL_CLK_PERIOD_NS 100.000
}
if [info exists ::env(PER_CLK_PERIOD_NS)] {
    set PER_CLK_PERIOD_NS $::env(PER_CLK_PERIOD_NS)
} else {
    set PER_CLK_PERIOD_NS 100.000
}


set FC_CLK_FREQ_MHZ [expr 1000 / $FC_CLK_PERIOD_NS]
set PER_CLK_FREQ_MHZ [expr 1000 / $PER_CLK_PERIOD_NS]
set CL_CLK_FREQ_MHZ  [expr 1000 / $CL_CLK_PERIOD_NS]

set ipName xilinx_clk_mngr

create_project $ipName . -part $partNumber
set_property board_part $boardName [current_project]

create_ip -name clk_wiz -vendor xilinx.com -library ip -module_name $ipName

#CONFIG.CLKOUT3_USED {true}      
#CONFIG.CLKOUT3_REQUESTED_OUT_FREQ {$CL_CLK_FREQ_MHZ} \                                           

set_property -dict [eval list CONFIG.PRIM_IN_FREQ {125.000} \
                        CONFIG.NUM_OUT_CLKS {2} \
                        CONFIG.CLKOUT2_USED {true} \
                        CONFIG.RESET_TYPE {ACTIVE_LOW} \
                        CONFIG.RESET_PORT {resetn} \
                        CONFIG.CLKOUT1_REQUESTED_OUT_FREQ {$FC_CLK_FREQ_MHZ} \
                        CONFIG.CLKOUT2_REQUESTED_OUT_FREQ {$PER_CLK_FREQ_MHZ} \
                        CONFIG.CLKIN1_JITTER_PS {50.0} \
                       ] [get_ips $ipName]

generate_target all [get_files  ./$ipName.srcs/sources_1/ip/$ipName/$ipName.xci]
create_ip_run [get_files -of_objects [get_fileset sources_1] ./$ipName.srcs/sources_1/ip/$ipName/$ipName.xci]
launch_run -jobs 12 ${ipName}_synth_1
wait_on_run ${ipName}_synth_1
