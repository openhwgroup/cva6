set partNumber $::env(XILINX_PART)
set boardName  $::env(XILINX_BOARD)

set ipName xlnx_ila

create_project $ipName . -force -part $partNumber
set_property board_part $boardName [current_project]

create_ip -name ila -vendor xilinx.com -library ip -module_name $ipName
# probe 1 pll_locked
# probe 2 ndmreset_n
# probe 3 irq_i
# probe 4 ipi
# probe 5 timer_irq
# probe 6 debug_req
# probe7 araddr
# probe8 arvalid
# probe9 arready
# probe10 awaddr
# probe11 awvalid
# probe12 awready
# probe 13 wdata
# probe 14 wvalid
# probe 15 wready
# probe 16 rdata
# probe 17 rresp
# probe 18 rvalid
# probe 19 bvalid
# probe 20 bresp

set_property -dict [list  CONFIG.C_NUM_OF_PROBES {20} \
                          CONFIG.C_PROBE0_WIDTH {1} \
                          CONFIG.C_PROBE1_WIDTH {1} \
                          CONFIG.C_PROBE2_WIDTH {2} \
                          CONFIG.C_PROBE3_WIDTH {1} \
                          CONFIG.C_PROBE4_WIDTH {1} \
                          CONFIG.C_PROBE5_WIDTH {1} \
                          CONFIG.C_PROBE6_WIDTH {64} \
                          CONFIG.C_PROBE7_WIDTH {1} \
                          CONFIG.C_PROBE8_WIDTH {1} \
                          CONFIG.C_PROBE9_WIDTH {64} \
                          CONFIG.C_PROBE10_WIDTH {1} \
                          CONFIG.C_PROBE11_WIDTH {1} \
                          CONFIG.C_PROBE12_WIDTH {64} \
                          CONFIG.C_PROBE13_WIDTH {1} \
                          CONFIG.C_PROBE14_WIDTH {1} \
                          CONFIG.C_PROBE15_WIDTH {64} \
                          CONFIG.C_PROBE16_WIDTH {2} \
                          CONFIG.C_PROBE17_WIDTH {1} \
                          CONFIG.C_PROBE18_WIDTH {1} \
                          CONFIG.C_PROBE19_WIDTH {2} \
                          CONFIG.C_DATA_DEPTH {4096}  \
                          CONFIG.C_INPUT_PIPE_STAGES {1} \
                    ] [get_ips $ipName]


generate_target {instantiation_template} [get_files ./$ipName.srcs/sources_1/ip/$ipName/$ipName.xci]
generate_target all [get_files  ./$ipName.srcs/sources_1/ip/$ipName/$ipName.xci]
create_ip_run [get_files -of_objects [get_fileset sources_1] ./$ipName.srcs/sources_1/ip/$ipName/$ipName.xci]
launch_run -jobs 8 ${ipName}_synth_1
wait_on_run ${ipName}_synth_1