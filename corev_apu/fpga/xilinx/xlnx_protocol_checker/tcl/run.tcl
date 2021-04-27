set partNumber $::env(XILINX_PART)
set boardName  $::env(XILINX_BOARD)

set ipName xlnx_protocol_checker

create_project $ipName . -force -part $partNumber
set_property board_part $boardName [current_project]

create_ip -name axi_protocol_checker -vendor xilinx.com -library ip -version 2.0 -module_name $ipName

set_property -dict [list  CONFIG.ADDR_WIDTH {64} \
                          CONFIG.DATA_WIDTH {64} \
                          CONFIG.ID_WIDTH {5} \
                          CONFIG.AWUSER_WIDTH {1} \
                          CONFIG.ARUSER_WIDTH {1} \
                          CONFIG.RUSER_WIDTH {1} \
                          CONFIG.WUSER_WIDTH {1} \
                          CONFIG.BUSER_WIDTH {1} \
                          CONFIG.MAX_AW_WAITS {1024} \
                          CONFIG.MAX_AR_WAITS {1024} \
                          CONFIG.MAX_W_WAITS {1024} \
                          CONFIG.MAX_R_WAITS {1024} \
                          CONFIG.MAX_B_WAITS {1024} \
                          CONFIG.MAX_CONTINUOUS_WTRANSFERS_WAITS {1024} \
                          CONFIG.MAX_WLAST_TO_AWVALID_WAITS {1024} \
                          CONFIG.MAX_WRITE_TO_BVALID_WAITS {1024} \
                          CONFIG.MAX_CONTINUOUS_RTRANSFERS_WAITS {1024} \
                    ] [get_ips $ipName]


generate_target {instantiation_template} [get_files ./$ipName.srcs/sources_1/ip/$ipName/$ipName.xci]
generate_target all [get_files  ./$ipName.srcs/sources_1/ip/$ipName/$ipName.xci]
create_ip_run [get_files -of_objects [get_fileset sources_1] ./$ipName.srcs/sources_1/ip/$ipName/$ipName.xci]
launch_run -jobs 8 ${ipName}_synth_1
wait_on_run ${ipName}_synth_1