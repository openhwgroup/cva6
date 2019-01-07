set partNumber $::env(XILINX_PART)
set boardName  $::env(XILINX_BOARD)

set ipName xlnx_axi_quad_spi

create_project $ipName . -part $partNumber
set_property board_part $boardName [current_project]

create_ip -name axi_quad_spi -vendor xilinx.com -library ip -module_name $ipName
set_property -dict [list CONFIG.C_USE_STARTUP {0} CONFIG.C_SCK_RATIO {4} CONFIG.C_FIFO_DEPTH {256} CONFIG.C_TYPE_OF_AXI4_INTERFACE {1} CONFIG.C_S_AXI4_ID_WIDTH {0}] [get_ips $ipName]

generate_target {instantiation_template} [get_files ./$ipName.srcs/sources_1/ip/$ipName/$ipName.xci]
generate_target all [get_files  ./$ipName.srcs/sources_1/ip/$ipName/$ipName.xci]
create_ip_run [get_files -of_objects [get_fileset sources_1] ./$ipName.srcs/sources_1/ip/$ipName/$ipName.xci]
launch_run -jobs 8 ${ipName}_synth_1
wait_on_run ${ipName}_synth_1