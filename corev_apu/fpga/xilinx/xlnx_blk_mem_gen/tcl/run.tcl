set partNumber $::env(XILINX_PART)
set boardName  $::env(XILINX_BOARD)

set ipName xlnx_blk_mem_gen

create_project $ipName . -force -part $partNumber
set_property board_part $boardName [current_project]

create_ip -name blk_mem_gen -vendor xilinx.com -library ip -module_name $ipName


#if {$::env(FPGA)} {
   set_property -dict [list CONFIG.AXI_ID_Width {5} \
                         CONFIG.Assume_Synchronous_Clk {true} \
                         CONFIG.Byte_Size {8} \
                         CONFIG.EN_SAFETY_CKT {true} \
                         CONFIG.Enable_B {Use_ENB_Pin} \
                         CONFIG.Interface_Type {AXI4} \
                         CONFIG.Memory_Type {Simple_Dual_Port_RAM} \
                         CONFIG.Operating_Mode_A {READ_FIRST} \
                         CONFIG.Operating_Mode_B {READ_FIRST} \
                         CONFIG.Port_B_Clock {100} \
                         CONFIG.Port_B_Enable_Rate {100} \
                         CONFIG.Read_Width_A {64} \
                         CONFIG.Read_Width_B {64} \
                         CONFIG.Register_PortA_Output_of_Memory_Primitives {false} \
                         CONFIG.Reset_Type {ASYNC} \
                         CONFIG.Use_AXI_ID {true} \
                         CONFIG.Use_Byte_Write_Enable {true} \
                         CONFIG.Use_RSTB_Pin {true} \
                         CONFIG.Write_Depth_A {24576} \
                         CONFIG.Write_Width_A {64} \
                         CONFIG.Write_Width_B {64}] [get_ips $ipName]
   
#} else {
#    set appName    ../../../../$::env(APP).coe
#    puts $appName
#    set_property -dict [list CONFIG.AXI_ID_Width {5} \
#                         CONFIG.Assume_Synchronous_Clk {true} \
#                         CONFIG.Byte_Size {8} \
#                         CONFIG.EN_SAFETY_CKT {true} \
#                         CONFIG.Enable_B {Use_ENB_Pin} \
#                         CONFIG.Interface_Type {AXI4} \
#                         CONFIG.Memory_Type {Simple_Dual_Port_RAM} \
#                         CONFIG.Operating_Mode_A {READ_FIRST} \
#                         CONFIG.Operating_Mode_B {READ_FIRST} \
#                         CONFIG.Port_B_Clock {100} \
#                         CONFIG.Port_B_Enable_Rate {100} \
#                         CONFIG.Read_Width_A {64} \
#                         CONFIG.Read_Width_B {64} \
#                         CONFIG.Register_PortA_Output_of_Memory_Primitives {false} \
#                         CONFIG.Reset_Type {ASYNC} \
#                         CONFIG.Use_AXI_ID {true} \
#                         CONFIG.Use_Byte_Write_Enable {true} \
#                         CONFIG.Use_RSTB_Pin {true} \
#                         CONFIG.Write_Depth_A {24576} \
#                         CONFIG.Write_Width_A {64} \
3                         CONFIG.Write_Width_B {64} \
#                         CONFIG.Load_Init_File {true} \
3                         CONFIG.Coe_File $appName] [get_ips $ipName]
#}
#CONFIG.Coe_File {../../../../$appName}] [get_ips $ipName]
#CONFIG.Coe_File {../../../../mnist.coe}] [get_ips $ipName]
generate_target {instantiation_template} [get_files ./$ipName.srcs/sources_1/ip/$ipName/$ipName.xci]
generate_target all [get_files  ./$ipName.srcs/sources_1/ip/$ipName/$ipName.xci]
create_ip_run [get_files -of_objects [get_fileset sources_1] ./$ipName.srcs/sources_1/ip/$ipName/$ipName.xci]
launch_run -jobs 8 ${ipName}_synth_1
wait_on_run ${ipName}_synth_1
