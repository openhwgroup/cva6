set partNumber $::env(XILINX_PART)
set boardName  $::env(XILINX_BOARD)

create_project xilinx_rom_bank_1024x64 . -part $partNumber
set_property board_part $boardName [current_project]
create_ip -name blk_mem_gen -vendor xilinx.com -library ip -module_name xilinx_rom_bank_1024x64
set_property -dict [list CONFIG.Memory_Type {Single_Port_RAM} CONFIG.Use_Byte_Write_Enable {true} CONFIG.Byte_Size {8} CONFIG.Write_Width_A {64} CONFIG.Write_Depth_A {1024} CONFIG.Register_PortA_Output_of_Memory_Primitives {false} CONFIG.Use_RSTA_Pin {true} ] [get_ips xilinx_rom_bank_1024x64]
exec cp boot_code.coe xilinx_rom_bank_1024x64.srcs/sources_1/ip/boot_code.coe
set_property -dict [list CONFIG.Load_Init_File {true} CONFIG.Coe_File {../boot_code.coe} CONFIG.Fill_Remaining_Memory_Locations {true}] [get_ips xilinx_rom_bank_1024x64]
generate_target all [get_files ./xilinx_rom_bank_1024x64.srcs/sources_1/ip/xilinx_rom_bank_1024x64/xilinx_rom_bank_1024x64.xci]
create_ip_run [get_files -of_objects [get_fileset sources_1] ./xilinx_rom_bank_1024x64.srcs/sources_1/ip/xilinx_rom_bank_1024x64/xilinx_rom_bank_1024x64.xci]
launch_run -jobs 8 xilinx_rom_bank_1024x64_synth_1
wait_on_run xilinx_rom_bank_1024x64_synth_1
