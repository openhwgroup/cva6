# Xilinx Vivado script
# Version: Vivado 2015.4
# Function:
#   Generate a vivado project for the lowRISC SoC

set mem_data_width {64}
set io_data_width {32}
set axi_id_width {8}

set origin_dir "."
set base_dir "src"

set project_name "ariane_top"
set CONFIG "default"

# Set the directory path for the original project from where this script was exported
set orig_proj_dir [file normalize $origin_dir/$project_name]

# Create project
create_project $project_name $origin_dir/$project_name

# Set the directory path for the new project
set proj_dir [get_property directory [current_project]]

# Set project properties
set obj [get_projects $project_name]
set_property "default_lib" "xil_defaultlib" $obj
set_property "part" "xc7a100tcsg324-1" $obj
set_property "simulator_language" "Mixed" $obj

# Create 'sources_1' fileset (if not found)
if {[string equal [get_filesets -quiet sources_1] ""]} {
  create_fileset -srcset sources_1
}

# Set 'sources_1' fileset object
set files [list \
               [file normalize $origin_dir/include/ariane_pkg.sv] \
               [file normalize $origin_dir/include/nbdcache_pkg.sv] \
               [file normalize $origin_dir/src/axi_if/axi_if.sv] \
               [file normalize $origin_dir/src/axi_mem_if/axi2mem.sv] \
               [file normalize $origin_dir/src/ariane.sv] \
               [file normalize $origin_dir/src/ariane_wrapped.sv] \
               [file normalize $origin_dir/src/alu.sv] \
               [file normalize $origin_dir/src/branch_unit.sv] \
               [file normalize $origin_dir/src/btb.sv] \
               [file normalize $origin_dir/src/commit_stage.sv] \
               [file normalize $origin_dir/src/compressed_decoder.sv] \
               [file normalize $origin_dir/src/controller.sv] \
               [file normalize $origin_dir/src/csr_buffer.sv] \
               [file normalize $origin_dir/src/csr_regfile.sv] \
               [file normalize $origin_dir/src/decoder.sv] \
               [file normalize $origin_dir/src/ex_stage.sv] \
               [file normalize $origin_dir/src/fetch_fifo.sv] \
               [file normalize $origin_dir/src/fifo.sv] \
               [file normalize $origin_dir/src/id_stage.sv] \
               [file normalize $origin_dir/src/if_stage.sv] \
               [file normalize $origin_dir/src/instr_realigner.sv] \
               [file normalize $origin_dir/src/issue_read_operands.sv] \
               [file normalize $origin_dir/src/issue_stage.sv] \
               [file normalize $origin_dir/src/load_unit.sv] \
               [file normalize $origin_dir/src/lsu.sv] \
               [file normalize $origin_dir/src/lsu_arbiter.sv] \
               [file normalize $origin_dir/src/mmu.sv] \
               [file normalize $origin_dir/src/mult.sv] \
               [file normalize $origin_dir/src/pcgen_stage.sv] \
               [file normalize $origin_dir/src/ptw.sv] \
               [file normalize $origin_dir/src/scoreboard.sv] \
               [file normalize $origin_dir/src/store_buffer.sv] \
               [file normalize $origin_dir/src/store_unit.sv] \
               [file normalize $origin_dir/src/tlb.sv] \
               [file normalize $origin_dir/src/debug_unit.sv] \
               [file normalize $origin_dir/src/nbdcache.sv] \
               [file normalize $origin_dir/src/miss_handler.sv] \
               [file normalize $origin_dir/src/cache_ctrl.sv] \
               [file normalize $origin_dir/src/perf_counters.sv] \
               [file normalize $origin_dir/src/regfile_ff.sv] \
               [file normalize $origin_dir/src/util/xilinx_sram.sv] \
               [file normalize $origin_dir/src/lfsr.sv] \
               [file normalize $origin_dir/src/icache.sv] \
             ]
add_files -norecurse -fileset [get_filesets sources_1] $files

# add include path
set_property include_dirs [list \
                               [file normalize $base_dir/include] \
                              ] [get_filesets sources_1]

set_property verilog_define [list FPGA FPGA_FULL NEXYS4] [get_filesets sources_1]

# Set 'sources_1' fileset properties
set_property "top" "chip_top" [get_filesets sources_1]

# Program/data RAM
create_ip -name blk_mem_gen -vendor xilinx.com -library ip -version 8.3 -module_name instr_ram
set_property -dict [list \
                        CONFIG.Memory_Type {True_Dual_Port_RAM} \
                        CONFIG.Use_Byte_Write_Enable {true} \
                        CONFIG.Byte_Size {8} \
                        CONFIG.Write_Width_A {64} \
                        CONFIG.Write_Depth_A {16384} \
                        CONFIG.Operating_Mode_A {READ_FIRST} \
                        CONFIG.Register_PortA_Output_of_Memory_Primitives {false} \
                        CONFIG.Register_PortB_Output_of_Memory_Primitives {false} \
                        CONFIG.Read_Width_A {64} \
                        CONFIG.Write_Width_B {64} \
                        CONFIG.Read_Width_B {64} \
                        CONFIG.Enable_B {Use_ENB_Pin} \
                        CONFIG.Port_B_Clock {100} \
                        CONFIG.Port_B_Write_Rate {50} \
                        CONFIG.Port_B_Enable_Rate {100}] [get_ips instr_ram]

create_ip -name blk_mem_gen -vendor xilinx.com -library ip -version 8.3 -module_name data_ram
set_property -dict [list \
                        CONFIG.Memory_Type {True_Dual_Port_RAM} \
                        CONFIG.Use_Byte_Write_Enable {true} \
                        CONFIG.Byte_Size {8} \
                        CONFIG.Write_Width_A {64} \
                        CONFIG.Write_Depth_A {16384} \
                        CONFIG.Operating_Mode_A {READ_FIRST} \
                        CONFIG.Register_PortA_Output_of_Memory_Primitives {false} \
                        CONFIG.Register_PortB_Output_of_Memory_Primitives {false} \
                        CONFIG.Read_Width_A {64} \
                        CONFIG.Write_Width_B {64} \
                        CONFIG.Read_Width_B {64} \
                        CONFIG.Enable_B {Use_ENB_Pin} \
                        CONFIG.Port_B_Clock {100} \
                        CONFIG.Port_B_Write_Rate {50} \
                        CONFIG.Port_B_Enable_Rate {100}] [get_ips data_ram]

# Cache RAMs
create_ip -name blk_mem_gen -vendor xilinx.com -library ip -module_name xilinx_dcache_bank_data_256x128
set_property -dict [list \
                        CONFIG.Use_Byte_Write_Enable {true} \
                        CONFIG.Byte_Size {8} \
                        CONFIG.Write_Width_A {128} \
                        CONFIG.Read_Width_A {128} \
                        CONFIG.Write_Width_B {128} \
                        CONFIG.Read_Width_B {128} \
                        CONFIG.Write_Depth_A {256} \
                        CONFIG.Register_PortA_Output_of_Memory_Primitives {false} ] \
    [get_ips xilinx_dcache_bank_data_256x128]

create_ip -name blk_mem_gen -vendor xilinx.com -library ip -module_name xilinx_dcache_bank_tag_256x46
set_property -dict [list \
                        CONFIG.Use_Byte_Write_Enable {true} \
                        CONFIG.Byte_Size {8} \
                        CONFIG.Write_Width_A {48} \
                        CONFIG.Read_Width_A {48} \
                        CONFIG.Write_Width_B {48} \
                        CONFIG.Read_Width_B {48} \
                        CONFIG.Write_Depth_A {256} \
                        CONFIG.Register_PortA_Output_of_Memory_Primitives {false} ] \
    [get_ips xilinx_dcache_bank_tag_256x46]

#UART
create_ip -name axi_uart16550 -vendor xilinx.com -library ip -module_name axi_uart16550_0
set_property -dict [list \
                        CONFIG.UART_BOARD_INTERFACE {Custom} \
                        CONFIG.C_S_AXI_ACLK_FREQ_HZ_d {25} \
                       ] [get_ips axi_uart16550_0]
generate_target {instantiation_template} \
    [get_files $proj_dir/$project_name.srcs/sources_1/ip/axi_uart16550_0/axi_uart16550_0.xci]

#BRAM Controller
create_ip -name axi_bram_ctrl -vendor xilinx.com -library ip -module_name axi_bram_ctrl_0
set_property -dict [list \
                        CONFIG.DATA_WIDTH $io_data_width \
                        CONFIG.ID_WIDTH $axi_id_width \
                        CONFIG.MEM_DEPTH {16384} \
                        CONFIG.PROTOCOL {AXI4} \
                        CONFIG.BMG_INSTANCE {EXTERNAL} \
                        CONFIG.SINGLE_PORT_BRAM {1} \
                        CONFIG.SUPPORTS_NARROW_BURST {1} \
                       ] [get_ips axi_bram_ctrl_0]
generate_target {instantiation_template} \
    [get_files $proj_dir/$project_name.srcs/sources_1/ip/axi_bram_ctrl_0/axi_bram_ctrl_0.xci]

#ETH RAM Controller
create_ip -name axi_bram_ctrl -vendor xilinx.com -library ip -module_name axi_bram_ctrl_1
set_property -dict [list \
                        CONFIG.DATA_WIDTH $io_data_width \
                        CONFIG.ID_WIDTH $axi_id_width \
                        CONFIG.MEM_DEPTH {8192} \
                        CONFIG.PROTOCOL {AXI4} \
                        CONFIG.BMG_INSTANCE {EXTERNAL} \
                        CONFIG.SINGLE_PORT_BRAM {1} \
                        CONFIG.SUPPORTS_NARROW_BURST {0} \
                       ] [get_ips axi_bram_ctrl_1]
generate_target {instantiation_template} \
    [get_files $proj_dir/$project_name.srcs/sources_1/ip/axi_bram_ctrl_1/axi_bram_ctrl_1.xci]

#HID RAM Controller
create_ip -name axi_bram_ctrl -vendor xilinx.com -library ip -module_name axi_bram_ctrl_2
set_property -dict [list \
                        CONFIG.DATA_WIDTH $io_data_width \
                        CONFIG.MEM_DEPTH {32768} \
                        CONFIG.PROTOCOL {AXI4LITE} \
                        CONFIG.BMG_INSTANCE {EXTERNAL} \
                        CONFIG.SINGLE_PORT_BRAM {1} \
                        CONFIG.SUPPORTS_NARROW_BURST {1} \
                       ] [get_ips axi_bram_ctrl_2]
generate_target {instantiation_template} \
    [get_files $proj_dir/$project_name.srcs/sources_1/ip/axi_bram_ctrl_2/axi_bram_ctrl_2.xci]

#Dummy Memory Controller (for simulation)
create_ip -name axi_bram_ctrl -vendor xilinx.com -library ip -module_name axi_bram_ctrl_3
set_property -dict [list \
                        CONFIG.DATA_WIDTH $mem_data_width \
                        CONFIG.ID_WIDTH $axi_id_width \
                        CONFIG.SINGLE_PORT_BRAM {1} \
                        CONFIG.BMG_INSTANCE {EXTERNAL} \
                        CONFIG.MEM_DEPTH {65536} \
                        CONFIG.ECC_TYPE {0} \
                       ] [get_ips axi_bram_ctrl_3]
generate_target {instantiation_template} \
    [get_files $proj_dir/$project_name.srcs/sources_1/ip/axi_bram_ctrl_3/axi_bram_ctrl_3.xci]

# Ethernet packet receive buffer
create_ip -name blk_mem_gen -vendor xilinx.com -library ip -module_name blk_mem_gen_0
set_property -dict [list \
			CONFIG.Memory_Type {True_Dual_Port_RAM} \
			CONFIG.Write_Width_A {8} \
			CONFIG.Write_Depth_A {16384} \
			CONFIG.Write_Width_B {32} \
			CONFIG.Register_PortA_Output_of_Memory_Primitives {false} \
			CONFIG.Register_PortB_Output_of_Memory_Primitives {false} \
			CONFIG.Read_Width_A {8} \
			CONFIG.Read_Width_B {32} \
			CONFIG.Enable_B {Use_ENB_Pin} \
			CONFIG.Port_B_Clock {100} \
			CONFIG.Port_B_Write_Rate {50} \
			CONFIG.Port_B_Enable_Rate {100}
		   ] [get_ips blk_mem_gen_0]
generate_target {instantiation_template} \
    [get_files $proj_dir/$project_name.srcs/sources_1/ip/blk_mem_gen_0/blk_mem_gen_0.xci]

# Memory Controller
create_ip -name mig_7series -vendor xilinx.com -library ip -module_name mig_7series_0
set_property CONFIG.XML_INPUT_FILE [file normalize script/mig_config.prj] [get_ips mig_7series_0]
generate_target {instantiation_template} \
    [get_files $proj_dir/$project_name.srcs/sources_1/ip/mig_7series_0/mig_7series_0.xci]

# AXI clock converter due to the clock difference
create_ip -name axi_clock_converter -vendor xilinx.com -library ip -version 2.1 -module_name axi_clock_converter_0
set_property -dict [list \
                        CONFIG.ADDR_WIDTH {30} \
                        CONFIG.DATA_WIDTH $mem_data_width \
                        CONFIG.ID_WIDTH $axi_id_width \
                        CONFIG.ACLK_ASYNC {0} \
                        CONFIG.ACLK_RATIO {1:2}] \
    [get_ips axi_clock_converter_0]
generate_target {instantiation_template} [get_files $proj_dir/$project_name.srcs/sources_1/ip/axi_clock_converter_0/axi_clock_converter_0.xci]

# Clock generators
create_ip -name clk_wiz -vendor xilinx.com -library ip -module_name clk_wiz_0
set_property -dict [list \
                        CONFIG.PRIMITIVE {PLL} \
                        CONFIG.CLKOUT1_REQUESTED_OUT_FREQ {200.000} \
                        CONFIG.RESET_TYPE {ACTIVE_LOW} \
                        CONFIG.CLKOUT1_DRIVES {BUFG} \
                        CONFIG.MMCM_DIVCLK_DIVIDE {1} \
                        CONFIG.MMCM_CLKFBOUT_MULT_F {10} \
                        CONFIG.MMCM_COMPENSATION {ZHOLD} \
                        CONFIG.MMCM_CLKOUT0_DIVIDE_F {5} \
                        CONFIG.RESET_PORT {resetn} \
                        CONFIG.CLKOUT1_JITTER {114.829} \
                        CONFIG.CLKOUT1_PHASE_ERROR {98.575} \
                        CONFIG.CLKOUT2_DRIVES {BUFG} \
                        CONFIG.CLKOUT2_REQUESTED_OUT_FREQ {60.000} \
                        CONFIG.CLKOUT2_USED {1} \
                        CONFIG.CLK_OUT2_PORT {clk_io_uart} \
                        CONFIG.CLKOUT3_DRIVES {BUFG} \
                        CONFIG.CLKOUT3_REQUESTED_OUT_FREQ {120.000} \
                        CONFIG.CLKOUT3_USED {1} \
                        CONFIG.CLK_OUT3_PORT {clk_pixel} \
                        CONFIG.CLKOUT4_USED {1} \
                        CONFIG.CLKOUT4_DRIVES {BUFG} \
                        CONFIG.CLKOUT4_REQUESTED_OUT_FREQ {50.000} \
                        CONFIG.CLK_OUT4_PORT {clk_rmii} \
                        CONFIG.CLKOUT5_USED {1} \
                        CONFIG.CLKOUT5_DRIVES {BUFG} \
                        CONFIG.CLKOUT5_REQUESTED_OUT_FREQ {50.000} \
                        CONFIG.CLKOUT5_REQUESTED_PHASE {90.000} \
                        CONFIG.CLK_OUT5_PORT {clk_rmii_quad}] \
    [get_ips clk_wiz_0]
generate_target {instantiation_template} [get_files $proj_dir/$project_name.srcs/sources_1/ip/clk_wiz_0/clk_wiz_0.xci]
#SD-card clock generator
create_ip -name clk_wiz -vendor xilinx.com -library ip -module_name clk_wiz_1
set_property -dict [list \
                        CONFIG.PRIMITIVE {MMCM} \
                        CONFIG.USE_DYN_RECONFIG {true} \
                        CONFIG.INTERFACE_SELECTION {Enable_DRP} \
                        CONFIG.PRIM_IN_FREQ {25.000} \
                        CONFIG.CLK_OUT1_PORT {clk_sdclk} \
                        CONFIG.CLKOUT1_REQUESTED_OUT_FREQ {5.000} \
                        CONFIG.PHASE_DUTY_CONFIG {false} \
                        CONFIG.CLKIN1_JITTER_PS {400.0} \
                        CONFIG.CLKOUT1_DRIVES {BUFG} \
                        CONFIG.CLKOUT2_DRIVES {BUFG} \
                        CONFIG.CLKOUT3_DRIVES {BUFG} \
                        CONFIG.CLKOUT4_DRIVES {BUFG} \
                        CONFIG.CLKOUT5_DRIVES {BUFG} \
                        CONFIG.CLKOUT6_DRIVES {BUFG} \
                        CONFIG.CLKOUT7_DRIVES {BUFG} \
                        CONFIG.FEEDBACK_SOURCE {FDBK_AUTO} \
                        CONFIG.MMCM_DIVCLK_DIVIDE {1} \
                        CONFIG.MMCM_CLKFBOUT_MULT_F {25.500} \
                        CONFIG.MMCM_CLKIN1_PERIOD {40.0} \
                        CONFIG.MMCM_COMPENSATION {ZHOLD} \
                        CONFIG.MMCM_CLKOUT0_DIVIDE_F {127.500} \
                        CONFIG.CLKOUT1_JITTER {652.674} \
                        CONFIG.CLKOUT1_PHASE_ERROR {319.966}] [get_ips clk_wiz_1]
generate_target {instantiation_template} [get_files $proj_dir/$project_name.srcs/sources_1/ip/clk_wiz_1/clk_wiz_1.xci]

# SPI interface for R/W SD card
create_ip -name axi_quad_spi -vendor xilinx.com -library ip -module_name axi_quad_spi_0
set_property -dict [list \
                        CONFIG.C_USE_STARTUP {0} \
                        CONFIG.C_SCK_RATIO {2} \
                        CONFIG.C_NUM_TRANSFER_BITS {8}] \
    [get_ips axi_quad_spi_0]
generate_target {instantiation_template} [get_files $proj_dir/$project_name.srcs/sources_1/ip/axi_quad_spi_0/axi_quad_spi_0.xci]

# Quad SPI interface for XIP SPI Flash
create_ip -name axi_quad_spi -vendor xilinx.com -library ip -module_name axi_quad_spi_1
set_property -dict [list \
                        CONFIG.C_USE_STARTUP {1} \
                        CONFIG.C_SPI_MEMORY {3} \
                        CONFIG.C_SPI_MODE {2} \
                        CONFIG.C_XIP_MODE {1} \
                        CONFIG.C_SPI_MEM_ADDR_BITS {32} \
                        CONFIG.C_S_AXI4_ID_WIDTH $axi_id_width \
                        CONFIG.C_SCK_RATIO {2} \
                        CONFIG.C_TYPE_OF_AXI4_INTERFACE {1}] \
    [get_ips axi_quad_spi_1]
generate_target {instantiation_template} [get_files $proj_dir/$project_name.srcs/sources_1/ip/axi_quad_spi_1/axi_quad_spi_1.xci]

# Create 'constrs_1' fileset (if not found)
if {[string equal [get_filesets -quiet constrs_1] ""]} {
  create_fileset -constrset constrs_1
}

# Set 'constrs_1' fileset object
set obj [get_filesets constrs_1]

# Add/Import constrs file and set constrs file properties
set files [list [file normalize "constraint/pin_plan.xdc"] \
	       [file normalize "constraint/timing.xdc"]]

set file_added [add_files -norecurse -fileset $obj $files]

# generate all IP source code
generate_target all [get_ips]

# force create the synth_1 path (need to make soft link in Makefile)
launch_runs -scripts_only synth_1


# Create 'sim_1' fileset (if not found)
if {[string equal [get_filesets -quiet sim_1] ""]} {
  create_fileset -simset sim_1
}

# Set 'sim_1' fileset object
set obj [get_filesets sim_1]
set files [list \
               [file normalize $base_dir/src/test/verilog/host_behav.sv] \
               [file normalize $base_dir/src/test/verilog/sd_verilator_model.sv] \
               [file normalize $base_dir/src/test/verilog/nasti_ram_dummy.sv] \
               [file normalize $base_dir/src/test/verilog/chip_top_tb.sv] \
              ]
add_files -norecurse -fileset $obj $files

# add include path
set_property include_dirs [list \
                               [file normalize $base_dir/src/main/verilog] \
                               [file normalize $origin_dir/src] \
                               [file normalize $origin_dir/generated-src] \
                               [file normalize $proj_dir/$project_name.srcs/sources_1/ip/mig_7series_0/mig_7series_0/example_design/sim] \
                              ] $obj
#set_property verilog_define [list FPGA FPGA_FULL NEXYS4] $obj
set_property verilog_define [list FPGA NASTI_RAM_DUMMY BOOT_MEM=\"[file normalize $origin_dir/src/boot.mem]\"] $obj

#set_property -name {xsim.elaborate.xelab.more_options} -value {-cc gcc -sv_lib dpi} -objects $obj
set_property "top" "tb" $obj

# force create the sim_1/behav path (need to make soft link in Makefile)
launch_simulation -scripts_only

# suppress some not very useful messages
# warning partial connection
set_msg_config -id "\[Synth 8-350\]" -suppress
# info do synthesis
set_msg_config -id "\[Synth 8-256\]" -suppress
set_msg_config -id "\[Synth 8-638\]" -suppress
# BRAM mapped to LUT due to optimization
set_msg_config -id "\[Synth 8-3969\]" -suppress
# BRAM with no output register
set_msg_config -id "\[Synth 8-4480\]" -suppress
# DSP without input pipelining
set_msg_config -id "\[Drc 23-20\]" -suppress
# Update IP version
set_msg_config -id "\[Netlist 29-345\]" -suppress


# do not flatten design
set_property STEPS.SYNTH_DESIGN.ARGS.FLATTEN_HIERARCHY none [get_runs synth_1]
