# Xilinx Vivado script
# Version: Vivado 2015.4
# Function:
#   Generate a vivado project for the lowRISC SoC

set mem_data_width {64}
set io_data_width {32}
set axi_id_width {8}
set axi_user_width {2}

set origin_dir "."
set base_dir "src"

set project_name "debug_wrap"
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
 "[file normalize "$origin_dir/src/socip/util/arbiter.sv"]"\
 "[file normalize "$origin_dir/src/soc/sd_crc_7.v"]"\
 "[file normalize "$origin_dir/src/soc/sd_crc_16.v"]"\
 "[file normalize "$origin_dir/src/soc/eth_lfsr.v"]"\
 "[file normalize "$origin_dir/src/socip/nasti/channel.sv"]"\
 "[file normalize "$origin_dir/src/jtag_xilinx/jtag_rom.v"]"\
 "[file normalize "$origin_dir/src/jtag_xilinx/jtag_addr.v"]"\
 "[file normalize "$origin_dir/src/socip/nasti/nasti_slicer.sv"]"\
 "[file normalize "$origin_dir/src/socip/nasti/nasti_mux.sv"]"\
 "[file normalize "$origin_dir/src/socip/nasti/nasti_demux.sv"]"\
 "[file normalize "$origin_dir/src/socip/nasti/nasti_combiner.sv"]"\
 "[file normalize "$origin_dir/src/socip/nasti/nasti_buf.sv"]"\
 "[file normalize "$origin_dir/src/util/slave_adapter.sv"]"\
 "[file normalize "$origin_dir/src/soc/sd_defines.h"]"\
 "[file normalize "$origin_dir/src/soc/sd_data_serial_host.sv"]"\
 "[file normalize "$origin_dir/src/soc/sd_cmd_serial_host.v"]"\
 "[file normalize "$origin_dir/src/soc/ps2_defines.v"]"\
 "[file normalize "$origin_dir/src/soc/ps2_translation_table.v"]"\
 "[file normalize "$origin_dir/src/soc/ps2_keyboard.v"]"\
 "[file normalize "$origin_dir/src/soc/dualmem.v"]"\
 "[file normalize "$origin_dir/src/soc/axis_gmii_tx.v"]"\
 "[file normalize "$origin_dir/src/soc/axis_gmii_rx.v"]"\
 "[file normalize "$origin_dir/src/axi_if/axi_if.sv"]"\
 "[file normalize "$origin_dir/src/jtag_xilinx/jtag_dummy.v"]"\
 "[file normalize "$origin_dir/src/util/core2axi.sv"]"\
 "[file normalize "$origin_dir/src/socip/nasti/nasti_crossbar.sv"]"\
 "[file normalize "$origin_dir/src/util/if_converter.sv"]"\
 "[file normalize "$origin_dir/src/util/nasti_converter.sv"]"\
 "[file normalize "$origin_dir/src/socip/nasti/nasti_bram_ctrl.sv"]"\
 "[file normalize "$origin_dir/src/util/sevensegment.v"]"\
 "[file normalize "$origin_dir/src/util/nexys4ddr_display.v"]"\
 "[file normalize "$origin_dir/src/soc/uart.v"]"\
 "[file normalize "$origin_dir/src/soc/sd_top.sv"]"\
 "[file normalize "$origin_dir/src/soc/rx_delay.v"]"\
 "[file normalize "$origin_dir/src/soc/ascii_code.v"]"\
 "[file normalize "$origin_dir/src/soc/ps2.v"]"\
 "[file normalize "$origin_dir/src/soc/my_fifo.v"]"\
 "[file normalize "$origin_dir/src/soc/fstore2.v"]"\
 "[file normalize "$origin_dir/src/soc/framing_top.sv"]"\
 "[file normalize "$origin_dir/src/util/dbg_wrap.sv"]"\
 "[file normalize "$origin_dir/src/util/crossbar_socip_test.sv"]"\
 "[file normalize "$origin_dir/src/util/axi_ram_wrap.sv"]"\
 "[file normalize "$origin_dir/src/util/display_top.sv"]"\
 "[file normalize "$origin_dir/src/soc/periph_soc.sv"]"\
 "[file normalize "$origin_dir/src/util/wrap_top.sv"]"\
 "[file normalize "$origin_dir/src/util/cluster_clock_gating.sv"]"\
 "[file normalize "$origin_dir/src/util/generic_fifo.sv"]"\
 "[file normalize "$origin_dir/src/axi_slice/axi_w_buffer.sv"]"\
 "[file normalize "$origin_dir/src/axi_slice/axi_r_buffer.sv"]"\
 "[file normalize "$origin_dir/src/axi_slice/axi_b_buffer.sv"]"\
 "[file normalize "$origin_dir/src/axi_slice/axi_aw_buffer.sv"]"\
 "[file normalize "$origin_dir/src/axi_slice/axi_ar_buffer.sv"]"\
 "[file normalize "$origin_dir/src/axi_mem_if/axi_mem_if.sv"]"\
 "[file normalize "$origin_dir/src/util/axi_bram_ctrl_ariane.sv"]"\
 "[file normalize "$origin_dir/src/util/infer_ram.sv"]"\
 "[file normalize "$origin_dir/include/ariane_pkg.sv"]"\
 "[file normalize "$origin_dir/src/soc/ddr2_model_parameters.vh"]"\
 "[file normalize "$origin_dir/src/soc/infer_bram.sv"]"\
 "[file normalize "$origin_dir/src/socip/nasti/nasti_request.vh"]"\
 "[file normalize "$origin_dir/src/socip/nasti/nasti_lite_writer.sv"]"\
 "[file normalize "$origin_dir/src/socip/nasti/nasti_lite_reader.sv"]"\
 "[file normalize "$origin_dir/src/socip/nasti/nasti_narrower_writer.sv"]"\
 "[file normalize "$origin_dir/src/socip/nasti/lite_nasti_writer.sv"]"\
 "[file normalize "$origin_dir/src/socip/nasti/nasti_narrower.sv"]"\
 "[file normalize "$origin_dir/src/socip/nasti/nasti_narrower_reader.sv"]"\
 "[file normalize "$origin_dir/src/socip/nasti/lite_nasti_reader.sv"]"\
 "[file normalize "$origin_dir/src/socip/nasti/nasti_lite_bridge.sv"]"\
 "[file normalize "$origin_dir/src/socip/nasti/nasti_data_mover.sv"]"\
 "[file normalize "$origin_dir/src/axi_slice/axi_buffer.sv"]"\
 "[file normalize "$origin_dir/src/axi_slice/axi_slice.sv"]"\
 "[file normalize "$origin_dir/src/axi_slice/axi_slice_wrap.sv"]"\
 "[file normalize "$origin_dir/src/util/cluster_clock_mux2.sv"]"\
 "[file normalize "$origin_dir/src/util/cluster_clock_inverter.sv"]"\
             ]
add_files -norecurse -fileset [get_filesets sources_1] $files

# add include path
set_property include_dirs [list \
                               [file normalize $base_dir/include] \
                              ] [get_filesets sources_1]

set_property verilog_define [list MIG FPGA FPGA_FULL NEXYS4 PULP_FPGA_EMUL NASTI_BRAM BOOT_MEM=\"[file normalize $origin_dir/src/boot.mem]\"] [get_filesets sources_1]

# Set 'sources_1' fileset properties
set_property "top" "ariane_nexys4ddr" [get_filesets sources_1]

# Program/data RAM
create_ip -name blk_mem_gen -vendor xilinx.com -library ip -module_name instr_ram
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

create_ip -name blk_mem_gen -vendor xilinx.com -library ip -module_name data_ram
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

# Clock generators
create_ip -name clk_wiz -vendor xilinx.com -library ip -module_name clk_wiz_ariane
set_property -dict [list \
                        CONFIG.PRIMITIVE {PLL} \
                        CONFIG.CLKOUT1_REQUESTED_OUT_FREQ {200.000} \
                        CONFIG.RESET_TYPE {ACTIVE_LOW} \
                        CONFIG.CLKOUT1_DRIVES {BUFG} \
                        CONFIG.MMCM_DIVCLK_DIVIDE {1} \
                        CONFIG.MMCM_COMPENSATION {ZHOLD} \
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
                        CONFIG.CLK_OUT5_PORT {clk_rmii_quad} \
			CONFIG.CLKOUT6_USED {true} \
			CONFIG.CLK_OUT6_PORT {clk_i} \
			CONFIG.CLKOUT6_REQUESTED_OUT_FREQ {25.000} \
			CONFIG.NUM_OUT_CLKS {6} \
		   ] \
    [get_ips clk_wiz_ariane]
generate_target {instantiation_template} [get_files $proj_dir/$project_name.srcs/sources_1/ip/clk_wiz_ariane/clk_wiz_ariane.xci]

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

# Create 'constrs_1' fileset (if not found)
if {[string equal [get_filesets -quiet constrs_1] ""]} {
  create_fileset -constrset constrs_1
}

# Set 'constrs_1' fileset object
set obj [get_filesets constrs_1]

# Add/Import constrs file and set constrs file properties
set files [list [file normalize "constraint/pin_plan_debug.xdc"]]

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
               [file normalize $base_dir/soc/sd_verilator_model.sv] \
               [file normalize $base_dir/soc/ariane_nexys4ddr_top_tb.sv] \
              ]
add_files -norecurse -fileset $obj $files

# add include path
set_property include_dirs [list \
                               [file normalize $base_dir/src/main/verilog] \
                               [file normalize $origin_dir/src] \
                               [file normalize $origin_dir/generated-src] \
                               [file normalize $proj_dir/$project_name.srcs/sources_1/ip/mig_7series_0/mig_7series_0/example_design/sim] \
                              ] $obj

set_property verilog_define [list FPGA NASTI_RAM_DUMMY] $obj

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

