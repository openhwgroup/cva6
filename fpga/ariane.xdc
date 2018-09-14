set_property PACKAGE_PIN AM13 [get_ports sys_rst]
set_property IOSTANDARD LVCMOS33 [get_ports sys_rst]
# PMOD0_0
set_property PACKAGE_PIN A20 [get_ports tck]
set_property IOSTANDARD LVCMOS33 [get_ports tck]
set_property PACKAGE_PIN B20 [get_ports tdi]
set_property PACKAGE_PIN A22 [get_ports tdo]
set_property PACKAGE_PIN A21 [get_ports tms]
set_property PACKAGE_PIN B21 [get_ports trst_n]
set_property IOSTANDARD LVCMOS33 [get_ports tdi]
set_property IOSTANDARD LVCMOS33 [get_ports tdo]
set_property IOSTANDARD LVCMOS33 [get_ports tms]
set_property IOSTANDARD LVCMOS33 [get_ports trst_n]
# accept sub-optimal placement
set_property CLOCK_DEDICATED_ROUTE FALSE [get_nets tck_IBUF_inst/O]

create_clock -period 100.000 -name tck -waveform {0.000 50.000} [get_ports tck]
set_input_jitter tck 1.000

set_max_delay -datapath_only -from [get_pins i_dmi_jtag/i_dmi_cdc/i_cdc_resp/i_src/data_src_q_reg*/C] -to [get_pins i_dmi_jtag/i_dmi_cdc/i_cdc_resp/i_dst/data_dst_q_reg*/D] 5.000
set_max_delay -datapath_only -from [get_pins i_dmi_jtag/i_dmi_cdc/i_cdc_resp/i_src/req_src_q_reg/C] -to [get_pins i_dmi_jtag/i_dmi_cdc/i_cdc_resp/i_dst/req_dst_q_reg/D] 5.000
set_max_delay -datapath_only -from [get_pins i_dmi_jtag/i_dmi_cdc/i_cdc_req/i_dst/ack_dst_q_reg/C] -to [get_pins i_dmi_jtag/i_dmi_cdc/i_cdc_req/i_src/ack_src_q_reg/D] 5.000

set_property C_CLK_INPUT_FREQ_HZ 300000000 [get_debug_cores dbg_hub]
set_property C_ENABLE_CLK_DIVIDER false [get_debug_cores dbg_hub]
set_property C_USER_SCAN_CHAIN 1 [get_debug_cores dbg_hub]
connect_debug_port dbg_hub/clk [get_nets clk_1]
