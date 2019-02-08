## Common Ariane XDCs

create_clock -period 100.000 -name tck -waveform {0.000 50.000} [get_ports tck]
set_input_jitter tck 1.000

# minimize routing delay
set_max_delay -datapath_only -from [get_pins i_dmi_jtag/i_dmi_jtag_tap/td_o_reg/Q] -to [get_ports tdo    ] 5 
set_max_delay -from [get_ports tdi    ] 5 
set_max_delay -from [get_ports tms    ] 5 
set_max_delay -from [get_ports trst_n ] 5

# constrain clock domain crossing
create_generated_clock -name ddr_clock_out [get_pins i_xlnx_clk_gen/ddr_clock_out]
set_max_delay  -from [get_clocks tck] -to [get_clocks -include_generated_clocks ddr_clock_out] 10


set_max_delay -datapath_only -from [get_pins i_dmi_jtag/i_dmi_cdc/i_cdc_resp/i_src/data_src_q_reg*/C] -to [get_pins i_dmi_jtag/i_dmi_cdc/i_cdc_resp/i_dst/data_dst_q_reg*/D] 10.000
set_max_delay -datapath_only -from [get_pins i_dmi_jtag/i_dmi_cdc/i_cdc_resp/i_src/req_src_q_reg/C] -to [get_pins i_dmi_jtag/i_dmi_cdc/i_cdc_resp/i_dst/req_dst_q_reg/D] 10.000
set_max_delay -datapath_only -from [get_pins i_dmi_jtag/i_dmi_cdc/i_cdc_req/i_dst/ack_dst_q_reg/C] -to [get_pins i_dmi_jtag/i_dmi_cdc/i_cdc_req/i_src/ack_src_q_reg/D] 10.000



