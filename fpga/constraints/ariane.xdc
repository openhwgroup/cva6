## Common Ariane XDCs

create_clock -period 100.000 -name tck -waveform {0.000 50.000} [get_ports tck]
set_input_jitter tck 1.000

set_max_delay -datapath_only -from [get_pins i_dmi_jtag/i_dmi_cdc/i_cdc_resp/i_src/data_src_q_reg*/C] -to [get_pins i_dmi_jtag/i_dmi_cdc/i_cdc_resp/i_dst/data_dst_q_reg*/D] 10.000
set_max_delay -datapath_only -from [get_pins i_dmi_jtag/i_dmi_cdc/i_cdc_resp/i_src/req_src_q_reg/C] -to [get_pins i_dmi_jtag/i_dmi_cdc/i_cdc_resp/i_dst/req_dst_q_reg/D] 10.000
set_max_delay -datapath_only -from [get_pins i_dmi_jtag/i_dmi_cdc/i_cdc_req/i_dst/ack_dst_q_reg/C] -to [get_pins i_dmi_jtag/i_dmi_cdc/i_cdc_req/i_src/ack_src_q_reg/D] 10.000




