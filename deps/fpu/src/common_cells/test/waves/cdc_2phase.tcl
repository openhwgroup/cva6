onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /cdc_2phase_tb/g_dut/i_dut/src_rst_ni
add wave -noupdate /cdc_2phase_tb/g_dut/i_dut/src_clk_i
add wave -noupdate /cdc_2phase_tb/g_dut/i_dut/src_data_i
add wave -noupdate /cdc_2phase_tb/g_dut/i_dut/src_valid_i
add wave -noupdate /cdc_2phase_tb/g_dut/i_dut/src_ready_o
add wave -noupdate /cdc_2phase_tb/g_dut/i_dut/dst_rst_ni
add wave -noupdate /cdc_2phase_tb/g_dut/i_dut/dst_clk_i
add wave -noupdate /cdc_2phase_tb/g_dut/i_dut/dst_data_o
add wave -noupdate /cdc_2phase_tb/g_dut/i_dut/dst_valid_o
add wave -noupdate /cdc_2phase_tb/g_dut/i_dut/dst_ready_i
add wave -noupdate /cdc_2phase_tb/g_dut/i_dut/async_req_o
add wave -noupdate /cdc_2phase_tb/g_dut/i_dut/async_req_i
add wave -noupdate /cdc_2phase_tb/g_dut/i_dut/async_ack_o
add wave -noupdate /cdc_2phase_tb/g_dut/i_dut/async_ack_i
add wave -noupdate /cdc_2phase_tb/g_dut/i_dut/async_data_o
add wave -noupdate /cdc_2phase_tb/g_dut/i_dut/async_data_i
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {0 ps} 0}
quietly wave cursor active 1
configure wave -namecolwidth 198
configure wave -valuecolwidth 165
configure wave -justifyvalue left
configure wave -signalnamewidth 1
configure wave -snapdistance 10
configure wave -datasetprefix 0
configure wave -rowmargin 4
configure wave -childrowmargin 2
configure wave -gridoffset 0
configure wave -gridperiod 500
configure wave -griddelta 40
configure wave -timeline 0
configure wave -timelineunits ns
update
WaveRestoreZoom {0 ps} {603392 ps}
