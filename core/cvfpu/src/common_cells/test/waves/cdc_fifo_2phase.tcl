onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /cdc_fifo_tb/i_dut/src_rst_ni
add wave -noupdate /cdc_fifo_tb/i_dut/src_clk_i
add wave -noupdate /cdc_fifo_tb/i_dut/src_data_i
add wave -noupdate /cdc_fifo_tb/i_dut/src_valid_i
add wave -noupdate /cdc_fifo_tb/i_dut/src_ready_o
add wave -noupdate /cdc_fifo_tb/i_dut/dst_rst_ni
add wave -noupdate /cdc_fifo_tb/i_dut/dst_clk_i
add wave -noupdate /cdc_fifo_tb/i_dut/dst_data_o
add wave -noupdate /cdc_fifo_tb/i_dut/dst_valid_o
add wave -noupdate /cdc_fifo_tb/i_dut/dst_ready_i
add wave -noupdate /cdc_fifo_tb/i_dut/fifo_widx
add wave -noupdate /cdc_fifo_tb/i_dut/fifo_ridx
add wave -noupdate /cdc_fifo_tb/i_dut/fifo_write
add wave -noupdate /cdc_fifo_tb/i_dut/fifo_wdata
add wave -noupdate /cdc_fifo_tb/i_dut/fifo_rdata
add wave -noupdate /cdc_fifo_tb/i_dut/fifo_widx
add wave -noupdate /cdc_fifo_tb/i_dut/fifo_ridx
add wave -noupdate /cdc_fifo_tb/i_dut/fifo_write
add wave -noupdate /cdc_fifo_tb/i_dut/fifo_wdata
add wave -noupdate /cdc_fifo_tb/i_dut/fifo_rdata
add wave -noupdate /cdc_fifo_tb/i_dut/fifo_data_q
add wave -noupdate /cdc_fifo_tb/i_dut/src_wptr_q
add wave -noupdate /cdc_fifo_tb/i_dut/dst_wptr
add wave -noupdate /cdc_fifo_tb/i_dut/src_rptr
add wave -noupdate /cdc_fifo_tb/i_dut/dst_rptr_q
add wave -noupdate -expand -group {cdc wptr} /cdc_fifo_tb/i_dut/i_cdc_wptr/src_rst_ni
add wave -noupdate -expand -group {cdc wptr} /cdc_fifo_tb/i_dut/i_cdc_wptr/src_clk_i
add wave -noupdate -expand -group {cdc wptr} /cdc_fifo_tb/i_dut/i_cdc_wptr/src_data_i
add wave -noupdate -expand -group {cdc wptr} /cdc_fifo_tb/i_dut/i_cdc_wptr/src_valid_i
add wave -noupdate -expand -group {cdc wptr} /cdc_fifo_tb/i_dut/i_cdc_wptr/src_ready_o
add wave -noupdate -expand -group {cdc wptr} /cdc_fifo_tb/i_dut/i_cdc_wptr/dst_rst_ni
add wave -noupdate -expand -group {cdc wptr} /cdc_fifo_tb/i_dut/i_cdc_wptr/dst_clk_i
add wave -noupdate -expand -group {cdc wptr} /cdc_fifo_tb/i_dut/i_cdc_wptr/dst_data_o
add wave -noupdate -expand -group {cdc wptr} /cdc_fifo_tb/i_dut/i_cdc_wptr/dst_valid_o
add wave -noupdate -expand -group {cdc wptr} /cdc_fifo_tb/i_dut/i_cdc_wptr/dst_ready_i
add wave -noupdate -expand -group {cdc wptr} /cdc_fifo_tb/i_dut/i_cdc_wptr/async_req
add wave -noupdate -expand -group {cdc wptr} /cdc_fifo_tb/i_dut/i_cdc_wptr/async_ack
add wave -noupdate -expand -group {cdc wptr} /cdc_fifo_tb/i_dut/i_cdc_wptr/async_data
add wave -noupdate -expand -group {cdc rptr} /cdc_fifo_tb/i_dut/i_cdc_rptr/src_rst_ni
add wave -noupdate -expand -group {cdc rptr} /cdc_fifo_tb/i_dut/i_cdc_rptr/src_clk_i
add wave -noupdate -expand -group {cdc rptr} /cdc_fifo_tb/i_dut/i_cdc_rptr/src_data_i
add wave -noupdate -expand -group {cdc rptr} /cdc_fifo_tb/i_dut/i_cdc_rptr/src_valid_i
add wave -noupdate -expand -group {cdc rptr} /cdc_fifo_tb/i_dut/i_cdc_rptr/src_ready_o
add wave -noupdate -expand -group {cdc rptr} /cdc_fifo_tb/i_dut/i_cdc_rptr/dst_rst_ni
add wave -noupdate -expand -group {cdc rptr} /cdc_fifo_tb/i_dut/i_cdc_rptr/dst_clk_i
add wave -noupdate -expand -group {cdc rptr} /cdc_fifo_tb/i_dut/i_cdc_rptr/dst_data_o
add wave -noupdate -expand -group {cdc rptr} /cdc_fifo_tb/i_dut/i_cdc_rptr/dst_valid_o
add wave -noupdate -expand -group {cdc rptr} /cdc_fifo_tb/i_dut/i_cdc_rptr/dst_ready_i
add wave -noupdate -expand -group {cdc rptr} /cdc_fifo_tb/i_dut/i_cdc_rptr/async_req
add wave -noupdate -expand -group {cdc rptr} /cdc_fifo_tb/i_dut/i_cdc_rptr/async_ack
add wave -noupdate -expand -group {cdc rptr} /cdc_fifo_tb/i_dut/i_cdc_rptr/async_data
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {186436 ps} 0}
quietly wave cursor active 1
configure wave -namecolwidth 150
configure wave -valuecolwidth 100
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
WaveRestoreZoom {0 ps} {525 ns}
