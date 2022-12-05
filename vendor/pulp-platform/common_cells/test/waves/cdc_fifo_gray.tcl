onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -divider memory
add wave -noupdate /cdc_fifo_tb/genblk1/i_dut/fifo_widx
add wave -noupdate /cdc_fifo_tb/genblk1/i_dut/fifo_ridx
add wave -noupdate /cdc_fifo_tb/genblk1/i_dut/fifo_write
add wave -noupdate /cdc_fifo_tb/genblk1/i_dut/fifo_wdata
add wave -noupdate /cdc_fifo_tb/genblk1/i_dut/fifo_rdata
add wave -noupdate -divider src
add wave -noupdate /cdc_fifo_tb/genblk1/i_dut/src_rst_ni
add wave -noupdate /cdc_fifo_tb/genblk1/i_dut/src_clk_i
add wave -noupdate /cdc_fifo_tb/genblk1/i_dut/src_data_i
add wave -noupdate /cdc_fifo_tb/genblk1/i_dut/src_valid_i
add wave -noupdate /cdc_fifo_tb/genblk1/i_dut/src_ready_o
add wave -noupdate /cdc_fifo_tb/genblk1/i_dut/src_wptr_bin_q
add wave -noupdate /cdc_fifo_tb/genblk1/i_dut/src_rptr_bin
add wave -noupdate -divider dst
add wave -noupdate /cdc_fifo_tb/genblk1/i_dut/dst_rst_ni
add wave -noupdate /cdc_fifo_tb/genblk1/i_dut/dst_clk_i
add wave -noupdate /cdc_fifo_tb/genblk1/i_dut/dst_data_o
add wave -noupdate /cdc_fifo_tb/genblk1/i_dut/dst_valid_o
add wave -noupdate /cdc_fifo_tb/genblk1/i_dut/dst_ready_i
add wave -noupdate /cdc_fifo_tb/genblk1/i_dut/dst_rptr_bin_q
add wave -noupdate /cdc_fifo_tb/genblk1/i_dut/dst_wptr_bin
add wave -noupdate -divider async
add wave -noupdate /cdc_fifo_tb/genblk1/i_dut/src_wptr_gray_q
add wave -noupdate /cdc_fifo_tb/genblk1/i_dut/dst_rptr_gray_q
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {162840203 ps} 0}
quietly wave cursor active 1
configure wave -namecolwidth 159
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
WaveRestoreZoom {0 ps} {704185650 ps}
