onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /tb_axi_to_axi_lite/i_dut/clk_i
add wave -noupdate /tb_axi_to_axi_lite/i_dut/rst_ni
add wave -noupdate /tb_axi_to_axi_lite/i_dut/rd_full
add wave -noupdate /tb_axi_to_axi_lite/i_dut/wr_full
add wave -noupdate -expand -group {FIFO (rd)} /tb_axi_to_axi_lite/i_dut/i_fifo_rd/push_i
add wave -noupdate -expand -group {FIFO (rd)} /tb_axi_to_axi_lite/i_dut/i_fifo_rd/pop_i
add wave -noupdate -expand -group {FIFO (wr)} /tb_axi_to_axi_lite/i_dut/i_fifo_wr/push_i
add wave -noupdate -expand -group {FIFO (wr)} /tb_axi_to_axi_lite/i_dut/i_fifo_wr/pop_i
add wave -noupdate -expand /tb_axi_to_axi_lite/i_dut/meta_rd
add wave -noupdate -expand /tb_axi_to_axi_lite/i_dut/meta_wr
add wave -noupdate -expand -group {in (AXI4)} /tb_axi_to_axi_lite/axi/clk_i
add wave -noupdate -expand -group {in (AXI4)} /tb_axi_to_axi_lite/axi/aw_id
add wave -noupdate -expand -group {in (AXI4)} /tb_axi_to_axi_lite/axi/aw_addr
add wave -noupdate -expand -group {in (AXI4)} /tb_axi_to_axi_lite/axi/aw_len
add wave -noupdate -expand -group {in (AXI4)} /tb_axi_to_axi_lite/axi/aw_size
add wave -noupdate -expand -group {in (AXI4)} /tb_axi_to_axi_lite/axi/aw_burst
add wave -noupdate -expand -group {in (AXI4)} /tb_axi_to_axi_lite/axi/aw_lock
add wave -noupdate -expand -group {in (AXI4)} /tb_axi_to_axi_lite/axi/aw_cache
add wave -noupdate -expand -group {in (AXI4)} /tb_axi_to_axi_lite/axi/aw_prot
add wave -noupdate -expand -group {in (AXI4)} /tb_axi_to_axi_lite/axi/aw_qos
add wave -noupdate -expand -group {in (AXI4)} /tb_axi_to_axi_lite/axi/aw_region
add wave -noupdate -expand -group {in (AXI4)} /tb_axi_to_axi_lite/axi/aw_atop
add wave -noupdate -expand -group {in (AXI4)} /tb_axi_to_axi_lite/axi/aw_user
add wave -noupdate -expand -group {in (AXI4)} /tb_axi_to_axi_lite/axi/aw_valid
add wave -noupdate -expand -group {in (AXI4)} /tb_axi_to_axi_lite/axi/aw_ready
add wave -noupdate -expand -group {in (AXI4)} /tb_axi_to_axi_lite/axi/w_data
add wave -noupdate -expand -group {in (AXI4)} /tb_axi_to_axi_lite/axi/w_strb
add wave -noupdate -expand -group {in (AXI4)} /tb_axi_to_axi_lite/axi/w_last
add wave -noupdate -expand -group {in (AXI4)} /tb_axi_to_axi_lite/axi/w_user
add wave -noupdate -expand -group {in (AXI4)} /tb_axi_to_axi_lite/axi/w_valid
add wave -noupdate -expand -group {in (AXI4)} /tb_axi_to_axi_lite/axi/w_ready
add wave -noupdate -expand -group {in (AXI4)} /tb_axi_to_axi_lite/axi/b_id
add wave -noupdate -expand -group {in (AXI4)} /tb_axi_to_axi_lite/axi/b_resp
add wave -noupdate -expand -group {in (AXI4)} /tb_axi_to_axi_lite/axi/b_user
add wave -noupdate -expand -group {in (AXI4)} /tb_axi_to_axi_lite/axi/b_valid
add wave -noupdate -expand -group {in (AXI4)} /tb_axi_to_axi_lite/axi/b_ready
add wave -noupdate -expand -group {in (AXI4)} /tb_axi_to_axi_lite/axi/ar_id
add wave -noupdate -expand -group {in (AXI4)} /tb_axi_to_axi_lite/axi/ar_addr
add wave -noupdate -expand -group {in (AXI4)} /tb_axi_to_axi_lite/axi/ar_len
add wave -noupdate -expand -group {in (AXI4)} /tb_axi_to_axi_lite/axi/ar_size
add wave -noupdate -expand -group {in (AXI4)} /tb_axi_to_axi_lite/axi/ar_burst
add wave -noupdate -expand -group {in (AXI4)} /tb_axi_to_axi_lite/axi/ar_lock
add wave -noupdate -expand -group {in (AXI4)} /tb_axi_to_axi_lite/axi/ar_cache
add wave -noupdate -expand -group {in (AXI4)} /tb_axi_to_axi_lite/axi/ar_prot
add wave -noupdate -expand -group {in (AXI4)} /tb_axi_to_axi_lite/axi/ar_qos
add wave -noupdate -expand -group {in (AXI4)} /tb_axi_to_axi_lite/axi/ar_region
add wave -noupdate -expand -group {in (AXI4)} /tb_axi_to_axi_lite/axi/ar_user
add wave -noupdate -expand -group {in (AXI4)} /tb_axi_to_axi_lite/axi/ar_valid
add wave -noupdate -expand -group {in (AXI4)} /tb_axi_to_axi_lite/axi/ar_ready
add wave -noupdate -expand -group {in (AXI4)} /tb_axi_to_axi_lite/axi/r_id
add wave -noupdate -expand -group {in (AXI4)} /tb_axi_to_axi_lite/axi/r_data
add wave -noupdate -expand -group {in (AXI4)} /tb_axi_to_axi_lite/axi/r_resp
add wave -noupdate -expand -group {in (AXI4)} /tb_axi_to_axi_lite/axi/r_last
add wave -noupdate -expand -group {in (AXI4)} /tb_axi_to_axi_lite/axi/r_user
add wave -noupdate -expand -group {in (AXI4)} /tb_axi_to_axi_lite/axi/r_valid
add wave -noupdate -expand -group {in (AXI4)} /tb_axi_to_axi_lite/axi/r_ready
add wave -noupdate -expand -group {out (AXI4-Lite)} /tb_axi_to_axi_lite/axi_lite/clk_i
add wave -noupdate -expand -group {out (AXI4-Lite)} /tb_axi_to_axi_lite/axi_lite/aw_addr
add wave -noupdate -expand -group {out (AXI4-Lite)} /tb_axi_to_axi_lite/axi_lite/aw_valid
add wave -noupdate -expand -group {out (AXI4-Lite)} /tb_axi_to_axi_lite/axi_lite/aw_ready
add wave -noupdate -expand -group {out (AXI4-Lite)} /tb_axi_to_axi_lite/axi_lite/w_data
add wave -noupdate -expand -group {out (AXI4-Lite)} /tb_axi_to_axi_lite/axi_lite/w_strb
add wave -noupdate -expand -group {out (AXI4-Lite)} /tb_axi_to_axi_lite/axi_lite/w_valid
add wave -noupdate -expand -group {out (AXI4-Lite)} /tb_axi_to_axi_lite/axi_lite/w_ready
add wave -noupdate -expand -group {out (AXI4-Lite)} /tb_axi_to_axi_lite/axi_lite/b_resp
add wave -noupdate -expand -group {out (AXI4-Lite)} /tb_axi_to_axi_lite/axi_lite/b_valid
add wave -noupdate -expand -group {out (AXI4-Lite)} /tb_axi_to_axi_lite/axi_lite/b_ready
add wave -noupdate -expand -group {out (AXI4-Lite)} /tb_axi_to_axi_lite/axi_lite/ar_addr
add wave -noupdate -expand -group {out (AXI4-Lite)} /tb_axi_to_axi_lite/axi_lite/ar_valid
add wave -noupdate -expand -group {out (AXI4-Lite)} /tb_axi_to_axi_lite/axi_lite/ar_ready
add wave -noupdate -expand -group {out (AXI4-Lite)} /tb_axi_to_axi_lite/axi_lite/r_data
add wave -noupdate -expand -group {out (AXI4-Lite)} /tb_axi_to_axi_lite/axi_lite/r_resp
add wave -noupdate -expand -group {out (AXI4-Lite)} /tb_axi_to_axi_lite/axi_lite/r_valid
add wave -noupdate -expand -group {out (AXI4-Lite)} /tb_axi_to_axi_lite/axi_lite/r_ready
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {8 ns} 0}
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
WaveRestoreZoom {0 ns} {105 ns}
