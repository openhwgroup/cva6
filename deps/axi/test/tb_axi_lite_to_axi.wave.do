onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /tb_axi_lite_to_axi/clk
add wave -noupdate /tb_axi_lite_to_axi/rst
add wave -noupdate -expand -group {axi lite} /tb_axi_lite_to_axi/axi_lite/aw_addr
add wave -noupdate -expand -group {axi lite} /tb_axi_lite_to_axi/axi_lite/aw_valid
add wave -noupdate -expand -group {axi lite} /tb_axi_lite_to_axi/axi_lite/aw_ready
add wave -noupdate -expand -group {axi lite} /tb_axi_lite_to_axi/axi_lite/w_data
add wave -noupdate -expand -group {axi lite} /tb_axi_lite_to_axi/axi_lite/w_strb
add wave -noupdate -expand -group {axi lite} /tb_axi_lite_to_axi/axi_lite/w_valid
add wave -noupdate -expand -group {axi lite} /tb_axi_lite_to_axi/axi_lite/w_ready
add wave -noupdate -expand -group {axi lite} /tb_axi_lite_to_axi/axi_lite/b_resp
add wave -noupdate -expand -group {axi lite} /tb_axi_lite_to_axi/axi_lite/b_valid
add wave -noupdate -expand -group {axi lite} /tb_axi_lite_to_axi/axi_lite/b_ready
add wave -noupdate -expand -group {axi lite} /tb_axi_lite_to_axi/axi_lite/ar_addr
add wave -noupdate -expand -group {axi lite} /tb_axi_lite_to_axi/axi_lite/ar_valid
add wave -noupdate -expand -group {axi lite} /tb_axi_lite_to_axi/axi_lite/ar_ready
add wave -noupdate -expand -group {axi lite} /tb_axi_lite_to_axi/axi_lite/r_data
add wave -noupdate -expand -group {axi lite} /tb_axi_lite_to_axi/axi_lite/r_resp
add wave -noupdate -expand -group {axi lite} /tb_axi_lite_to_axi/axi_lite/r_valid
add wave -noupdate -expand -group {axi lite} /tb_axi_lite_to_axi/axi_lite/r_ready
add wave -noupdate -expand -group axi /tb_axi_lite_to_axi/axi/aw_id
add wave -noupdate -expand -group axi /tb_axi_lite_to_axi/axi/aw_addr
add wave -noupdate -expand -group axi /tb_axi_lite_to_axi/axi/aw_len
add wave -noupdate -expand -group axi /tb_axi_lite_to_axi/axi/aw_size
add wave -noupdate -expand -group axi /tb_axi_lite_to_axi/axi/aw_burst
add wave -noupdate -expand -group axi /tb_axi_lite_to_axi/axi/aw_lock
add wave -noupdate -expand -group axi /tb_axi_lite_to_axi/axi/aw_cache
add wave -noupdate -expand -group axi /tb_axi_lite_to_axi/axi/aw_prot
add wave -noupdate -expand -group axi /tb_axi_lite_to_axi/axi/aw_qos
add wave -noupdate -expand -group axi /tb_axi_lite_to_axi/axi/aw_region
add wave -noupdate -expand -group axi /tb_axi_lite_to_axi/axi/aw_atop
add wave -noupdate -expand -group axi /tb_axi_lite_to_axi/axi/aw_user
add wave -noupdate -expand -group axi /tb_axi_lite_to_axi/axi/aw_valid
add wave -noupdate -expand -group axi /tb_axi_lite_to_axi/axi/aw_ready
add wave -noupdate -expand -group axi /tb_axi_lite_to_axi/axi/w_data
add wave -noupdate -expand -group axi /tb_axi_lite_to_axi/axi/w_strb
add wave -noupdate -expand -group axi /tb_axi_lite_to_axi/axi/w_last
add wave -noupdate -expand -group axi /tb_axi_lite_to_axi/axi/w_user
add wave -noupdate -expand -group axi /tb_axi_lite_to_axi/axi/w_valid
add wave -noupdate -expand -group axi /tb_axi_lite_to_axi/axi/w_ready
add wave -noupdate -expand -group axi /tb_axi_lite_to_axi/axi/b_resp
add wave -noupdate -expand -group axi /tb_axi_lite_to_axi/axi/b_valid
add wave -noupdate -expand -group axi /tb_axi_lite_to_axi/axi/b_ready
add wave -noupdate -expand -group axi /tb_axi_lite_to_axi/axi/ar_id
add wave -noupdate -expand -group axi /tb_axi_lite_to_axi/axi/ar_addr
add wave -noupdate -expand -group axi /tb_axi_lite_to_axi/axi/ar_len
add wave -noupdate -expand -group axi /tb_axi_lite_to_axi/axi/ar_size
add wave -noupdate -expand -group axi /tb_axi_lite_to_axi/axi/ar_burst
add wave -noupdate -expand -group axi /tb_axi_lite_to_axi/axi/ar_lock
add wave -noupdate -expand -group axi /tb_axi_lite_to_axi/axi/ar_cache
add wave -noupdate -expand -group axi /tb_axi_lite_to_axi/axi/ar_prot
add wave -noupdate -expand -group axi /tb_axi_lite_to_axi/axi/ar_qos
add wave -noupdate -expand -group axi /tb_axi_lite_to_axi/axi/ar_region
add wave -noupdate -expand -group axi /tb_axi_lite_to_axi/axi/ar_user
add wave -noupdate -expand -group axi /tb_axi_lite_to_axi/axi/ar_valid
add wave -noupdate -expand -group axi /tb_axi_lite_to_axi/axi/ar_ready
add wave -noupdate -expand -group axi /tb_axi_lite_to_axi/axi/r_data
add wave -noupdate -expand -group axi /tb_axi_lite_to_axi/axi/r_resp
add wave -noupdate -expand -group axi /tb_axi_lite_to_axi/axi/r_valid
add wave -noupdate -expand -group axi /tb_axi_lite_to_axi/axi/r_ready
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {16 ns} 0}
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
WaveRestoreZoom {0 ns} {408 ns}
