onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /tb_axi_atop_filter/clk
add wave -noupdate /tb_axi_atop_filter/rst_n
add wave -noupdate -expand -group upstream /tb_axi_atop_filter/upstream/aw_id
add wave -noupdate -expand -group upstream /tb_axi_atop_filter/upstream/aw_addr
add wave -noupdate -expand -group upstream /tb_axi_atop_filter/upstream/aw_len
add wave -noupdate -expand -group upstream /tb_axi_atop_filter/upstream/aw_size
add wave -noupdate -expand -group upstream /tb_axi_atop_filter/upstream/aw_burst
add wave -noupdate -expand -group upstream /tb_axi_atop_filter/upstream/aw_lock
add wave -noupdate -expand -group upstream /tb_axi_atop_filter/upstream/aw_cache
add wave -noupdate -expand -group upstream /tb_axi_atop_filter/upstream/aw_prot
add wave -noupdate -expand -group upstream /tb_axi_atop_filter/upstream/aw_qos
add wave -noupdate -expand -group upstream /tb_axi_atop_filter/upstream/aw_region
add wave -noupdate -expand -group upstream /tb_axi_atop_filter/upstream/aw_atop
add wave -noupdate -expand -group upstream /tb_axi_atop_filter/upstream/aw_user
add wave -noupdate -expand -group upstream /tb_axi_atop_filter/upstream/aw_valid
add wave -noupdate -expand -group upstream /tb_axi_atop_filter/upstream/aw_ready
add wave -noupdate -expand -group upstream /tb_axi_atop_filter/upstream/w_data
add wave -noupdate -expand -group upstream /tb_axi_atop_filter/upstream/w_strb
add wave -noupdate -expand -group upstream /tb_axi_atop_filter/upstream/w_last
add wave -noupdate -expand -group upstream /tb_axi_atop_filter/upstream/w_user
add wave -noupdate -expand -group upstream /tb_axi_atop_filter/upstream/w_valid
add wave -noupdate -expand -group upstream /tb_axi_atop_filter/upstream/w_ready
add wave -noupdate -expand -group upstream /tb_axi_atop_filter/upstream/b_id
add wave -noupdate -expand -group upstream /tb_axi_atop_filter/upstream/b_resp
add wave -noupdate -expand -group upstream /tb_axi_atop_filter/upstream/b_user
add wave -noupdate -expand -group upstream /tb_axi_atop_filter/upstream/b_valid
add wave -noupdate -expand -group upstream /tb_axi_atop_filter/upstream/b_ready
add wave -noupdate -expand -group upstream /tb_axi_atop_filter/upstream/ar_id
add wave -noupdate -expand -group upstream /tb_axi_atop_filter/upstream/ar_addr
add wave -noupdate -expand -group upstream /tb_axi_atop_filter/upstream/ar_len
add wave -noupdate -expand -group upstream /tb_axi_atop_filter/upstream/ar_size
add wave -noupdate -expand -group upstream /tb_axi_atop_filter/upstream/ar_burst
add wave -noupdate -expand -group upstream /tb_axi_atop_filter/upstream/ar_lock
add wave -noupdate -expand -group upstream /tb_axi_atop_filter/upstream/ar_cache
add wave -noupdate -expand -group upstream /tb_axi_atop_filter/upstream/ar_prot
add wave -noupdate -expand -group upstream /tb_axi_atop_filter/upstream/ar_qos
add wave -noupdate -expand -group upstream /tb_axi_atop_filter/upstream/ar_region
add wave -noupdate -expand -group upstream /tb_axi_atop_filter/upstream/ar_user
add wave -noupdate -expand -group upstream /tb_axi_atop_filter/upstream/ar_valid
add wave -noupdate -expand -group upstream /tb_axi_atop_filter/upstream/ar_ready
add wave -noupdate -expand -group upstream /tb_axi_atop_filter/upstream/r_id
add wave -noupdate -expand -group upstream /tb_axi_atop_filter/upstream/r_data
add wave -noupdate -expand -group upstream /tb_axi_atop_filter/upstream/r_resp
add wave -noupdate -expand -group upstream /tb_axi_atop_filter/upstream/r_last
add wave -noupdate -expand -group upstream /tb_axi_atop_filter/upstream/r_user
add wave -noupdate -expand -group upstream /tb_axi_atop_filter/upstream/r_valid
add wave -noupdate -expand -group upstream /tb_axi_atop_filter/upstream/r_ready
add wave -noupdate -expand -group downstream /tb_axi_atop_filter/downstream/aw_id
add wave -noupdate -expand -group downstream /tb_axi_atop_filter/downstream/aw_addr
add wave -noupdate -expand -group downstream /tb_axi_atop_filter/downstream/aw_len
add wave -noupdate -expand -group downstream /tb_axi_atop_filter/downstream/aw_size
add wave -noupdate -expand -group downstream /tb_axi_atop_filter/downstream/aw_burst
add wave -noupdate -expand -group downstream /tb_axi_atop_filter/downstream/aw_lock
add wave -noupdate -expand -group downstream /tb_axi_atop_filter/downstream/aw_cache
add wave -noupdate -expand -group downstream /tb_axi_atop_filter/downstream/aw_prot
add wave -noupdate -expand -group downstream /tb_axi_atop_filter/downstream/aw_qos
add wave -noupdate -expand -group downstream /tb_axi_atop_filter/downstream/aw_region
add wave -noupdate -expand -group downstream /tb_axi_atop_filter/downstream/aw_atop
add wave -noupdate -expand -group downstream /tb_axi_atop_filter/downstream/aw_user
add wave -noupdate -expand -group downstream /tb_axi_atop_filter/downstream/aw_valid
add wave -noupdate -expand -group downstream /tb_axi_atop_filter/downstream/aw_ready
add wave -noupdate -expand -group downstream /tb_axi_atop_filter/downstream/w_data
add wave -noupdate -expand -group downstream /tb_axi_atop_filter/downstream/w_strb
add wave -noupdate -expand -group downstream /tb_axi_atop_filter/downstream/w_last
add wave -noupdate -expand -group downstream /tb_axi_atop_filter/downstream/w_user
add wave -noupdate -expand -group downstream /tb_axi_atop_filter/downstream/w_valid
add wave -noupdate -expand -group downstream /tb_axi_atop_filter/downstream/w_ready
add wave -noupdate -expand -group downstream /tb_axi_atop_filter/downstream/b_id
add wave -noupdate -expand -group downstream /tb_axi_atop_filter/downstream/b_resp
add wave -noupdate -expand -group downstream /tb_axi_atop_filter/downstream/b_user
add wave -noupdate -expand -group downstream /tb_axi_atop_filter/downstream/b_valid
add wave -noupdate -expand -group downstream /tb_axi_atop_filter/downstream/b_ready
add wave -noupdate -expand -group downstream /tb_axi_atop_filter/downstream/ar_id
add wave -noupdate -expand -group downstream /tb_axi_atop_filter/downstream/ar_addr
add wave -noupdate -expand -group downstream /tb_axi_atop_filter/downstream/ar_len
add wave -noupdate -expand -group downstream /tb_axi_atop_filter/downstream/ar_size
add wave -noupdate -expand -group downstream /tb_axi_atop_filter/downstream/ar_burst
add wave -noupdate -expand -group downstream /tb_axi_atop_filter/downstream/ar_lock
add wave -noupdate -expand -group downstream /tb_axi_atop_filter/downstream/ar_cache
add wave -noupdate -expand -group downstream /tb_axi_atop_filter/downstream/ar_prot
add wave -noupdate -expand -group downstream /tb_axi_atop_filter/downstream/ar_qos
add wave -noupdate -expand -group downstream /tb_axi_atop_filter/downstream/ar_region
add wave -noupdate -expand -group downstream /tb_axi_atop_filter/downstream/ar_user
add wave -noupdate -expand -group downstream /tb_axi_atop_filter/downstream/ar_valid
add wave -noupdate -expand -group downstream /tb_axi_atop_filter/downstream/ar_ready
add wave -noupdate -expand -group downstream /tb_axi_atop_filter/downstream/r_id
add wave -noupdate -expand -group downstream /tb_axi_atop_filter/downstream/r_data
add wave -noupdate -expand -group downstream /tb_axi_atop_filter/downstream/r_resp
add wave -noupdate -expand -group downstream /tb_axi_atop_filter/downstream/r_last
add wave -noupdate -expand -group downstream /tb_axi_atop_filter/downstream/r_user
add wave -noupdate -expand -group downstream /tb_axi_atop_filter/downstream/r_valid
add wave -noupdate -expand -group downstream /tb_axi_atop_filter/downstream/r_ready
TreeUpdate [SetDefaultTree]
configure wave -namecolwidth 150
configure wave -valuecolwidth 100
configure wave -justifyvalue left
configure wave -signalnamewidth 1
configure wave -snapdistance 10
configure wave -datasetprefix 0
configure wave -rowmargin 4
configure wave -childrowmargin 2
configure wave -gridoffset 0
configure wave -gridperiod 1
configure wave -griddelta 40
configure wave -timeline 0
configure wave -timelineunits ns
update
