onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /tb/*
add wave -noupdate /tb/exp_rdata
add wave -noupdate /tb/p_mem/*
add wave -noupdate -group axi_data_dv /tb/axi_data_dv/*
add wave -noupdate -group axi_bypass_dv /tb/axi_bypass_dv/*
add wave -noupdate -divider Programs
add wave -noupdate -group Writeport /tb/i_tb_writeport/clk_i
add wave -noupdate -group Writeport /tb/i_tb_writeport/rst_ni
add wave -noupdate -group Writeport /tb/i_tb_writeport/req_rate_i
add wave -noupdate -group Writeport /tb/i_tb_writeport/seq_type_i
add wave -noupdate -group Writeport /tb/i_tb_writeport/seq_run_i
add wave -noupdate -group Writeport /tb/i_tb_writeport/seq_num_vect_i
add wave -noupdate -group Writeport /tb/i_tb_writeport/seq_last_i
add wave -noupdate -group Writeport /tb/i_tb_writeport/dut_req_port_i
add wave -noupdate -group Writeport /tb/i_tb_writeport/test_name_i
add wave -noupdate -group Writeport /tb/i_tb_writeport/paddr
add wave -noupdate -group Writeport /tb/i_tb_writeport/seq_done_o
add wave -noupdate -group Writeport /tb/i_tb_writeport/dut_req_port_o
add wave -noupdate -group {Readport 0} /tb/i_tb_readport0/clk_i
add wave -noupdate -group {Readport 0} /tb/i_tb_readport0/rst_ni
add wave -noupdate -group {Readport 0} /tb/i_tb_readport0/seq_type_i
add wave -noupdate -group {Readport 0} /tb/i_tb_readport0/seq_run_i
add wave -noupdate -group {Readport 0} /tb/i_tb_readport0/seq_num_resp_i
add wave -noupdate -group {Readport 0} /tb/i_tb_readport0/seq_last_i
add wave -noupdate -group {Readport 0} /tb/i_tb_readport0/seq_done_o
add wave -noupdate -group {Readport 0} -expand /tb/i_tb_readport0/dut_req_port_o
add wave -noupdate -group {Readport 0} -expand /tb/i_tb_readport0/dut_req_port_i
add wave -noupdate -group {Readport 0} /tb/i_tb_readport0/paddr
add wave -noupdate -group {Readport 0} /tb/i_tb_readport0/seq_end_req
add wave -noupdate -group {Readport 0} /tb/i_tb_readport0/seq_end_ack
add wave -noupdate -group {Readport 0} /tb/i_tb_readport0/tag_q
add wave -noupdate -group {Readport 0} /tb/i_tb_readport0/tag_vld_q
add wave -noupdate -group {Readport 0} /tb/i_tb_readport0/p_tag_delay/tmp_paddr
add wave -noupdate -group {Readport 0} /tb/i_tb_readport0/p_tag_delay/cnt
add wave -noupdate -group {Readport 0} /tb/i_tb_readport0/p_tag_delay/tmp_vld
add wave -noupdate -group {Readport 1} /tb/i_tb_readport1/clk_i
add wave -noupdate -group {Readport 1} /tb/i_tb_readport1/rst_ni
add wave -noupdate -group {Readport 1} /tb/i_tb_readport1/seq_type_i
add wave -noupdate -group {Readport 1} /tb/i_tb_readport1/seq_run_i
add wave -noupdate -group {Readport 1} /tb/i_tb_readport1/seq_num_resp_i
add wave -noupdate -group {Readport 1} /tb/i_tb_readport1/seq_last_i
add wave -noupdate -group {Readport 1} /tb/i_tb_readport1/seq_done_o
add wave -noupdate -group {Readport 1} -expand /tb/i_tb_readport1/dut_req_port_o
add wave -noupdate -group {Readport 1} -expand /tb/i_tb_readport1/dut_req_port_i
add wave -noupdate -group {Readport 1} /tb/i_tb_readport1/paddr
add wave -noupdate -group {Readport 1} /tb/i_tb_readport1/seq_end_req
add wave -noupdate -group {Readport 1} /tb/i_tb_readport1/seq_end_ack
add wave -noupdate -group {Readport 1} /tb/i_tb_readport1/tag_q
add wave -noupdate -group {Readport 1} /tb/i_tb_readport1/tag_vld_q
add wave -noupdate -group {Readport 1} /tb/i_tb_readport1/p_tag_delay/tmp_paddr
add wave -noupdate -group {Amoport 1} /tb/i_tb_amoport/*
add wave -noupdate -divider Modules
add wave -noupdate -expand -group i_dut /tb/i_dut/*
add wave -noupdate -group i_missunit /tb/i_dut/i_miss_handler/*
add wave -noupdate -group i_ctrl0 {/tb/i_dut/master_ports[0]/i_cache_ctrl/*}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/master_ports[1]/i_cache_ctrl/*}
add wave -noupdate -group i_ctrl2 {/tb/i_dut/master_ports[2]/i_cache_ctrl/*}
add wave -noupdate -group i_bypass_axi_adapter /tb/i_dut/i_miss_handler/i_bypass_axi_adapter/*
add wave -noupdate -group i_miss_axi_adapter /tb/i_dut/i_miss_handler/i_miss_axi_adapter/*
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {31432807547 ps} 0} {{Cursor 2} {17675291 ps} 0} {{Cursor 3} {1027790000 ps} 0}
quietly wave cursor active 2
configure wave -namecolwidth 375
configure wave -valuecolwidth 224
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
configure wave -timelineunits ps
update
WaveRestoreZoom {0 ps} {56623104 ps}
