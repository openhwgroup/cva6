onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /tb_axi_lite_xbar/i_dut/clk_i
add wave -noupdate /tb_axi_lite_xbar/i_dut/rst_ni
add wave -noupdate -expand -group {master[1]} {/tb_axi_lite_xbar/master[1]/aw_addr}
add wave -noupdate -expand -group {master[1]} {/tb_axi_lite_xbar/master[1]/aw_valid}
add wave -noupdate -expand -group {master[1]} {/tb_axi_lite_xbar/master[1]/aw_ready}
add wave -noupdate -expand -group {master[1]} {/tb_axi_lite_xbar/master[1]/w_data}
add wave -noupdate -expand -group {master[1]} {/tb_axi_lite_xbar/master[1]/w_strb}
add wave -noupdate -expand -group {master[1]} {/tb_axi_lite_xbar/master[1]/w_valid}
add wave -noupdate -expand -group {master[1]} {/tb_axi_lite_xbar/master[1]/w_ready}
add wave -noupdate -expand -group {master[1]} {/tb_axi_lite_xbar/master[1]/b_resp}
add wave -noupdate -expand -group {master[1]} {/tb_axi_lite_xbar/master[1]/b_valid}
add wave -noupdate -expand -group {master[1]} {/tb_axi_lite_xbar/master[1]/b_ready}
add wave -noupdate -expand -group {master[1]} {/tb_axi_lite_xbar/master[1]/ar_addr}
add wave -noupdate -expand -group {master[1]} {/tb_axi_lite_xbar/master[1]/ar_valid}
add wave -noupdate -expand -group {master[1]} {/tb_axi_lite_xbar/master[1]/ar_ready}
add wave -noupdate -expand -group {master[1]} {/tb_axi_lite_xbar/master[1]/r_data}
add wave -noupdate -expand -group {master[1]} {/tb_axi_lite_xbar/master[1]/r_resp}
add wave -noupdate -expand -group {master[1]} {/tb_axi_lite_xbar/master[1]/r_valid}
add wave -noupdate -expand -group {master[1]} {/tb_axi_lite_xbar/master[1]/r_ready}
add wave -noupdate -group {master[0]} {/tb_axi_lite_xbar/master[0]/aw_addr}
add wave -noupdate -group {master[0]} {/tb_axi_lite_xbar/master[0]/aw_valid}
add wave -noupdate -group {master[0]} {/tb_axi_lite_xbar/master[0]/aw_ready}
add wave -noupdate -group {master[0]} {/tb_axi_lite_xbar/master[0]/w_data}
add wave -noupdate -group {master[0]} {/tb_axi_lite_xbar/master[0]/w_strb}
add wave -noupdate -group {master[0]} {/tb_axi_lite_xbar/master[0]/w_valid}
add wave -noupdate -group {master[0]} {/tb_axi_lite_xbar/master[0]/w_ready}
add wave -noupdate -group {master[0]} {/tb_axi_lite_xbar/master[0]/b_resp}
add wave -noupdate -group {master[0]} {/tb_axi_lite_xbar/master[0]/b_valid}
add wave -noupdate -group {master[0]} {/tb_axi_lite_xbar/master[0]/b_ready}
add wave -noupdate -group {master[0]} {/tb_axi_lite_xbar/master[0]/ar_addr}
add wave -noupdate -group {master[0]} {/tb_axi_lite_xbar/master[0]/ar_valid}
add wave -noupdate -group {master[0]} {/tb_axi_lite_xbar/master[0]/ar_ready}
add wave -noupdate -group {master[0]} {/tb_axi_lite_xbar/master[0]/r_data}
add wave -noupdate -group {master[0]} {/tb_axi_lite_xbar/master[0]/r_resp}
add wave -noupdate -group {master[0]} {/tb_axi_lite_xbar/master[0]/r_valid}
add wave -noupdate -group {master[0]} {/tb_axi_lite_xbar/master[0]/r_ready}
add wave -noupdate -expand -group {slave[1]} {/tb_axi_lite_xbar/slave[1]/aw_addr}
add wave -noupdate -expand -group {slave[1]} {/tb_axi_lite_xbar/slave[1]/aw_valid}
add wave -noupdate -expand -group {slave[1]} {/tb_axi_lite_xbar/slave[1]/aw_ready}
add wave -noupdate -expand -group {slave[1]} {/tb_axi_lite_xbar/slave[1]/w_data}
add wave -noupdate -expand -group {slave[1]} {/tb_axi_lite_xbar/slave[1]/w_strb}
add wave -noupdate -expand -group {slave[1]} {/tb_axi_lite_xbar/slave[1]/w_valid}
add wave -noupdate -expand -group {slave[1]} {/tb_axi_lite_xbar/slave[1]/w_ready}
add wave -noupdate -expand -group {slave[1]} {/tb_axi_lite_xbar/slave[1]/b_resp}
add wave -noupdate -expand -group {slave[1]} {/tb_axi_lite_xbar/slave[1]/b_valid}
add wave -noupdate -expand -group {slave[1]} {/tb_axi_lite_xbar/slave[1]/b_ready}
add wave -noupdate -expand -group {slave[1]} {/tb_axi_lite_xbar/slave[1]/ar_addr}
add wave -noupdate -expand -group {slave[1]} {/tb_axi_lite_xbar/slave[1]/ar_valid}
add wave -noupdate -expand -group {slave[1]} {/tb_axi_lite_xbar/slave[1]/ar_ready}
add wave -noupdate -expand -group {slave[1]} {/tb_axi_lite_xbar/slave[1]/r_data}
add wave -noupdate -expand -group {slave[1]} {/tb_axi_lite_xbar/slave[1]/r_resp}
add wave -noupdate -expand -group {slave[1]} {/tb_axi_lite_xbar/slave[1]/r_valid}
add wave -noupdate -expand -group {slave[1]} {/tb_axi_lite_xbar/slave[1]/r_ready}
add wave -noupdate -group {slave[0]} {/tb_axi_lite_xbar/slave[0]/aw_addr}
add wave -noupdate -group {slave[0]} {/tb_axi_lite_xbar/slave[0]/aw_valid}
add wave -noupdate -group {slave[0]} {/tb_axi_lite_xbar/slave[0]/aw_ready}
add wave -noupdate -group {slave[0]} {/tb_axi_lite_xbar/slave[0]/w_data}
add wave -noupdate -group {slave[0]} {/tb_axi_lite_xbar/slave[0]/w_strb}
add wave -noupdate -group {slave[0]} {/tb_axi_lite_xbar/slave[0]/w_valid}
add wave -noupdate -group {slave[0]} {/tb_axi_lite_xbar/slave[0]/w_ready}
add wave -noupdate -group {slave[0]} {/tb_axi_lite_xbar/slave[0]/b_resp}
add wave -noupdate -group {slave[0]} {/tb_axi_lite_xbar/slave[0]/b_valid}
add wave -noupdate -group {slave[0]} {/tb_axi_lite_xbar/slave[0]/b_ready}
add wave -noupdate -group {slave[0]} {/tb_axi_lite_xbar/slave[0]/ar_addr}
add wave -noupdate -group {slave[0]} {/tb_axi_lite_xbar/slave[0]/ar_valid}
add wave -noupdate -group {slave[0]} {/tb_axi_lite_xbar/slave[0]/ar_ready}
add wave -noupdate -group {slave[0]} {/tb_axi_lite_xbar/slave[0]/r_data}
add wave -noupdate -group {slave[0]} {/tb_axi_lite_xbar/slave[0]/r_resp}
add wave -noupdate -group {slave[0]} {/tb_axi_lite_xbar/slave[0]/r_valid}
add wave -noupdate -group {slave[0]} {/tb_axi_lite_xbar/slave[0]/r_ready}
add wave -noupdate /tb_axi_lite_xbar/routing/rules
add wave -noupdate -group {dut arb} /tb_axi_lite_xbar/i_dut/s_arb_rd/in_req
add wave -noupdate -group {dut arb} /tb_axi_lite_xbar/i_dut/s_arb_rd/in_ack
add wave -noupdate -group {dut arb} /tb_axi_lite_xbar/i_dut/s_arb_rd/out_req
add wave -noupdate -group {dut arb} /tb_axi_lite_xbar/i_dut/s_arb_rd/out_ack
add wave -noupdate -group {dut arb} /tb_axi_lite_xbar/i_dut/s_arb_rd/out_sel
add wave -noupdate -group {dut arb} /tb_axi_lite_xbar/i_dut/s_arb_wr/in_req
add wave -noupdate -group {dut arb} /tb_axi_lite_xbar/i_dut/s_arb_wr/in_ack
add wave -noupdate -group {dut arb} /tb_axi_lite_xbar/i_dut/s_arb_wr/out_req
add wave -noupdate -group {dut arb} /tb_axi_lite_xbar/i_dut/s_arb_wr/out_ack
add wave -noupdate -group {dut arb} /tb_axi_lite_xbar/i_dut/s_arb_wr/out_sel
add wave -noupdate -group {rd addr resolver} /tb_axi_lite_xbar/i_dut/i_simple/i_rd_resolver/addr_i
add wave -noupdate -group {rd addr resolver} /tb_axi_lite_xbar/i_dut/i_simple/i_rd_resolver/match_idx_o
add wave -noupdate -group {rd addr resolver} /tb_axi_lite_xbar/i_dut/i_simple/i_rd_resolver/match_ok_o
add wave -noupdate -group {rd addr resolver} /tb_axi_lite_xbar/i_dut/i_simple/i_rd_resolver/matched_rules
add wave -noupdate -group {rd addr resolver} /tb_axi_lite_xbar/i_dut/i_simple/i_rd_resolver/matched_slaves
add wave -noupdate -group {wr addr resolver} /tb_axi_lite_xbar/i_dut/i_simple/i_wr_resolver/addr_i
add wave -noupdate -group {wr addr resolver} /tb_axi_lite_xbar/i_dut/i_simple/i_wr_resolver/match_idx_o
add wave -noupdate -group {wr addr resolver} /tb_axi_lite_xbar/i_dut/i_simple/i_wr_resolver/match_ok_o
add wave -noupdate -group {wr addr resolver} /tb_axi_lite_xbar/i_dut/i_simple/i_wr_resolver/matched_rules
add wave -noupdate -group {wr addr resolver} /tb_axi_lite_xbar/i_dut/i_simple/i_wr_resolver/matched_slaves
add wave -noupdate /tb_axi_lite_xbar/i_dut/i_simple/tag_rd_q
add wave -noupdate /tb_axi_lite_xbar/i_dut/i_simple/tag_wr_q
add wave -noupdate /tb_axi_lite_xbar/i_dut/i_simple/tag_rd_d
add wave -noupdate /tb_axi_lite_xbar/i_dut/i_simple/tag_wr_d
add wave -noupdate /tb_axi_lite_xbar/i_dut/i_simple/state_rd_q
add wave -noupdate /tb_axi_lite_xbar/i_dut/i_simple/state_wr_q
add wave -noupdate /tb_axi_lite_xbar/i_dut/i_simple/wr_wvalid
add wave -noupdate /tb_axi_lite_xbar/i_dut/i_simple/wr_wready
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {384109 ps} 0}
quietly wave cursor active 1
configure wave -namecolwidth 439
configure wave -valuecolwidth 100
configure wave -justifyvalue left
configure wave -signalnamewidth 0
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
WaveRestoreZoom {375443 ps} {391851 ps}
