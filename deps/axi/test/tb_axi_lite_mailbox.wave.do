log -r /*
onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /tb_axi_lite_mailbox/i_mailbox_dut/i_axi_lite_mailbox/clk_i
add wave -noupdate /tb_axi_lite_mailbox/i_mailbox_dut/i_axi_lite_mailbox/rst_ni
add wave -noupdate /tb_axi_lite_mailbox/i_mailbox_dut/i_axi_lite_mailbox/test_i
add wave -noupdate -divider Ports
add wave -noupdate /tb_axi_lite_mailbox/i_mailbox_dut/i_axi_lite_mailbox/slv_reqs_i
add wave -noupdate /tb_axi_lite_mailbox/i_mailbox_dut/i_axi_lite_mailbox/slv_resps_o
add wave -noupdate -divider IRQ
add wave -noupdate /tb_axi_lite_mailbox/i_mailbox_dut/i_axi_lite_mailbox/irq_o
add wave -noupdate -divider {Mailbox FIFO status}
add wave -noupdate /tb_axi_lite_mailbox/i_mailbox_dut/i_axi_lite_mailbox/mbox_full
add wave -noupdate /tb_axi_lite_mailbox/i_mailbox_dut/i_axi_lite_mailbox/mbox_empty
add wave -noupdate /tb_axi_lite_mailbox/i_mailbox_dut/i_axi_lite_mailbox/mbox_push
add wave -noupdate /tb_axi_lite_mailbox/i_mailbox_dut/i_axi_lite_mailbox/mbox_pop
add wave -noupdate /tb_axi_lite_mailbox/i_mailbox_dut/i_axi_lite_mailbox/w_mbox_flush
add wave -noupdate /tb_axi_lite_mailbox/i_mailbox_dut/i_axi_lite_mailbox/r_mbox_flush
add wave -noupdate /tb_axi_lite_mailbox/i_mailbox_dut/i_axi_lite_mailbox/mbox_w_data
add wave -noupdate /tb_axi_lite_mailbox/i_mailbox_dut/i_axi_lite_mailbox/mbox_r_data
add wave -noupdate /tb_axi_lite_mailbox/i_mailbox_dut/i_axi_lite_mailbox/mbox_usage
add wave -noupdate -divider {Port 0 internal}
add wave -noupdate /tb_axi_lite_mailbox/i_mailbox_dut/i_axi_lite_mailbox/i_slv_port_0/w_reg_idx
add wave -noupdate /tb_axi_lite_mailbox/i_mailbox_dut/i_axi_lite_mailbox/i_slv_port_0/r_reg_idx
add wave -noupdate /tb_axi_lite_mailbox/i_mailbox_dut/i_axi_lite_mailbox/i_slv_port_0/status_q
add wave -noupdate /tb_axi_lite_mailbox/i_mailbox_dut/i_axi_lite_mailbox/i_slv_port_0/error_q
add wave -noupdate /tb_axi_lite_mailbox/i_mailbox_dut/i_axi_lite_mailbox/i_slv_port_0/wirqt_q
add wave -noupdate /tb_axi_lite_mailbox/i_mailbox_dut/i_axi_lite_mailbox/i_slv_port_0/rirqt_q
add wave -noupdate /tb_axi_lite_mailbox/i_mailbox_dut/i_axi_lite_mailbox/i_slv_port_0/irqs_q
add wave -noupdate /tb_axi_lite_mailbox/i_mailbox_dut/i_axi_lite_mailbox/i_slv_port_0/irqen_q
add wave -noupdate /tb_axi_lite_mailbox/i_mailbox_dut/i_axi_lite_mailbox/i_slv_port_0/irqp_q
add wave -noupdate /tb_axi_lite_mailbox/i_mailbox_dut/i_axi_lite_mailbox/i_slv_port_0/ctrl_q
add wave -noupdate /tb_axi_lite_mailbox/i_mailbox_dut/i_axi_lite_mailbox/i_slv_port_0/update_regs
add wave -noupdate -divider {Port 1 internal}
add wave -noupdate /tb_axi_lite_mailbox/i_mailbox_dut/i_axi_lite_mailbox/i_slv_port_1/w_reg_idx
add wave -noupdate /tb_axi_lite_mailbox/i_mailbox_dut/i_axi_lite_mailbox/i_slv_port_1/r_reg_idx
add wave -noupdate /tb_axi_lite_mailbox/i_mailbox_dut/i_axi_lite_mailbox/i_slv_port_1/status_q
add wave -noupdate /tb_axi_lite_mailbox/i_mailbox_dut/i_axi_lite_mailbox/i_slv_port_1/error_q
add wave -noupdate /tb_axi_lite_mailbox/i_mailbox_dut/i_axi_lite_mailbox/i_slv_port_1/wirqt_q
add wave -noupdate /tb_axi_lite_mailbox/i_mailbox_dut/i_axi_lite_mailbox/i_slv_port_1/rirqt_q
add wave -noupdate /tb_axi_lite_mailbox/i_mailbox_dut/i_axi_lite_mailbox/i_slv_port_1/irqs_q
add wave -noupdate /tb_axi_lite_mailbox/i_mailbox_dut/i_axi_lite_mailbox/i_slv_port_1/irqen_q
add wave -noupdate /tb_axi_lite_mailbox/i_mailbox_dut/i_axi_lite_mailbox/i_slv_port_1/irqp_q
add wave -noupdate /tb_axi_lite_mailbox/i_mailbox_dut/i_axi_lite_mailbox/i_slv_port_1/ctrl_q
add wave -noupdate /tb_axi_lite_mailbox/i_mailbox_dut/i_axi_lite_mailbox/i_slv_port_1/update_regs
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {2613 ns} 0}
quietly wave cursor active 1
configure wave -namecolwidth 415
configure wave -valuecolwidth 123
configure wave -justifyvalue left
configure wave -signalnamewidth 0
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
WaveRestoreZoom {0 ns} {5103 ns}
