onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /store_queue_tb/dut/clk_i
add wave -noupdate /store_queue_tb/dut/rst_ni
add wave -noupdate /store_queue_tb/dut/flush_i
add wave -noupdate /store_queue_tb/dut/paddr_o
add wave -noupdate /store_queue_tb/dut/data_o
add wave -noupdate /store_queue_tb/dut/valid_o
add wave -noupdate /store_queue_tb/dut/be_o
add wave -noupdate /store_queue_tb/dut/commit_i
add wave -noupdate /store_queue_tb/dut/ready_o
add wave -noupdate /store_queue_tb/dut/valid_i
add wave -noupdate /store_queue_tb/dut/paddr_i
add wave -noupdate /store_queue_tb/dut/data_i
add wave -noupdate /store_queue_tb/dut/be_i
add wave -noupdate /store_queue_tb/dut/address_o
add wave -noupdate /store_queue_tb/dut/data_wdata_o
add wave -noupdate /store_queue_tb/dut/data_req_o
add wave -noupdate /store_queue_tb/dut/data_we_o
add wave -noupdate /store_queue_tb/dut/data_be_o
add wave -noupdate /store_queue_tb/dut/data_gnt_i
add wave -noupdate /store_queue_tb/dut/data_rvalid_i
add wave -noupdate /store_queue_tb/dut/CS
add wave -noupdate /store_queue_tb/dut/NS
add wave -noupdate /store_queue_tb/dut/commit_queue_n
add wave -noupdate /store_queue_tb/dut/commit_queue_q
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {0 ns} 0}
quietly wave cursor active 0
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
WaveRestoreZoom {0 ns} {13479 ns}
