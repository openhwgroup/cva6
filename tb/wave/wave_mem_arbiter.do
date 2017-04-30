onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /mem_arbiter_tb/dut/clk_i
add wave -noupdate /mem_arbiter_tb/dut/rst_ni
add wave -noupdate /mem_arbiter_tb/dut/flush_ready_o
add wave -noupdate -expand -group Slave /mem_arbiter_tb/dut/address_o
add wave -noupdate -expand -group Slave /mem_arbiter_tb/dut/data_wdata_o
add wave -noupdate -expand -group Slave /mem_arbiter_tb/dut/data_req_o
add wave -noupdate -expand -group Slave /mem_arbiter_tb/dut/data_we_o
add wave -noupdate -expand -group Slave /mem_arbiter_tb/dut/data_be_o
add wave -noupdate -expand -group Slave /mem_arbiter_tb/dut/data_gnt_i
add wave -noupdate -expand -group Slave /mem_arbiter_tb/dut/data_rvalid_i
add wave -noupdate -expand -group Slave /mem_arbiter_tb/dut/data_rdata_i
add wave -noupdate -expand -group Master /mem_arbiter_tb/dut/address_i
add wave -noupdate -expand -group Master /mem_arbiter_tb/dut/data_wdata_i
add wave -noupdate -expand -group Master -expand /mem_arbiter_tb/dut/data_req_i
add wave -noupdate -expand -group Master /mem_arbiter_tb/dut/data_we_i
add wave -noupdate -expand -group Master /mem_arbiter_tb/dut/data_be_i
add wave -noupdate -expand -group Master -expand /mem_arbiter_tb/dut/data_gnt_o
add wave -noupdate -expand -group Master -expand /mem_arbiter_tb/dut/data_rvalid_o
add wave -noupdate -expand -group Master -expand /mem_arbiter_tb/dut/data_rdata_o
add wave -noupdate /mem_arbiter_tb/dut/full_o
add wave -noupdate /mem_arbiter_tb/dut/empty_o
add wave -noupdate /mem_arbiter_tb/dut/data_i
add wave -noupdate /mem_arbiter_tb/dut/push_i
add wave -noupdate /mem_arbiter_tb/dut/data_o
add wave -noupdate /mem_arbiter_tb/dut/pop_i
add wave -noupdate -expand -group FIFO /mem_arbiter_tb/dut/fifo_i/clk_i
add wave -noupdate -expand -group FIFO /mem_arbiter_tb/dut/fifo_i/rst_ni
add wave -noupdate -expand -group FIFO /mem_arbiter_tb/dut/fifo_i/flush_i
add wave -noupdate -expand -group FIFO /mem_arbiter_tb/dut/fifo_i/full_o
add wave -noupdate -expand -group FIFO /mem_arbiter_tb/dut/fifo_i/empty_o
add wave -noupdate -expand -group FIFO /mem_arbiter_tb/dut/fifo_i/single_element_o
add wave -noupdate -expand -group FIFO /mem_arbiter_tb/dut/fifo_i/data_i
add wave -noupdate -expand -group FIFO /mem_arbiter_tb/dut/fifo_i/push_i
add wave -noupdate -expand -group FIFO /mem_arbiter_tb/dut/fifo_i/data_o
add wave -noupdate -expand -group FIFO /mem_arbiter_tb/dut/fifo_i/pop_i
add wave -noupdate -expand -group FIFO /mem_arbiter_tb/dut/fifo_i/read_pointer_n
add wave -noupdate -expand -group FIFO /mem_arbiter_tb/dut/fifo_i/read_pointer_q
add wave -noupdate -expand -group FIFO /mem_arbiter_tb/dut/fifo_i/write_pointer_n
add wave -noupdate -expand -group FIFO /mem_arbiter_tb/dut/fifo_i/write_pointer_q
add wave -noupdate -expand -group FIFO /mem_arbiter_tb/dut/fifo_i/status_cnt_n
add wave -noupdate -expand -group FIFO /mem_arbiter_tb/dut/fifo_i/status_cnt_q
add wave -noupdate -expand -group FIFO /mem_arbiter_tb/dut/fifo_i/mem_n
add wave -noupdate -expand -group FIFO /mem_arbiter_tb/dut/fifo_i/mem_q
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {421 ns} 0}
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
configure wave -gridperiod 1
configure wave -griddelta 40
configure wave -timeline 0
configure wave -timelineunits ns
update
WaveRestoreZoom {0 ns} {1050 ns}
