onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /id_queue_tb/dut/clk_i
add wave -noupdate /id_queue_tb/dut/rst_ni
add wave -noupdate -expand -group inp /id_queue_tb/dut/inp_req_i
add wave -noupdate -expand -group inp /id_queue_tb/dut/inp_gnt_o
add wave -noupdate -expand -group inp /id_queue_tb/dut/inp_id_i
add wave -noupdate -expand -group inp /id_queue_tb/dut/inp_data_i
add wave -noupdate -expand -group exists /id_queue_tb/dut/exists_req_i
add wave -noupdate -expand -group exists /id_queue_tb/dut/exists_gnt_o
add wave -noupdate -expand -group exists /id_queue_tb/dut/exists_data_i
add wave -noupdate -expand -group exists /id_queue_tb/dut/exists_mask_i
add wave -noupdate -expand -group exists /id_queue_tb/dut/exists_o
add wave -noupdate -expand -group oup /id_queue_tb/dut/oup_req_i
add wave -noupdate -expand -group oup /id_queue_tb/dut/oup_gnt_o
add wave -noupdate -expand -group oup /id_queue_tb/dut/oup_id_i
add wave -noupdate -expand -group oup /id_queue_tb/dut/oup_pop_i
add wave -noupdate -expand -group oup /id_queue_tb/dut/oup_data_o
add wave -noupdate -expand -group oup /id_queue_tb/dut/oup_data_valid_o
add wave -noupdate -expand -group internals /id_queue_tb/dut/head_tail_q
add wave -noupdate -expand -group internals /id_queue_tb/dut/linked_data_q
add wave -noupdate -expand -group internals /id_queue_tb/dut/full
add wave -noupdate -expand -group internals /id_queue_tb/dut/no_id_match
add wave -noupdate -expand -group internals /id_queue_tb/dut/head_tail_free
add wave -noupdate -expand -group internals /id_queue_tb/dut/idx_matches_id
add wave -noupdate -expand -group internals /id_queue_tb/dut/exists_match
add wave -noupdate -expand -group internals /id_queue_tb/dut/linked_data_free
add wave -noupdate -expand -group internals /id_queue_tb/dut/match_id
add wave -noupdate -expand -group internals /id_queue_tb/dut/head_tail_free_idx
add wave -noupdate -expand -group internals /id_queue_tb/dut/match_idx
add wave -noupdate -expand -group internals /id_queue_tb/dut/linked_data_free_idx
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {0 ps} 0}
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
