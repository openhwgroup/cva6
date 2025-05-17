onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -divider {Address Input}
add wave -noupdate -label {INPUT ADDRESS} /addr_decode_tb/i_addr_decode_dut/addr_i
add wave -noupdate -label {ADDRESS MAP} /addr_decode_tb/i_addr_decode_dut/addr_map_i
add wave -noupdate -divider {Index output}
add wave -noupdate -label {DECODED INDEX} /addr_decode_tb/i_addr_decode_dut/idx_o
add wave -noupdate -label {DECODE VALID} /addr_decode_tb/i_addr_decode_dut/dec_valid_o
add wave -noupdate -label {DECODE ERROR} /addr_decode_tb/i_addr_decode_dut/dec_error_o
add wave -noupdate -divider {Default decode input}
add wave -noupdate -label {DEFAULT ENABLE} /addr_decode_tb/i_addr_decode_dut/en_default_idx_i
add wave -noupdate -label {DEFAULT INDEX} /addr_decode_tb/i_addr_decode_dut/default_idx_i
add wave -noupdate -divider {Matched rules}
add wave -noupdate -label {MATCHED RULES} /addr_decode_tb/i_addr_decode_dut/matched_rules
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {0 ns} 0}
quietly wave cursor active 0
configure wave -namecolwidth 146
configure wave -valuecolwidth 100
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
WaveRestoreZoom {0 ns} {22958 ns}
