log -r /*
git SetDefaultTree
onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /sub_per_hash_tb/clk
add wave -noupdate /sub_per_hash_tb/rst_n
add wave -noupdate /sub_per_hash_tb/data
add wave -noupdate /sub_per_hash_tb/hash
add wave -noupdate -expand -subitemconfig {{/sub_per_hash_tb/onehot_hash[2]} -expand {/sub_per_hash_tb/onehot_hash[1]} -expand {/sub_per_hash_tb/onehot_hash[0]} -expand} /sub_per_hash_tb/onehot_hash
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {0 ns} 0}
quietly wave cursor active 0
configure wave -namecolwidth 207
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
WaveRestoreZoom {0 ns} {42432 ns}
