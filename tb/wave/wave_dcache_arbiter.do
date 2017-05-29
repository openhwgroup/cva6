onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /dcache_arbiter_tb/dut/*
add wave -noupdate -group FIFO /dcache_arbiter_tb/dut/fifo_i/*
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
