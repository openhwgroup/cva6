onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -group TB /tb/*
add wave -noupdate -expand -group icache /tb/dut/*
add wave -noupdate -group mem_emul /tb/i_mem_emul/*
add wave -noupdate -group tlb_emul /tb/i_tlb_emul/*
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {3047 ps} 0}
quietly wave cursor active 1
configure wave -namecolwidth 208
configure wave -valuecolwidth 420
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
WaveRestoreZoom {3049926 ps} {3050004 ps}
