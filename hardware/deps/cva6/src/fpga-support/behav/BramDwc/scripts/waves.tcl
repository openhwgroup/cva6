quietly WaveActivateNextPane {} 0

configure wave -signalnamewidth 1

delete wave *

add wave -noupdate /Testbench/Clk_C
add wave -noupdate /Testbench/Rst_RB
add wave -noupdate /Testbench/EndOfSim_S

add wave -noupdate -expand -group Bram_PM /Testbench/Bram_PM/*
add wave -noupdate -expand -group Bram_PS /Testbench/Bram_PS/*
add wave -noupdate -expand /Testbench/ExpResp

update

# vim: syntax=tcl
