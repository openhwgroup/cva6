# remove previous library
sh rm -rf WORK/*
remove_design -design

# set multithreading
set disable_multicore_resource_checks true
set NumberThreads [exec cat /proc/cpuinfo | grep -c processor]
set_host_options -max_cores $NumberThreads

# This script was generated automatically by bender.
set search_path_initial $search_path
set ROOT "/home/scmoritz/Documents/platformsec/iopmp"

set search_path $search_path_initial
lappend search_path "$ROOT/include"

analyze -format sv \
    [list \
        "$ROOT/include/pmp_pkg.sv" \
        "$ROOT/src/napot_extract.sv" \
        "$ROOT/src/pmp_napot_entry.sv" \
        "$ROOT/src/pmp_tor_entry.sv" \
        "$ROOT/src/pmp_na4_entry.sv" \
        "$ROOT/src/pmp_entry.sv" \
        "$ROOT/src/pmp.sv" \
    ]

set search_path $search_path_initial

elaborate pmp

# Constraints
set_max_delay -to [all_outputs] 200
set_max_area 0
set_load 0.1 [all_outputs]
set_max_fanout 1 [all_inputs]
set_fanout_load 8 [all_outputs]

compile_ultra

report_timing