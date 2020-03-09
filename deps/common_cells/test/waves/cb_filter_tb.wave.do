log -r /*

add wave -position end -label Clock -color "light blue"  sim:/cb_filter_tb/i_dut/clk_i
add wave -position end -label Reset -color "orange"      sim:/cb_filter_tb/i_dut/rst_ni

add wave -position end -divider "Lookup Hashes"
add wave -position end -label LOOK_DATA      -color "green" sim:/cb_filter_tb/i_dut/i_look_hashes/data_i
add wave -position end -label LOOK_HASH      -color "pink"  sim:/cb_filter_tb/i_dut/i_look_hashes/hashes
add wave -position end -label LOOKUP_VALID_O -color "blue"  sim:/cb_filter_tb/i_dut/look_valid_o


add wave -position end -divider "Increment Hashes"
add wave -position end -label INCR_DATA  -color "green" sim:/cb_filter_tb/i_dut/i_incr_hashes/data_i
add wave -position end -label INCR_VALID -color "blue"  sim:/cb_filter_tb/i_dut/incr_valid_i
add wave -position end -label INCR_HASH  -color "pink"  sim:/cb_filter_tb/i_dut/i_incr_hashes/hashes
add wave -position end -label INCR_IND   -color "pink"  sim:/cb_filter_tb/i_dut/i_incr_hashes/indicator_o


add wave -position end -divider "Decrement Hashes"
add wave -position end -label DECR_DATA  -color "green" sim:/cb_filter_tb/i_dut/i_decr_hashes/data_i
add wave -position end -label DECR_VALID -color "blue"  sim:/cb_filter_tb/i_dut/decr_valid_i
add wave -position end -label DECR_HASH  -color "pink"  sim:/cb_filter_tb/i_dut/i_decr_hashes/hashes
add wave -position end -label DECR_IND   -color "pink"  sim:/cb_filter_tb/i_dut/i_incr_hashes/indicator_o

add wave -position end -divider "Filter Flags"
add wave -position end -label OCCUPIED  -color "orange"   sim:/cb_filter_tb/i_dut/bucket_occupied
add wave -position end -label USAGE     -color "pink"     sim:/cb_filter_tb/i_dut/filter_usage_o
add wave -position end -label FULL      -color "magenta"  sim:/cb_filter_tb/i_dut/filter_full_o
add wave -position end -label EMPTY     -color "green"    sim:/cb_filter_tb/i_dut/filter_empty_o
add wave -position end -label ERROR     -color "red"      sim:/cb_filter_tb/i_dut/filter_error_o
