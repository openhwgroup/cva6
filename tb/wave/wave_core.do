add wave -noupdate -group core /core_tb/dut/*
add wave -noupdate -group pcgen_stage -group btb /core_tb/dut/pcgen_i/btb_i/*
add wave -noupdate -group pcgen_stage /core_tb/dut/pcgen_i/*
add wave -noupdate -group if_stage -group fetch_fifo /core_tb/dut/if_stage_i/fetch_fifo_i/*
add wave -noupdate -group if_stage /core_tb/dut/if_stage_i/*
add wave -noupdate -group id_stage -group scoreboard /core_tb/dut/id_stage_i/scoreboard_i/*
add wave -noupdate -group id_stage -group decoder /core_tb/dut/id_stage_i/decoder_i/*
add wave -noupdate -group id_stage -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/*
add wave -noupdate -group id_stage /core_tb/dut/id_stage_i/*
add wave -noupdate -group ex_stage -group ALU /core_tb/dut/ex_stage_i/alu_i/*
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/*
add wave -noupdate -group ex_stage -group lsu -group mem_arbiter /core_tb/dut/ex_stage_i/lsu_i/dcache_arbiter_i/*
add wave -noupdate -group ex_stage -group lsu -group mem_arbiter -group arbiter_fifo /core_tb/dut/ex_stage_i/lsu_i/dcache_arbiter_i/fifo_i/*
add wave -noupdate -group ex_stage -group lsu -group store_unit /core_tb/dut/ex_stage_i/lsu_i/store_unit_i/*
add wave -noupdate -group ex_stage -group lsu -group store_unit -group store_queue /core_tb/dut/ex_stage_i/lsu_i/store_unit_i/store_queue_i/*
add wave -noupdate -group ex_stage -group lsu -group load_unit /core_tb/dut/ex_stage_i/lsu_i/load_unit_i/*
add wave -noupdate -group ex_stage -group lsu -group load_unit -group fifo /core_tb/dut/ex_stage_i/lsu_i/load_unit_i/fifo_i/*
add wave -noupdate -group ex_stage -group lsu -group lsu_arbiter /core_tb/dut/ex_stage_i/lsu_i/lsu_arbiter_i/*
add wave -noupdate -group ex_stage -group branch_unit /core_tb/dut/ex_stage_i/branch_unit_i/*
add wave -noupdate -group ex_stage -expand -group csr_buffer /core_tb/dut/ex_stage_i/csr_buffer_i/*
add wave -noupdate -group ex_stage /core_tb/dut/ex_stage_i/*
add wave -noupdate -group commit_stage /core_tb/dut/commit_stage_i/*
add wave -noupdate -group csr_file /core_tb/dut/csr_regfile_i/*
add wave -noupdate -group controller /core_tb/dut/controller_i/*
