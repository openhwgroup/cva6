add wave -noupdate -group core /core_tb/dut/*

add wave -noupdate -group pcgen_stage -group btb /core_tb/dut/pcgen_i/btb_i/*
add wave -noupdate -group pcgen_stage /core_tb/dut/pcgen_i/*

add wave -noupdate -group if_stage -group fetch_fifo /core_tb/dut/if_stage_i/fetch_fifo_i/*
add wave -noupdate -group if_stage /core_tb/dut/if_stage_i/*

add wave -noupdate -group id_stage -group decoder /core_tb/dut/id_stage_i/decoder_i/*
add wave -noupdate -group id_stage -group compressed_decoder /core_tb/dut/id_stage_i/compressed_decoder_i/*
add wave -noupdate -group id_stage -group instr_realigner /core_tb/dut/id_stage_i/instr_realigner_i/*
add wave -noupdate -group id_stage /core_tb/dut/id_stage_i/*

add wave -noupdate -group issue_stage -group scoreboard /core_tb/dut/issue_stage_i/scoreboard_i/*
add wave -noupdate -group issue_stage -group issue_read_operands /core_tb/dut/issue_stage_i/issue_read_operands_i/*
add wave -noupdate -group issue_stage /core_tb/dut/issue_stage_i/*

add wave -noupdate -group ex_stage -group alu /core_tb/dut/ex_stage_i/alu_i/*

add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/*
add wave -noupdate -group ex_stage -group lsu  -group lsu_bypass /core_tb/dut/ex_stage_i/lsu_i/lsu_bypass_i/*
add wave -noupdate -group ex_stage -group lsu -group mmu /core_tb/dut/ex_stage_i/lsu_i/mmu_i/*
add wave -noupdate -group ex_stage -group lsu -group mmu -group itlb /core_tb/dut/ex_stage_i/lsu_i/mmu_i/itlb_i/*
add wave -noupdate -group ex_stage -group lsu -group mmu -group dtlb /core_tb/dut/ex_stage_i/lsu_i/mmu_i/dtlb_i/*
add wave -noupdate -group ex_stage -group lsu -group mmu -group ptw /core_tb/dut/ex_stage_i/lsu_i/mmu_i/ptw_i/*
add wave -noupdate -group ex_stage -group lsu -group dcache_arbiter /core_tb/dut/ex_stage_i/lsu_i/dcache_arbiter_i/*
add wave -noupdate -group ex_stage -group lsu -group dcache_arbiter -group arbiter_fifo /core_tb/dut/ex_stage_i/lsu_i/dcache_arbiter_i/fifo_i/*
add wave -noupdate -group ex_stage -group lsu -group store_unit /core_tb/dut/ex_stage_i/lsu_i/store_unit_i/*
add wave -noupdate -group ex_stage -group lsu -group store_unit -group store_buffer /core_tb/dut/ex_stage_i/lsu_i/store_unit_i/store_buffer_i/*
add wave -noupdate -group ex_stage -group lsu -group load_unit /core_tb/dut/ex_stage_i/lsu_i/load_unit_i/*
add wave -noupdate -group ex_stage -group lsu -group lsu_arbiter /core_tb/dut/ex_stage_i/lsu_i/lsu_arbiter_i/*

add wave -noupdate -group ex_stage -group branch_unit /core_tb/dut/ex_stage_i/branch_unit_i/*

add wave -noupdate -group ex_stage -group csr_buffer /core_tb/dut/ex_stage_i/csr_buffer_i/*
add wave -noupdate -group ex_stage /core_tb/dut/ex_stage_i/*

add wave -noupdate -group commit_stage /core_tb/dut/commit_stage_i/*

add wave -noupdate -group csr_file /core_tb/dut/csr_regfile_i/*

add wave -noupdate -group controller /core_tb/dut/controller_i/*
