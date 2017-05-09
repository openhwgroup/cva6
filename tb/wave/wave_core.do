add wave -noupdate -group instr_if /core_tb/instr_if/*

add wave -noupdate -group Core /core_tb/dut/clk_i
add wave -noupdate -group Core /core_tb/dut/clock_en_i
add wave -noupdate -group Core /core_tb/dut/test_en_i
add wave -noupdate -group Core /core_tb/dut/fetch_enable_i
add wave -noupdate -group Core /core_tb/dut/core_busy_o
add wave -noupdate -group Core /core_tb/dut/ext_perf_counters_i
add wave -noupdate -group Core /core_tb/dut/boot_addr_i
add wave -noupdate -group Core /core_tb/dut/core_id_i
add wave -noupdate -group Core /core_tb/dut/cluster_id_i
add wave -noupdate -group Core /core_tb/dut/irq_i
add wave -noupdate -group Core /core_tb/dut/irq_id_i
add wave -noupdate -group Core /core_tb/dut/irq_ack_o
add wave -noupdate -group Core /core_tb/dut/irq_sec_i
add wave -noupdate -group Core /core_tb/dut/sec_lvl_o

add wave -noupdate -group pcgen_stage -group btb /core_tb/dut/pcgen_i/btb_i/*
add wave -noupdate -group pcgen_stage /core_tb/dut/pcgen_i/*
add wave -noupdate -group if_stage -group prefetch_buffer -group fifo /core_tb/dut/if_stage_i/prefetch_buffer_i/fifo_i/*
add wave -noupdate -group if_stage -group prefetch_buffer /core_tb/dut/if_stage_i/prefetch_buffer_i/*
add wave -noupdate -group if_stage /core_tb/dut/if_stage_i/*
add wave -noupdate -group id_stage -group scoreboard /core_tb/dut/id_stage_i/scoreboard_i/*
add wave -noupdate -group id_stage -group decoder /core_tb/dut/id_stage_i/decoder_i/*
add wave -noupdate -group id_stage -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/*
add wave -noupdate -group ex_stage -group ALU /core_tb/dut/ex_stage_i/alu_i/*
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/*
add wave -noupdate -group ex_stage -expand -group csr_buffer /core_tb/dut/ex_stage_i/csr_buffer_i/*
add wave -noupdate -group ex_stage /core_tb/dut/ex_stage_i/*
add wave -noupdate -group commit_stage /core_tb/dut/commit_stage_i/*
add wave -noupdate -group csr_file /core_tb/dut/csr_regfile_i/*

TreeUpdate [SetDefaultTree]
