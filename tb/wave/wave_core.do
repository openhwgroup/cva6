add wave -noupdate -group core /cva6_tb/dut/i_cva6/*

add wave -noupdate -group frontend /cva6_tb/dut/i_cva6/i_frontend/*
add wave -noupdate -group frontend -group icache /cva6_tb/dut/i_cva6/i_std_cache_subsystem/i_icache/*
add wave -noupdate -group frontend -group ras /cva6_tb/dut/i_cva6/i_frontend/i_ras/*
add wave -noupdate -group frontend -group btb /cva6_tb/dut/i_cva6/i_frontend/i_btb/*
add wave -noupdate -group frontend -group bht /cva6_tb/dut/i_cva6/i_frontend/i_bht/*
# add wave -noupdate -group frontend -group instr_scan /cva6_tb/dut/i_cva6/i_frontend/*/i_instr_scan/*
# add wave -noupdate -group frontend -group fetch_fifo /cva6_tb/dut/i_cva6/i_frontend/i_fetch_fifo/*

add wave -noupdate -group id_stage -group decoder /cva6_tb/dut/i_cva6/id_stage_i/decoder_i/*
add wave -noupdate -group id_stage -group compressed_decoder /cva6_tb/dut/i_cva6/id_stage_i/compressed_decoder_i/*
add wave -noupdate -group id_stage -group instr_realigner /cva6_tb/dut/i_cva6/id_stage_i/instr_realigner_i/*
add wave -noupdate -group id_stage /cva6_tb/dut/i_cva6/id_stage_i/*

add wave -noupdate -group issue_stage -group scoreboard /cva6_tb/dut/i_cva6/issue_stage_i/i_scoreboard/*
add wave -noupdate -group issue_stage -group issue_read_operands /cva6_tb/dut/i_cva6/issue_stage_i/i_issue_read_operands/*
add wave -noupdate -group issue_stage -group rename /cva6_tb/dut/i_cva6/issue_stage_i/i_re_name/*
add wave -noupdate -group issue_stage /cva6_tb/dut/i_cva6/issue_stage_i/*

add wave -noupdate -group ex_stage -group alu /cva6_tb/dut/i_cva6/ex_stage_i/alu_i/*
add wave -noupdate -group ex_stage -group mult /cva6_tb/dut/i_cva6/ex_stage_i/i_mult/*
add wave -noupdate -group ex_stage -group mult -group mul /cva6_tb/dut/i_cva6/ex_stage_i/i_mult/i_mul/*
add wave -noupdate -group ex_stage -group mult -group div /cva6_tb/dut/i_cva6/ex_stage_i/i_mult/i_div/*
add wave -noupdate -group ex_stage -group fpu /cva6_tb/dut/i_cva6/ex_stage_i/fpu_gen/fpu_i/*
add wave -noupdate -group ex_stage -group fpu -group fpnew /cva6_tb/dut/i_cva6/ex_stage_i/fpu_gen/fpu_i/fpnew_top_i/i_fpnew/*

add wave -noupdate -group ex_stage -group lsu /cva6_tb/dut/i_cva6/ex_stage_i/lsu_i/*
add wave -noupdate -group ex_stage -group lsu  -group lsu_bypass /cva6_tb/dut/i_cva6/ex_stage_i/lsu_i/lsu_bypass_i/*
add wave -noupdate -group ex_stage -group lsu -group mmu /cva6_tb/dut/i_cva6/ex_stage_i/lsu_i/i_mmu/*
add wave -noupdate -group ex_stage -group lsu -group mmu -group itlb /cva6_tb/dut/i_cva6/ex_stage_i/lsu_i/i_mmu/i_itlb/*
add wave -noupdate -group ex_stage -group lsu -group mmu -group dtlb /cva6_tb/dut/i_cva6/ex_stage_i/lsu_i/i_mmu/i_dtlb/*
add wave -noupdate -group ex_stage -group lsu -group mmu -group ptw /cva6_tb/dut/i_cva6/ex_stage_i/lsu_i/i_mmu/i_ptw/*

add wave -noupdate -group ex_stage -group lsu -group store_unit /cva6_tb/dut/i_cva6/ex_stage_i/lsu_i/i_store_unit/*
add wave -noupdate -group ex_stage -group lsu -group store_unit -group store_buffer /cva6_tb/dut/i_cva6/ex_stage_i/lsu_i/i_store_unit/store_buffer_i/*

add wave -noupdate -group ex_stage -group lsu -group load_unit /cva6_tb/dut/i_cva6/ex_stage_i/lsu_i/i_load_unit/*
add wave -noupdate -group ex_stage -group lsu -group lsu_arbiter /cva6_tb/dut/i_cva6/ex_stage_i/lsu_i/i_lsu_arbiter/*

add wave -noupdate -group ex_stage -group branch_unit /cva6_tb/dut/i_cva6/ex_stage_i/branch_unit_i/*

add wave -noupdate -group ex_stage -group csr_buffer /cva6_tb/dut/i_cva6/ex_stage_i/csr_buffer_i/*
add wave -noupdate -group ex_stage /cva6_tb/dut/i_cva6/ex_stage_i/*

add wave -noupdate -group commit_stage /cva6_tb/dut/i_cva6/commit_stage_i/*

add wave -noupdate -group csr_file /cva6_tb/dut/i_cva6/csr_regfile_i/*

add wave -noupdate -group controller /cva6_tb/dut/i_cva6/controller_i/*

add wave -noupdate -group nbdcache /cva6_tb/dut/i_cva6/i_std_cache_subsystem/i_nbdcache/*
add wave -noupdate -group nbdcache -group miss_handler /cva6_tb/dut/i_cva6/i_std_cache_subsystem/i_nbdcache/i_miss_handler/*

add wave -noupdate -group nbdcache -group bypass_arbiter /cva6_tb/dut/i_cva6/i_std_cache_subsystem/i_nbdcache/i_miss_handler/i_bypass_arbiter/*
add wave -noupdate -group nbdcache -group bypass_axi /cva6_tb/dut/i_cva6/i_std_cache_subsystem/i_nbdcache/i_miss_handler/i_bypass_axi_adapter/*

add wave -noupdate -group nbdcache -group miss_axi /cva6_tb/dut/i_cva6/i_std_cache_subsystem/i_nbdcache/i_miss_handler/i_miss_axi_adapter/*
add wave -noupdate -group nbdcache -group lfsr /cva6_tb/dut/i_cva6/i_std_cache_subsystem/i_nbdcache/i_miss_handler/i_lfsr/*

add wave -noupdate -group nbdcache -group dirty_ram /cva6_tb/dut/i_cva6/i_std_cache_subsystem/i_nbdcache/valid_dirty_sram/*
add wave -noupdate -group nbdcache -group tag_cmp /cva6_tb/dut/i_cva6/i_std_cache_subsystem/i_nbdcache/i_tag_cmp/*

add wave -noupdate -group nbdcache -group ptw {/cva6_tb/dut/i_cva6/i_std_cache_subsystem/i_nbdcache/master_ports[0]/i_cache_ctrl/*}
add wave -noupdate -group nbdcache -group load {/cva6_tb/dut/i_cva6/i_std_cache_subsystem/i_nbdcache/master_ports[1]/i_cache_ctrl/*}
add wave -noupdate -group nbdcache -group store {/cva6_tb/dut/i_cva6/i_std_cache_subsystem/i_nbdcache/master_ports[2]/i_cache_ctrl/*}

add wave -noupdate -group perf_counters /cva6_tb/dut/i_cva6/i_perf_counters/*

add wave -noupdate -group dm_top /cva6_tb/dut/i_dm_top/*
add wave -noupdate -group dm_top -group dm_csrs /cva6_tb/dut/i_dm_top/i_dm_csrs/*
add wave -noupdate -group dm_top -group dm_mem /cva6_tb/dut/i_dm_top/i_dm_mem/*

add wave -noupdate -group bootrom /cva6_tb/dut/i_bootrom/*

add wave -noupdate -group tracer_if /cva6_tb/dut/i_cva6/instr_tracer_i/tracer_if/*

add wave -group SimJTAG /cva6_tb/dut/i_SimJTAG/*

add wave -group dmi_jtag /cva6_tb/dut/i_dmi_jtag/*
add wave -group dmi_jtag -group dmi_jtag_tap /cva6_tb/dut/i_dmi_jtag/i_dmi_jtag_tap/*
add wave -group dmi_jtag -group dmi_cdc /cva6_tb/dut/i_dmi_jtag/i_dmi_cdc/*