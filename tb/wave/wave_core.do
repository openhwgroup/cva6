onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -group instr_if /core_tb/instr_if/clk
add wave -noupdate -group instr_if /core_tb/instr_if/address
add wave -noupdate -group instr_if /core_tb/instr_if/data_wdata
add wave -noupdate -group instr_if /core_tb/instr_if/data_req
add wave -noupdate -group instr_if /core_tb/instr_if/data_gnt
add wave -noupdate -group instr_if /core_tb/instr_if/data_rvalid
add wave -noupdate -group instr_if /core_tb/instr_if/data_rdata
add wave -noupdate -group instr_if /core_tb/instr_if/data_we
add wave -noupdate -group instr_if /core_tb/instr_if/data_be
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
add wave -noupdate -expand -group if_stage -group prefetch_buffer -group fifo /core_tb/dut/if_stage_i/prefetch_buffer_i/fifo_i/clk
add wave -noupdate -expand -group if_stage -group prefetch_buffer -group fifo /core_tb/dut/if_stage_i/prefetch_buffer_i/fifo_i/rst_n
add wave -noupdate -expand -group if_stage -group prefetch_buffer -group fifo /core_tb/dut/if_stage_i/prefetch_buffer_i/fifo_i/clear_i
add wave -noupdate -expand -group if_stage -group prefetch_buffer -group fifo /core_tb/dut/if_stage_i/prefetch_buffer_i/fifo_i/in_addr_i
add wave -noupdate -expand -group if_stage -group prefetch_buffer -group fifo /core_tb/dut/if_stage_i/prefetch_buffer_i/fifo_i/in_rdata_i
add wave -noupdate -expand -group if_stage -group prefetch_buffer -group fifo /core_tb/dut/if_stage_i/prefetch_buffer_i/fifo_i/in_valid_i
add wave -noupdate -expand -group if_stage -group prefetch_buffer -group fifo /core_tb/dut/if_stage_i/prefetch_buffer_i/fifo_i/in_ready_o
add wave -noupdate -expand -group if_stage -group prefetch_buffer -group fifo /core_tb/dut/if_stage_i/prefetch_buffer_i/fifo_i/out_addr_o
add wave -noupdate -expand -group if_stage -group prefetch_buffer -group fifo /core_tb/dut/if_stage_i/prefetch_buffer_i/fifo_i/out_rdata_o
add wave -noupdate -expand -group if_stage -group prefetch_buffer -group fifo /core_tb/dut/if_stage_i/prefetch_buffer_i/fifo_i/out_valid_o
add wave -noupdate -expand -group if_stage -group prefetch_buffer -group fifo /core_tb/dut/if_stage_i/prefetch_buffer_i/fifo_i/out_ready_i
add wave -noupdate -expand -group if_stage -group prefetch_buffer -group fifo /core_tb/dut/if_stage_i/prefetch_buffer_i/fifo_i/out_valid_stored_o
add wave -noupdate -expand -group if_stage -group prefetch_buffer -group fifo /core_tb/dut/if_stage_i/prefetch_buffer_i/fifo_i/addr_n
add wave -noupdate -expand -group if_stage -group prefetch_buffer -group fifo /core_tb/dut/if_stage_i/prefetch_buffer_i/fifo_i/addr_int
add wave -noupdate -expand -group if_stage -group prefetch_buffer -group fifo /core_tb/dut/if_stage_i/prefetch_buffer_i/fifo_i/addr_Q
add wave -noupdate -expand -group if_stage -group prefetch_buffer -group fifo /core_tb/dut/if_stage_i/prefetch_buffer_i/fifo_i/rdata_n
add wave -noupdate -expand -group if_stage -group prefetch_buffer -group fifo /core_tb/dut/if_stage_i/prefetch_buffer_i/fifo_i/rdata_int
add wave -noupdate -expand -group if_stage -group prefetch_buffer -group fifo /core_tb/dut/if_stage_i/prefetch_buffer_i/fifo_i/rdata_Q
add wave -noupdate -expand -group if_stage -group prefetch_buffer -group fifo /core_tb/dut/if_stage_i/prefetch_buffer_i/fifo_i/valid_n
add wave -noupdate -expand -group if_stage -group prefetch_buffer -group fifo /core_tb/dut/if_stage_i/prefetch_buffer_i/fifo_i/valid_int
add wave -noupdate -expand -group if_stage -group prefetch_buffer -group fifo /core_tb/dut/if_stage_i/prefetch_buffer_i/fifo_i/valid_Q
add wave -noupdate -expand -group if_stage -group prefetch_buffer -group fifo /core_tb/dut/if_stage_i/prefetch_buffer_i/fifo_i/addr_next
add wave -noupdate -expand -group if_stage -group prefetch_buffer -group fifo /core_tb/dut/if_stage_i/prefetch_buffer_i/fifo_i/rdata
add wave -noupdate -expand -group if_stage -group prefetch_buffer -group fifo /core_tb/dut/if_stage_i/prefetch_buffer_i/fifo_i/rdata_unaligned
add wave -noupdate -expand -group if_stage -group prefetch_buffer -group fifo /core_tb/dut/if_stage_i/prefetch_buffer_i/fifo_i/valid
add wave -noupdate -expand -group if_stage -group prefetch_buffer -group fifo /core_tb/dut/if_stage_i/prefetch_buffer_i/fifo_i/valid_unaligned
add wave -noupdate -expand -group if_stage -group prefetch_buffer -group fifo /core_tb/dut/if_stage_i/prefetch_buffer_i/fifo_i/aligned_is_compressed
add wave -noupdate -expand -group if_stage -group prefetch_buffer -group fifo /core_tb/dut/if_stage_i/prefetch_buffer_i/fifo_i/unaligned_is_compressed
add wave -noupdate -expand -group if_stage -group prefetch_buffer -group fifo /core_tb/dut/if_stage_i/prefetch_buffer_i/fifo_i/aligned_is_compressed_st
add wave -noupdate -expand -group if_stage -group prefetch_buffer -group fifo /core_tb/dut/if_stage_i/prefetch_buffer_i/fifo_i/unaligned_is_compressed_st
add wave -noupdate -expand -group if_stage -group prefetch_buffer -group fifo /core_tb/dut/if_stage_i/prefetch_buffer_i/fifo_i/j
add wave -noupdate -expand -group if_stage -group prefetch_buffer /core_tb/dut/if_stage_i/prefetch_buffer_i/clk
add wave -noupdate -expand -group if_stage -group prefetch_buffer /core_tb/dut/if_stage_i/prefetch_buffer_i/rst_n
add wave -noupdate -expand -group if_stage -group prefetch_buffer /core_tb/dut/if_stage_i/prefetch_buffer_i/req_i
add wave -noupdate -expand -group if_stage -group prefetch_buffer /core_tb/dut/if_stage_i/prefetch_buffer_i/branch_i
add wave -noupdate -expand -group if_stage -group prefetch_buffer /core_tb/dut/if_stage_i/prefetch_buffer_i/addr_i
add wave -noupdate -expand -group if_stage -group prefetch_buffer /core_tb/dut/if_stage_i/prefetch_buffer_i/ready_i
add wave -noupdate -expand -group if_stage -group prefetch_buffer /core_tb/dut/if_stage_i/prefetch_buffer_i/valid_o
add wave -noupdate -expand -group if_stage -group prefetch_buffer /core_tb/dut/if_stage_i/prefetch_buffer_i/addr_o
add wave -noupdate -expand -group if_stage -group prefetch_buffer /core_tb/dut/if_stage_i/prefetch_buffer_i/rdata_o
add wave -noupdate -expand -group if_stage -group prefetch_buffer /core_tb/dut/if_stage_i/prefetch_buffer_i/instr_req_o
add wave -noupdate -expand -group if_stage -group prefetch_buffer /core_tb/dut/if_stage_i/prefetch_buffer_i/instr_gnt_i
add wave -noupdate -expand -group if_stage -group prefetch_buffer /core_tb/dut/if_stage_i/prefetch_buffer_i/instr_addr_o
add wave -noupdate -expand -group if_stage -group prefetch_buffer /core_tb/dut/if_stage_i/prefetch_buffer_i/instr_rdata_i
add wave -noupdate -expand -group if_stage -group prefetch_buffer /core_tb/dut/if_stage_i/prefetch_buffer_i/instr_rvalid_i
add wave -noupdate -expand -group if_stage -group prefetch_buffer /core_tb/dut/if_stage_i/prefetch_buffer_i/busy_o
add wave -noupdate -expand -group if_stage -group prefetch_buffer /core_tb/dut/if_stage_i/prefetch_buffer_i/CS
add wave -noupdate -expand -group if_stage -group prefetch_buffer /core_tb/dut/if_stage_i/prefetch_buffer_i/NS
add wave -noupdate -expand -group if_stage -group prefetch_buffer /core_tb/dut/if_stage_i/prefetch_buffer_i/instr_addr_q
add wave -noupdate -expand -group if_stage -group prefetch_buffer /core_tb/dut/if_stage_i/prefetch_buffer_i/fetch_addr
add wave -noupdate -expand -group if_stage -group prefetch_buffer /core_tb/dut/if_stage_i/prefetch_buffer_i/addr_valid
add wave -noupdate -expand -group if_stage -group prefetch_buffer /core_tb/dut/if_stage_i/prefetch_buffer_i/fifo_valid
add wave -noupdate -expand -group if_stage -group prefetch_buffer /core_tb/dut/if_stage_i/prefetch_buffer_i/fifo_ready
add wave -noupdate -expand -group if_stage -group prefetch_buffer /core_tb/dut/if_stage_i/prefetch_buffer_i/fifo_clear
add wave -noupdate -expand -group if_stage -group prefetch_buffer /core_tb/dut/if_stage_i/prefetch_buffer_i/valid_stored
add wave -noupdate -expand -group if_stage /core_tb/dut/if_stage_i/clk_i
add wave -noupdate -expand -group if_stage /core_tb/dut/if_stage_i/rst_ni
add wave -noupdate -expand -group if_stage /core_tb/dut/if_stage_i/flush_i
add wave -noupdate -expand -group if_stage /core_tb/dut/if_stage_i/req_i
add wave -noupdate -expand -group if_stage /core_tb/dut/if_stage_i/if_busy_o
add wave -noupdate -expand -group if_stage /core_tb/dut/if_stage_i/id_ready_i
add wave -noupdate -expand -group if_stage /core_tb/dut/if_stage_i/halt_if_i
add wave -noupdate -expand -group if_stage /core_tb/dut/if_stage_i/instr_req_o
add wave -noupdate -expand -group if_stage /core_tb/dut/if_stage_i/instr_addr_o
add wave -noupdate -expand -group if_stage /core_tb/dut/if_stage_i/instr_gnt_i
add wave -noupdate -expand -group if_stage /core_tb/dut/if_stage_i/instr_rvalid_i
add wave -noupdate -expand -group if_stage /core_tb/dut/if_stage_i/instr_rdata_i
add wave -noupdate -expand -group if_stage /core_tb/dut/if_stage_i/instr_valid_id_o
add wave -noupdate -expand -group if_stage /core_tb/dut/if_stage_i/instr_rdata_id_o
add wave -noupdate -expand -group if_stage /core_tb/dut/if_stage_i/is_compressed_id_o
add wave -noupdate -expand -group if_stage /core_tb/dut/if_stage_i/illegal_c_insn_id_o
add wave -noupdate -expand -group if_stage /core_tb/dut/if_stage_i/pc_if_o
add wave -noupdate -expand -group if_stage /core_tb/dut/if_stage_i/pc_id_o
add wave -noupdate -expand -group if_stage /core_tb/dut/if_stage_i/ex_o
add wave -noupdate -expand -group if_stage /core_tb/dut/if_stage_i/boot_addr_i
add wave -noupdate -expand -group if_stage /core_tb/dut/if_stage_i/if_ready
add wave -noupdate -expand -group if_stage /core_tb/dut/if_stage_i/if_valid
add wave -noupdate -expand -group if_stage /core_tb/dut/if_stage_i/branch_req
add wave -noupdate -expand -group if_stage /core_tb/dut/if_stage_i/valid
add wave -noupdate -expand -group if_stage /core_tb/dut/if_stage_i/prefetch_busy
add wave -noupdate -expand -group if_stage /core_tb/dut/if_stage_i/fetch_addr_n
add wave -noupdate -expand -group if_stage /core_tb/dut/if_stage_i/fetch_valid
add wave -noupdate -expand -group if_stage /core_tb/dut/if_stage_i/fetch_ready
add wave -noupdate -expand -group if_stage /core_tb/dut/if_stage_i/fetch_rdata
add wave -noupdate -expand -group if_stage /core_tb/dut/if_stage_i/fetch_addr
add wave -noupdate -expand -group if_stage /core_tb/dut/if_stage_i/offset_fsm_cs
add wave -noupdate -expand -group if_stage /core_tb/dut/if_stage_i/offset_fsm_ns
add wave -noupdate -expand -group if_stage /core_tb/dut/if_stage_i/instr_decompressed
add wave -noupdate -expand -group if_stage /core_tb/dut/if_stage_i/illegal_c_insn
add wave -noupdate -expand -group if_stage /core_tb/dut/if_stage_i/instr_compressed_int
add wave -noupdate -expand -group if_stage /core_tb/dut/if_stage_i/clear_instr_valid_i
add wave -noupdate -expand -group id_stage /core_tb/dut/id_stage_i/clk_i
add wave -noupdate -expand -group id_stage /core_tb/dut/id_stage_i/rst_ni
add wave -noupdate -expand -group id_stage /core_tb/dut/id_stage_i/test_en_i
add wave -noupdate -expand -group id_stage /core_tb/dut/id_stage_i/flush_i
add wave -noupdate -expand -group id_stage /core_tb/dut/id_stage_i/instruction_i
add wave -noupdate -expand -group id_stage /core_tb/dut/id_stage_i/instruction_valid_i
add wave -noupdate -expand -group id_stage /core_tb/dut/id_stage_i/pc_if_i
add wave -noupdate -expand -group id_stage /core_tb/dut/id_stage_i/ready_o
add wave -noupdate -expand -group id_stage /core_tb/dut/id_stage_i/operator_o
add wave -noupdate -expand -group id_stage /core_tb/dut/id_stage_i/operand_a_o
add wave -noupdate -expand -group id_stage /core_tb/dut/id_stage_i/operand_b_o
add wave -noupdate -expand -group id_stage /core_tb/dut/id_stage_i/trans_id_o
add wave -noupdate -expand -group id_stage /core_tb/dut/id_stage_i/alu_ready_i
add wave -noupdate -expand -group id_stage /core_tb/dut/id_stage_i/alu_valid_o
add wave -noupdate -expand -group id_stage /core_tb/dut/id_stage_i/lsu_ready_i
add wave -noupdate -expand -group id_stage /core_tb/dut/id_stage_i/lsu_valid_o
add wave -noupdate -expand -group id_stage /core_tb/dut/id_stage_i/mult_ready_i
add wave -noupdate -expand -group id_stage /core_tb/dut/id_stage_i/mult_valid_o
add wave -noupdate -expand -group id_stage /core_tb/dut/id_stage_i/trans_id_i
add wave -noupdate -expand -group id_stage /core_tb/dut/id_stage_i/wdata_i
add wave -noupdate -expand -group id_stage /core_tb/dut/id_stage_i/wb_valid_i
add wave -noupdate -expand -group id_stage /core_tb/dut/id_stage_i/waddr_a_i
add wave -noupdate -expand -group id_stage /core_tb/dut/id_stage_i/wdata_a_i
add wave -noupdate -expand -group id_stage /core_tb/dut/id_stage_i/we_a_i
add wave -noupdate -expand -group id_stage /core_tb/dut/id_stage_i/commit_instr_o
add wave -noupdate -expand -group id_stage /core_tb/dut/id_stage_i/commit_ack_i
add wave -noupdate -expand -group id_stage -expand -group scoreboard /core_tb/dut/id_stage_i/scoreboard_i/clk_i
add wave -noupdate -expand -group id_stage -expand -group scoreboard /core_tb/dut/id_stage_i/scoreboard_i/rst_ni
add wave -noupdate -expand -group id_stage -expand -group scoreboard /core_tb/dut/id_stage_i/scoreboard_i/full_o
add wave -noupdate -expand -group id_stage -expand -group scoreboard /core_tb/dut/id_stage_i/scoreboard_i/flush_i
add wave -noupdate -expand -group id_stage -expand -group scoreboard /core_tb/dut/id_stage_i/scoreboard_i/rd_clobber_o
add wave -noupdate -expand -group id_stage -expand -group scoreboard /core_tb/dut/id_stage_i/scoreboard_i/rs1_i
add wave -noupdate -expand -group id_stage -expand -group scoreboard /core_tb/dut/id_stage_i/scoreboard_i/rs1_o
add wave -noupdate -expand -group id_stage -expand -group scoreboard /core_tb/dut/id_stage_i/scoreboard_i/rs1_valid_o
add wave -noupdate -expand -group id_stage -expand -group scoreboard /core_tb/dut/id_stage_i/scoreboard_i/rs2_i
add wave -noupdate -expand -group id_stage -expand -group scoreboard /core_tb/dut/id_stage_i/scoreboard_i/rs2_o
add wave -noupdate -expand -group id_stage -expand -group scoreboard /core_tb/dut/id_stage_i/scoreboard_i/rs2_valid_o
add wave -noupdate -expand -group id_stage -expand -group scoreboard /core_tb/dut/id_stage_i/scoreboard_i/commit_instr_o
add wave -noupdate -expand -group id_stage -expand -group scoreboard /core_tb/dut/id_stage_i/scoreboard_i/commit_ack_i
add wave -noupdate -expand -group id_stage -expand -group scoreboard /core_tb/dut/id_stage_i/scoreboard_i/decoded_instr_i
add wave -noupdate -expand -group id_stage -expand -group scoreboard /core_tb/dut/id_stage_i/scoreboard_i/decoded_instr_valid_i
add wave -noupdate -expand -group id_stage -expand -group scoreboard /core_tb/dut/id_stage_i/scoreboard_i/issue_instr_o
add wave -noupdate -expand -group id_stage -expand -group scoreboard /core_tb/dut/id_stage_i/scoreboard_i/issue_instr_valid_o
add wave -noupdate -expand -group id_stage -expand -group scoreboard /core_tb/dut/id_stage_i/scoreboard_i/issue_ack_i
add wave -noupdate -expand -group id_stage -expand -group scoreboard /core_tb/dut/id_stage_i/scoreboard_i/trans_id_i
add wave -noupdate -expand -group id_stage -expand -group scoreboard /core_tb/dut/id_stage_i/scoreboard_i/wdata_i
add wave -noupdate -expand -group id_stage -expand -group scoreboard /core_tb/dut/id_stage_i/scoreboard_i/ex_i
add wave -noupdate -expand -group id_stage -expand -group scoreboard /core_tb/dut/id_stage_i/scoreboard_i/wb_valid_i
add wave -noupdate -expand -group id_stage -expand -group scoreboard /core_tb/dut/id_stage_i/scoreboard_i/mem_q
add wave -noupdate -expand -group id_stage -expand -group scoreboard /core_tb/dut/id_stage_i/scoreboard_i/mem_n
add wave -noupdate -expand -group id_stage -expand -group scoreboard /core_tb/dut/id_stage_i/scoreboard_i/issue_pointer_n
add wave -noupdate -expand -group id_stage -expand -group scoreboard /core_tb/dut/id_stage_i/scoreboard_i/issue_pointer_q
add wave -noupdate -expand -group id_stage -expand -group scoreboard /core_tb/dut/id_stage_i/scoreboard_i/commit_pointer_n
add wave -noupdate -expand -group id_stage -expand -group scoreboard /core_tb/dut/id_stage_i/scoreboard_i/commit_pointer_q
add wave -noupdate -expand -group id_stage -expand -group scoreboard /core_tb/dut/id_stage_i/scoreboard_i/top_pointer_n
add wave -noupdate -expand -group id_stage -expand -group scoreboard /core_tb/dut/id_stage_i/scoreboard_i/top_pointer_q
add wave -noupdate -expand -group id_stage -expand -group scoreboard /core_tb/dut/id_stage_i/scoreboard_i/top_pointer_qq
add wave -noupdate -expand -group id_stage -expand -group scoreboard /core_tb/dut/id_stage_i/scoreboard_i/pointer_overflow
add wave -noupdate -expand -group id_stage -expand -group scoreboard /core_tb/dut/id_stage_i/scoreboard_i/empty
add wave -noupdate -expand -group id_stage -expand -group scoreboard /core_tb/dut/id_stage_i/scoreboard_i/reset_condition
add wave -noupdate -expand -group id_stage -group decoder /core_tb/dut/id_stage_i/decoder_i/clk_i
add wave -noupdate -expand -group id_stage -group decoder /core_tb/dut/id_stage_i/decoder_i/rst_ni
add wave -noupdate -expand -group id_stage -group decoder /core_tb/dut/id_stage_i/decoder_i/pc_i
add wave -noupdate -expand -group id_stage -group decoder /core_tb/dut/id_stage_i/decoder_i/instruction_i
add wave -noupdate -expand -group id_stage -group decoder /core_tb/dut/id_stage_i/decoder_i/ex_i
add wave -noupdate -expand -group id_stage -group decoder /core_tb/dut/id_stage_i/decoder_i/instruction_o
add wave -noupdate -expand -group id_stage -group decoder /core_tb/dut/id_stage_i/decoder_i/instr
add wave -noupdate -expand -group id_stage -group decoder /core_tb/dut/id_stage_i/decoder_i/imm_select
add wave -noupdate -expand -group id_stage -group decoder /core_tb/dut/id_stage_i/decoder_i/imm_i_type
add wave -noupdate -expand -group id_stage -group decoder /core_tb/dut/id_stage_i/decoder_i/imm_iz_type
add wave -noupdate -expand -group id_stage -group decoder /core_tb/dut/id_stage_i/decoder_i/imm_s_type
add wave -noupdate -expand -group id_stage -group decoder /core_tb/dut/id_stage_i/decoder_i/imm_sb_type
add wave -noupdate -expand -group id_stage -group decoder /core_tb/dut/id_stage_i/decoder_i/imm_u_type
add wave -noupdate -expand -group id_stage -group decoder /core_tb/dut/id_stage_i/decoder_i/imm_uj_type
add wave -noupdate -expand -group id_stage -group decoder /core_tb/dut/id_stage_i/decoder_i/imm_z_type
add wave -noupdate -expand -group id_stage -group decoder /core_tb/dut/id_stage_i/decoder_i/imm_s2_type
add wave -noupdate -expand -group id_stage -group decoder /core_tb/dut/id_stage_i/decoder_i/imm_bi_type
add wave -noupdate -expand -group id_stage -group decoder /core_tb/dut/id_stage_i/decoder_i/imm_s3_type
add wave -noupdate -expand -group id_stage -group decoder /core_tb/dut/id_stage_i/decoder_i/imm_vs_type
add wave -noupdate -expand -group id_stage -group decoder /core_tb/dut/id_stage_i/decoder_i/imm_vu_type
add wave -noupdate -expand -group id_stage -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/clk_i
add wave -noupdate -expand -group id_stage -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/rst_ni
add wave -noupdate -expand -group id_stage -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/test_en_i
add wave -noupdate -expand -group id_stage -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/flush_i
add wave -noupdate -expand -group id_stage -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/issue_instr_i
add wave -noupdate -expand -group id_stage -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/issue_instr_valid_i
add wave -noupdate -expand -group id_stage -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/issue_ack_o
add wave -noupdate -expand -group id_stage -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/rs1_o
add wave -noupdate -expand -group id_stage -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/rs1_i
add wave -noupdate -expand -group id_stage -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/rs1_valid_i
add wave -noupdate -expand -group id_stage -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/rs2_o
add wave -noupdate -expand -group id_stage -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/rs2_i
add wave -noupdate -expand -group id_stage -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/rs2_valid_i
add wave -noupdate -expand -group id_stage -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/rd_clobber_i
add wave -noupdate -expand -group id_stage -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/operator_o
add wave -noupdate -expand -group id_stage -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/operand_a_o
add wave -noupdate -expand -group id_stage -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/operand_b_o
add wave -noupdate -expand -group id_stage -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/trans_id_o
add wave -noupdate -expand -group id_stage -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/alu_ready_i
add wave -noupdate -expand -group id_stage -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/alu_valid_o
add wave -noupdate -expand -group id_stage -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/lsu_ready_i
add wave -noupdate -expand -group id_stage -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/lsu_valid_o
add wave -noupdate -expand -group id_stage -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/mult_ready_i
add wave -noupdate -expand -group id_stage -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/mult_valid_o
add wave -noupdate -expand -group id_stage -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/waddr_a_i
add wave -noupdate -expand -group id_stage -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/wdata_a_i
add wave -noupdate -expand -group id_stage -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/we_a_i
add wave -noupdate -expand -group id_stage -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/stall
add wave -noupdate -expand -group id_stage -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/fu_busy
add wave -noupdate -expand -group id_stage -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/operand_a_regfile
add wave -noupdate -expand -group id_stage -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/operand_b_regfile
add wave -noupdate -expand -group id_stage -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/operand_a_n
add wave -noupdate -expand -group id_stage -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/operand_a_q
add wave -noupdate -expand -group id_stage -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/operand_b_n
add wave -noupdate -expand -group id_stage -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/operand_b_q
add wave -noupdate -expand -group id_stage -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/alu_valid_n
add wave -noupdate -expand -group id_stage -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/alu_valid_q
add wave -noupdate -expand -group id_stage -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/trans_id_n
add wave -noupdate -expand -group id_stage -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/trans_id_q
add wave -noupdate -expand -group id_stage -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/operator_n
add wave -noupdate -expand -group id_stage -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/operator_q
add wave -noupdate -expand -group id_stage -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/forward_rs1
add wave -noupdate -expand -group id_stage -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/forward_rs2
add wave -noupdate -group ex_stage -group ALU /core_tb/dut/ex_stage_i/alu_i/operator_i
add wave -noupdate -group ex_stage -group ALU /core_tb/dut/ex_stage_i/alu_i/operand_a_i
add wave -noupdate -group ex_stage -group ALU /core_tb/dut/ex_stage_i/alu_i/operand_b_i
add wave -noupdate -group ex_stage -group ALU /core_tb/dut/ex_stage_i/alu_i/adder_result_o
add wave -noupdate -group ex_stage -group ALU /core_tb/dut/ex_stage_i/alu_i/adder_result_ext_o
add wave -noupdate -group ex_stage -group ALU /core_tb/dut/ex_stage_i/alu_i/result_o
add wave -noupdate -group ex_stage -group ALU /core_tb/dut/ex_stage_i/alu_i/comparison_result_o
add wave -noupdate -group ex_stage -group ALU /core_tb/dut/ex_stage_i/alu_i/is_equal_result_o
add wave -noupdate -group ex_stage -group ALU /core_tb/dut/ex_stage_i/alu_i/operand_a_rev
add wave -noupdate -group ex_stage -group ALU /core_tb/dut/ex_stage_i/alu_i/operand_a_rev32
add wave -noupdate -group ex_stage -group ALU /core_tb/dut/ex_stage_i/alu_i/operand_b_neg
add wave -noupdate -group ex_stage -group ALU /core_tb/dut/ex_stage_i/alu_i/adder_op_b_negate
add wave -noupdate -group ex_stage -group ALU /core_tb/dut/ex_stage_i/alu_i/adder_in_a
add wave -noupdate -group ex_stage -group ALU /core_tb/dut/ex_stage_i/alu_i/adder_in_b
add wave -noupdate -group ex_stage -group ALU /core_tb/dut/ex_stage_i/alu_i/adder_result
add wave -noupdate -group ex_stage -group ALU /core_tb/dut/ex_stage_i/alu_i/shift_left
add wave -noupdate -group ex_stage -group ALU /core_tb/dut/ex_stage_i/alu_i/shift_arithmetic
add wave -noupdate -group ex_stage -group ALU /core_tb/dut/ex_stage_i/alu_i/shift_amt
add wave -noupdate -group ex_stage -group ALU /core_tb/dut/ex_stage_i/alu_i/shift_op_a
add wave -noupdate -group ex_stage -group ALU /core_tb/dut/ex_stage_i/alu_i/shift_op_a32
add wave -noupdate -group ex_stage -group ALU /core_tb/dut/ex_stage_i/alu_i/shift_result
add wave -noupdate -group ex_stage -group ALU /core_tb/dut/ex_stage_i/alu_i/shift_result32
add wave -noupdate -group ex_stage -group ALU /core_tb/dut/ex_stage_i/alu_i/shift_right_result
add wave -noupdate -group ex_stage -group ALU /core_tb/dut/ex_stage_i/alu_i/shift_right_result32
add wave -noupdate -group ex_stage -group ALU /core_tb/dut/ex_stage_i/alu_i/shift_left_result
add wave -noupdate -group ex_stage -group ALU /core_tb/dut/ex_stage_i/alu_i/shift_left_result32
add wave -noupdate -group ex_stage -group ALU /core_tb/dut/ex_stage_i/alu_i/shift_op_a_64
add wave -noupdate -group ex_stage -group ALU /core_tb/dut/ex_stage_i/alu_i/shift_op_a_32
add wave -noupdate -group ex_stage -group ALU /core_tb/dut/ex_stage_i/alu_i/is_equal
add wave -noupdate -group ex_stage -group ALU /core_tb/dut/ex_stage_i/alu_i/is_greater_equal
add wave -noupdate -group ex_stage -group ALU /core_tb/dut/ex_stage_i/alu_i/cmp_signed
add wave -noupdate -group ex_stage -group ALU /core_tb/dut/ex_stage_i/alu_i/cmp_result
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/clk_i
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/rst_ni
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/flush_i
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/operator_i
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/operand_a_i
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/operand_b_i
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/imm_i
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/lsu_ready_o
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/lsu_valid_i
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/trans_id_i
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/lsu_trans_id_o
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/lsu_result_o
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/lsu_valid_o
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/commit_i
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/enable_translation_i
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/fetch_req_i
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/fetch_gnt_o
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/fetch_valid_o
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/fetch_err_o
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/fetch_vaddr_i
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/fetch_rdata_o
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/priv_lvl_i
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/flag_pum_i
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/flag_mxr_i
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/pd_ppn_i
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/asid_i
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/flush_tlb_i
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/instr_if_address_o
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/instr_if_data_req_o
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/instr_if_data_be_o
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/instr_if_data_gnt_i
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/instr_if_data_rvalid_i
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/instr_if_data_rdata_i
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/data_if_address_o
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/data_if_data_wdata_o
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/data_if_data_req_o
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/data_if_data_we_o
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/data_if_data_be_o
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/data_if_data_gnt_i
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/data_if_data_rvalid_i
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/data_if_data_rdata_i
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/lsu_exception_o
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/data_misaligned
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/CS
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/NS
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/vaddr_i
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/stall
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/get_from_register
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/vaddr
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/data
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/be
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/operator
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/trans_id
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/vaddr_q
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/data_q
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/operator_q
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/trans_id_q
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/st_buffer_paddr
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/st_buffer_data
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/st_buffer_be
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/st_buffer_valid
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/st_ready
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/st_valid
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/translation_req
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/translation_valid
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/paddr_o
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/address_i
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/data_wdata_i
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/data_req_i
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/data_we_i
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/data_be_i
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/data_gnt_o
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/data_rvalid_o
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/data_rdata_o
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/rdata
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/address_match
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/op
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/rdata_d_ext
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/rdata_w_ext
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/rdata_h_ext
add wave -noupdate -group ex_stage -group lsu /core_tb/dut/ex_stage_i/lsu_i/rdata_b_ext
add wave -noupdate -group ex_stage -group csr_buffer /core_tb/dut/ex_stage_i/csr_buffer_i/clk_i
add wave -noupdate -group ex_stage -group csr_buffer /core_tb/dut/ex_stage_i/csr_buffer_i/rst_ni
add wave -noupdate -group ex_stage -group csr_buffer /core_tb/dut/ex_stage_i/csr_buffer_i/flush_i
add wave -noupdate -group ex_stage -group csr_buffer /core_tb/dut/ex_stage_i/csr_buffer_i/operator_i
add wave -noupdate -group ex_stage -group csr_buffer /core_tb/dut/ex_stage_i/csr_buffer_i/operand_a_i
add wave -noupdate -group ex_stage -group csr_buffer /core_tb/dut/ex_stage_i/csr_buffer_i/operand_b_i
add wave -noupdate -group ex_stage -group csr_buffer /core_tb/dut/ex_stage_i/csr_buffer_i/trans_id_i
add wave -noupdate -group ex_stage -group csr_buffer /core_tb/dut/ex_stage_i/csr_buffer_i/csr_ready_o
add wave -noupdate -group ex_stage -group csr_buffer /core_tb/dut/ex_stage_i/csr_buffer_i/csr_valid_i
add wave -noupdate -group ex_stage -group csr_buffer /core_tb/dut/ex_stage_i/csr_buffer_i/csr_trans_id_o
add wave -noupdate -group ex_stage -group csr_buffer /core_tb/dut/ex_stage_i/csr_buffer_i/csr_result_o
add wave -noupdate -group ex_stage -group csr_buffer /core_tb/dut/ex_stage_i/csr_buffer_i/csr_valid_o
add wave -noupdate -group ex_stage -group csr_buffer /core_tb/dut/ex_stage_i/csr_buffer_i/commit_i
add wave -noupdate -group ex_stage -group csr_buffer /core_tb/dut/ex_stage_i/csr_buffer_i/csr_addr_o
add wave -noupdate -group ex_stage -group csr_buffer /core_tb/dut/ex_stage_i/csr_buffer_i/csr_reg_n
add wave -noupdate -group ex_stage -group csr_buffer /core_tb/dut/ex_stage_i/csr_buffer_i/csr_reg_q
add wave -noupdate -group ex_stage /core_tb/dut/ex_stage_i/clk_i
add wave -noupdate -group ex_stage /core_tb/dut/ex_stage_i/rst_ni
add wave -noupdate -group ex_stage /core_tb/dut/ex_stage_i/operator_i
add wave -noupdate -group ex_stage /core_tb/dut/ex_stage_i/operand_a_i
add wave -noupdate -group ex_stage /core_tb/dut/ex_stage_i/operand_b_i
add wave -noupdate -group ex_stage /core_tb/dut/ex_stage_i/trans_id_i
add wave -noupdate -group ex_stage /core_tb/dut/ex_stage_i/alu_ready_o
add wave -noupdate -group ex_stage /core_tb/dut/ex_stage_i/alu_valid_i
add wave -noupdate -group ex_stage /core_tb/dut/ex_stage_i/alu_valid_o
add wave -noupdate -group ex_stage /core_tb/dut/ex_stage_i/alu_result_o
add wave -noupdate -group ex_stage /core_tb/dut/ex_stage_i/alu_trans_id_o
add wave -noupdate -group ex_stage /core_tb/dut/ex_stage_i/comparison_result_o
add wave -noupdate -group ex_stage /core_tb/dut/ex_stage_i/lsu_ready_o
add wave -noupdate -group ex_stage /core_tb/dut/ex_stage_i/lsu_valid_i
add wave -noupdate -group ex_stage /core_tb/dut/ex_stage_i/mult_ready_o
add wave -noupdate -group ex_stage /core_tb/dut/ex_stage_i/mult_valid_i
add wave -noupdate -group commit_stage /core_tb/dut/commit_stage_i/clk_i
add wave -noupdate -group commit_stage /core_tb/dut/commit_stage_i/rst_ni
add wave -noupdate -group commit_stage /core_tb/dut/commit_stage_i/exception_o
add wave -noupdate -group commit_stage /core_tb/dut/commit_stage_i/commit_instr_i
add wave -noupdate -group commit_stage /core_tb/dut/commit_stage_i/commit_ack_o
add wave -noupdate -group commit_stage /core_tb/dut/commit_stage_i/waddr_a_o
add wave -noupdate -group commit_stage /core_tb/dut/commit_stage_i/wdata_a_o
add wave -noupdate -group commit_stage /core_tb/dut/commit_stage_i/we_a_o
add wave -noupdate -group commit_stage /core_tb/dut/commit_stage_i/pc_o
add wave -noupdate -group commit_stage /core_tb/dut/commit_stage_i/csr_op_o
add wave -noupdate -group commit_stage /core_tb/dut/commit_stage_i/csr_wdata_o
add wave -noupdate -group commit_stage /core_tb/dut/commit_stage_i/csr_rdata_i
add wave -noupdate -group commit_stage /core_tb/dut/commit_stage_i/csr_exception_i
add wave -noupdate -group commit_stage /core_tb/dut/commit_stage_i/commit_lsu_o
add wave -noupdate -group commit_stage /core_tb/dut/commit_stage_i/commit_csr_o
add wave -noupdate -group commit_stage /core_tb/dut/commit_stage_i/irq_enable_i
add wave -noupdate -group commit_stage /core_tb/dut/commit_stage_i/exception
add wave -noupdate -group csr_file /core_tb/dut/csr_regfile_i/clk_i
add wave -noupdate -group csr_file /core_tb/dut/csr_regfile_i/rst_ni
add wave -noupdate -group csr_file /core_tb/dut/csr_regfile_i/flush_o
add wave -noupdate -group csr_file /core_tb/dut/csr_regfile_i/core_id_i
add wave -noupdate -group csr_file /core_tb/dut/csr_regfile_i/cluster_id_i
add wave -noupdate -group csr_file /core_tb/dut/csr_regfile_i/boot_addr_i
add wave -noupdate -group csr_file /core_tb/dut/csr_regfile_i/ex_i
add wave -noupdate -group csr_file /core_tb/dut/csr_regfile_i/csr_op_i
add wave -noupdate -group csr_file /core_tb/dut/csr_regfile_i/csr_addr_i
add wave -noupdate -group csr_file /core_tb/dut/csr_regfile_i/csr_wdata_i
add wave -noupdate -group csr_file /core_tb/dut/csr_regfile_i/csr_rdata_o
add wave -noupdate -group csr_file /core_tb/dut/csr_regfile_i/pc_i
add wave -noupdate -group csr_file /core_tb/dut/csr_regfile_i/csr_exception_o
add wave -noupdate -group csr_file /core_tb/dut/csr_regfile_i/irq_enable_o
add wave -noupdate -group csr_file /core_tb/dut/csr_regfile_i/epc_o
add wave -noupdate -group csr_file /core_tb/dut/csr_regfile_i/trap_vector_base_o
add wave -noupdate -group csr_file /core_tb/dut/csr_regfile_i/priv_lvl_o
add wave -noupdate -group csr_file /core_tb/dut/csr_regfile_i/enable_translation_o
add wave -noupdate -group csr_file /core_tb/dut/csr_regfile_i/flag_pum_o
add wave -noupdate -group csr_file /core_tb/dut/csr_regfile_i/flag_mxr_o
add wave -noupdate -group csr_file /core_tb/dut/csr_regfile_i/pd_ppn_o
add wave -noupdate -group csr_file /core_tb/dut/csr_regfile_i/asid_o
add wave -noupdate -group csr_file /core_tb/dut/csr_regfile_i/csr_addr
add wave -noupdate -group csr_file /core_tb/dut/csr_regfile_i/read_access_exception
add wave -noupdate -group csr_file /core_tb/dut/csr_regfile_i/update_access_exception
add wave -noupdate -group csr_file /core_tb/dut/csr_regfile_i/csr_we
add wave -noupdate -group csr_file /core_tb/dut/csr_regfile_i/csr_wdata
add wave -noupdate -group csr_file /core_tb/dut/csr_regfile_i/csr_rdata
add wave -noupdate -group csr_file /core_tb/dut/csr_regfile_i/priv_lvl_n
add wave -noupdate -group csr_file /core_tb/dut/csr_regfile_i/priv_lvl_q
add wave -noupdate -group csr_file /core_tb/dut/csr_regfile_i/prev_priv_lvl_n
add wave -noupdate -group csr_file /core_tb/dut/csr_regfile_i/prev_priv_lvl_q
add wave -noupdate -group csr_file /core_tb/dut/csr_regfile_i/mstatus_q
add wave -noupdate -group csr_file /core_tb/dut/csr_regfile_i/mstatus_n
add wave -noupdate -group csr_file /core_tb/dut/csr_regfile_i/mtvec_q
add wave -noupdate -group csr_file /core_tb/dut/csr_regfile_i/mtvec_n
add wave -noupdate -group csr_file /core_tb/dut/csr_regfile_i/medeleg_q
add wave -noupdate -group csr_file /core_tb/dut/csr_regfile_i/medeleg_n
add wave -noupdate -group csr_file /core_tb/dut/csr_regfile_i/mideleg_q
add wave -noupdate -group csr_file /core_tb/dut/csr_regfile_i/mideleg_n
add wave -noupdate -group csr_file /core_tb/dut/csr_regfile_i/mip_q
add wave -noupdate -group csr_file /core_tb/dut/csr_regfile_i/mip_n
add wave -noupdate -group csr_file /core_tb/dut/csr_regfile_i/mie_q
add wave -noupdate -group csr_file /core_tb/dut/csr_regfile_i/mie_n
add wave -noupdate -group csr_file /core_tb/dut/csr_regfile_i/mscratch_q
add wave -noupdate -group csr_file /core_tb/dut/csr_regfile_i/mscratch_n
add wave -noupdate -group csr_file /core_tb/dut/csr_regfile_i/mepc_q
add wave -noupdate -group csr_file /core_tb/dut/csr_regfile_i/mepc_n
add wave -noupdate -group csr_file /core_tb/dut/csr_regfile_i/mcause_q
add wave -noupdate -group csr_file /core_tb/dut/csr_regfile_i/mcause_n
add wave -noupdate -group csr_file /core_tb/dut/csr_regfile_i/mtval_q
add wave -noupdate -group csr_file /core_tb/dut/csr_regfile_i/mtval_n
add wave -noupdate -group csr_file /core_tb/dut/csr_regfile_i/stvec_q
add wave -noupdate -group csr_file /core_tb/dut/csr_regfile_i/stvec_n
add wave -noupdate -group csr_file /core_tb/dut/csr_regfile_i/sscratch_q
add wave -noupdate -group csr_file /core_tb/dut/csr_regfile_i/sscratch_n
add wave -noupdate -group csr_file /core_tb/dut/csr_regfile_i/sepc_q
add wave -noupdate -group csr_file /core_tb/dut/csr_regfile_i/sepc_n
add wave -noupdate -group csr_file /core_tb/dut/csr_regfile_i/scause_q
add wave -noupdate -group csr_file /core_tb/dut/csr_regfile_i/scause_n
add wave -noupdate -group csr_file /core_tb/dut/csr_regfile_i/stval_q
add wave -noupdate -group csr_file /core_tb/dut/csr_regfile_i/stval_n
add wave -noupdate -group csr_file /core_tb/dut/csr_regfile_i/satp_q
add wave -noupdate -group csr_file /core_tb/dut/csr_regfile_i/satp_n
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {207 ns} 0} {{Cursor 2} {278 ns} 1}
quietly wave cursor active 1
configure wave -namecolwidth 241
configure wave -valuecolwidth 258
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
WaveRestoreZoom {0 ns} {1580 ns}
