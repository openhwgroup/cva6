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
add wave -noupdate -group Core /core_tb/dut/rst_n
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
add wave -noupdate -group if /core_tb/dut/i_if_stage/clk_i
add wave -noupdate -group if /core_tb/dut/i_if_stage/rst_ni
add wave -noupdate -group if /core_tb/dut/i_if_stage/req_i
add wave -noupdate -group if /core_tb/dut/i_if_stage/if_busy_o
add wave -noupdate -group if /core_tb/dut/i_if_stage/id_ready_i
add wave -noupdate -group if /core_tb/dut/i_if_stage/halt_if_i
add wave -noupdate -group if /core_tb/dut/i_if_stage/instr_req_o
add wave -noupdate -group if /core_tb/dut/i_if_stage/instr_addr_o
add wave -noupdate -group if /core_tb/dut/i_if_stage/instr_gnt_i
add wave -noupdate -group if /core_tb/dut/i_if_stage/instr_rvalid_i
add wave -noupdate -group if /core_tb/dut/i_if_stage/instr_rdata_i
add wave -noupdate -group if /core_tb/dut/i_if_stage/instr_valid_id_o
add wave -noupdate -group if /core_tb/dut/i_if_stage/instr_rdata_id_o
add wave -noupdate -group if /core_tb/dut/i_if_stage/is_compressed_id_o
add wave -noupdate -group if /core_tb/dut/i_if_stage/illegal_c_insn_id_o
add wave -noupdate -group if /core_tb/dut/i_if_stage/pc_if_o
add wave -noupdate -group if /core_tb/dut/i_if_stage/pc_id_o
add wave -noupdate -group if /core_tb/dut/i_if_stage/boot_addr_i
add wave -noupdate -group if /core_tb/dut/i_if_stage/if_ready
add wave -noupdate -group if /core_tb/dut/i_if_stage/if_valid
add wave -noupdate -group if /core_tb/dut/i_if_stage/branch_req
add wave -noupdate -group if /core_tb/dut/i_if_stage/valid
add wave -noupdate -group if /core_tb/dut/i_if_stage/prefetch_busy
add wave -noupdate -group if /core_tb/dut/i_if_stage/fetch_addr_n
add wave -noupdate -group if /core_tb/dut/i_if_stage/fetch_valid
add wave -noupdate -group if /core_tb/dut/i_if_stage/fetch_ready
add wave -noupdate -group if /core_tb/dut/i_if_stage/fetch_rdata
add wave -noupdate -group if /core_tb/dut/i_if_stage/fetch_addr
add wave -noupdate -group if /core_tb/dut/i_if_stage/offset_fsm_cs
add wave -noupdate -group if /core_tb/dut/i_if_stage/offset_fsm_ns
add wave -noupdate -group if /core_tb/dut/i_if_stage/instr_decompressed
add wave -noupdate -group if /core_tb/dut/i_if_stage/illegal_c_insn
add wave -noupdate -group if /core_tb/dut/i_if_stage/instr_compressed_int
add wave -noupdate -group if /core_tb/dut/i_if_stage/clear_instr_valid_i
add wave -noupdate -group prefetcher /core_tb/dut/i_if_stage/prefetch_buffer_i/clk
add wave -noupdate -group prefetcher /core_tb/dut/i_if_stage/prefetch_buffer_i/rst_n
add wave -noupdate -group prefetcher /core_tb/dut/i_if_stage/prefetch_buffer_i/req_i
add wave -noupdate -group prefetcher /core_tb/dut/i_if_stage/prefetch_buffer_i/branch_i
add wave -noupdate -group prefetcher /core_tb/dut/i_if_stage/prefetch_buffer_i/addr_i
add wave -noupdate -group prefetcher /core_tb/dut/i_if_stage/prefetch_buffer_i/ready_i
add wave -noupdate -group prefetcher /core_tb/dut/i_if_stage/prefetch_buffer_i/valid_o
add wave -noupdate -group prefetcher /core_tb/dut/i_if_stage/prefetch_buffer_i/addr_o
add wave -noupdate -group prefetcher /core_tb/dut/i_if_stage/prefetch_buffer_i/rdata_o
add wave -noupdate -group prefetcher /core_tb/dut/i_if_stage/prefetch_buffer_i/instr_req_o
add wave -noupdate -group prefetcher /core_tb/dut/i_if_stage/prefetch_buffer_i/instr_gnt_i
add wave -noupdate -group prefetcher /core_tb/dut/i_if_stage/prefetch_buffer_i/instr_addr_o
add wave -noupdate -group prefetcher /core_tb/dut/i_if_stage/prefetch_buffer_i/instr_rdata_i
add wave -noupdate -group prefetcher /core_tb/dut/i_if_stage/prefetch_buffer_i/instr_rvalid_i
add wave -noupdate -group prefetcher /core_tb/dut/i_if_stage/prefetch_buffer_i/busy_o
add wave -noupdate -group prefetcher /core_tb/dut/i_if_stage/prefetch_buffer_i/CS
add wave -noupdate -group prefetcher /core_tb/dut/i_if_stage/prefetch_buffer_i/NS
add wave -noupdate -group prefetcher /core_tb/dut/i_if_stage/prefetch_buffer_i/instr_addr_q
add wave -noupdate -group prefetcher /core_tb/dut/i_if_stage/prefetch_buffer_i/fetch_addr
add wave -noupdate -group prefetcher /core_tb/dut/i_if_stage/prefetch_buffer_i/addr_valid
add wave -noupdate -group prefetcher /core_tb/dut/i_if_stage/prefetch_buffer_i/fifo_valid
add wave -noupdate -group prefetcher /core_tb/dut/i_if_stage/prefetch_buffer_i/fifo_ready
add wave -noupdate -group prefetcher /core_tb/dut/i_if_stage/prefetch_buffer_i/fifo_clear
add wave -noupdate -group prefetcher /core_tb/dut/i_if_stage/prefetch_buffer_i/valid_stored
add wave -noupdate -expand -group id_stage /core_tb/dut/id_stage_i/clk_i
add wave -noupdate -expand -group id_stage /core_tb/dut/id_stage_i/rst_ni
add wave -noupdate -expand -group id_stage /core_tb/dut/id_stage_i/test_en_i
add wave -noupdate -expand -group id_stage /core_tb/dut/id_stage_i/flush_i
add wave -noupdate -expand -group id_stage /core_tb/dut/id_stage_i/instruction_i
add wave -noupdate -expand -group id_stage /core_tb/dut/id_stage_i/instruction_valid_i
add wave -noupdate -expand -group id_stage /core_tb/dut/id_stage_i/pc_if_i
add wave -noupdate -expand -group id_stage /core_tb/dut/id_stage_i/ex_i
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
add wave -noupdate -expand -group id_stage -expand /core_tb/dut/id_stage_i/commit_instr_o
add wave -noupdate -expand -group id_stage /core_tb/dut/id_stage_i/commit_ack_i
add wave -noupdate -expand -group id_stage /core_tb/dut/id_stage_i/full_o
add wave -noupdate -expand -group id_stage /core_tb/dut/id_stage_i/rd_clobber_o
add wave -noupdate -expand -group id_stage /core_tb/dut/id_stage_i/rs1_i
add wave -noupdate -expand -group id_stage /core_tb/dut/id_stage_i/rs1_o
add wave -noupdate -expand -group id_stage /core_tb/dut/id_stage_i/rs1_valid_o
add wave -noupdate -expand -group id_stage /core_tb/dut/id_stage_i/rs2_i
add wave -noupdate -expand -group id_stage /core_tb/dut/id_stage_i/rs2_o
add wave -noupdate -expand -group id_stage /core_tb/dut/id_stage_i/rs2_valid_o
add wave -noupdate -expand -group id_stage /core_tb/dut/id_stage_i/issue_instr_o
add wave -noupdate -expand -group id_stage /core_tb/dut/id_stage_i/decoded_instr_i
add wave -noupdate -expand -group id_stage /core_tb/dut/id_stage_i/issue_instr_valid_o
add wave -noupdate -expand -group id_stage /core_tb/dut/id_stage_i/issue_ack_i
add wave -noupdate -expand -group id_stage /core_tb/dut/id_stage_i/illegal_instr_o
add wave -noupdate -expand -group ex_stage /core_tb/dut/ex_stage_i/clk_i
add wave -noupdate -expand -group ex_stage /core_tb/dut/ex_stage_i/rst_ni
add wave -noupdate -expand -group ex_stage /core_tb/dut/ex_stage_i/operator_i
add wave -noupdate -expand -group ex_stage /core_tb/dut/ex_stage_i/operand_a_i
add wave -noupdate -expand -group ex_stage /core_tb/dut/ex_stage_i/operand_b_i
add wave -noupdate -expand -group ex_stage /core_tb/dut/ex_stage_i/trans_id_i
add wave -noupdate -expand -group ex_stage /core_tb/dut/ex_stage_i/alu_ready_o
add wave -noupdate -expand -group ex_stage /core_tb/dut/ex_stage_i/alu_valid_i
add wave -noupdate -expand -group ex_stage /core_tb/dut/ex_stage_i/alu_valid_o
add wave -noupdate -expand -group ex_stage /core_tb/dut/ex_stage_i/alu_result_o
add wave -noupdate -expand -group ex_stage /core_tb/dut/ex_stage_i/alu_trans_id_o
add wave -noupdate -expand -group ex_stage /core_tb/dut/ex_stage_i/comparison_result_o
add wave -noupdate -expand -group ex_stage /core_tb/dut/ex_stage_i/lsu_ready_o
add wave -noupdate -expand -group ex_stage /core_tb/dut/ex_stage_i/lsu_valid_i
add wave -noupdate -expand -group ex_stage /core_tb/dut/ex_stage_i/mult_ready_o
add wave -noupdate -expand -group ex_stage /core_tb/dut/ex_stage_i/mult_valid_i
add wave -noupdate -group decoder /core_tb/dut/id_stage_i/decoder_i/clk_i
add wave -noupdate -group decoder /core_tb/dut/id_stage_i/decoder_i/rst_ni
add wave -noupdate -group decoder /core_tb/dut/id_stage_i/decoder_i/pc_i
add wave -noupdate -group decoder /core_tb/dut/id_stage_i/decoder_i/instruction_i
add wave -noupdate -group decoder /core_tb/dut/id_stage_i/decoder_i/ex_i
add wave -noupdate -group decoder /core_tb/dut/id_stage_i/decoder_i/instruction_o
add wave -noupdate -group decoder /core_tb/dut/id_stage_i/decoder_i/illegal_instr_o
add wave -noupdate -group decoder /core_tb/dut/id_stage_i/decoder_i/instr
add wave -noupdate -group decoder /core_tb/dut/id_stage_i/decoder_i/imm_select
add wave -noupdate -group decoder /core_tb/dut/id_stage_i/decoder_i/imm_i_type
add wave -noupdate -group decoder /core_tb/dut/id_stage_i/decoder_i/imm_iz_type
add wave -noupdate -group decoder /core_tb/dut/id_stage_i/decoder_i/imm_s_type
add wave -noupdate -group decoder /core_tb/dut/id_stage_i/decoder_i/imm_sb_type
add wave -noupdate -group decoder /core_tb/dut/id_stage_i/decoder_i/imm_u_type
add wave -noupdate -group decoder /core_tb/dut/id_stage_i/decoder_i/imm_uj_type
add wave -noupdate -group decoder /core_tb/dut/id_stage_i/decoder_i/imm_z_type
add wave -noupdate -group decoder /core_tb/dut/id_stage_i/decoder_i/imm_s2_type
add wave -noupdate -group decoder /core_tb/dut/id_stage_i/decoder_i/imm_bi_type
add wave -noupdate -group decoder /core_tb/dut/id_stage_i/decoder_i/imm_s3_type
add wave -noupdate -group decoder /core_tb/dut/id_stage_i/decoder_i/imm_vs_type
add wave -noupdate -group decoder /core_tb/dut/id_stage_i/decoder_i/imm_vu_type
add wave -noupdate -expand -group ALU /core_tb/dut/ex_stage_i/alu_i/operator_i
add wave -noupdate -expand -group ALU /core_tb/dut/ex_stage_i/alu_i/operand_a_i
add wave -noupdate -expand -group ALU /core_tb/dut/ex_stage_i/alu_i/operand_b_i
add wave -noupdate -expand -group ALU /core_tb/dut/ex_stage_i/alu_i/adder_result_o
add wave -noupdate -expand -group ALU /core_tb/dut/ex_stage_i/alu_i/adder_result_ext_o
add wave -noupdate -expand -group ALU /core_tb/dut/ex_stage_i/alu_i/result_o
add wave -noupdate -expand -group ALU /core_tb/dut/ex_stage_i/alu_i/comparison_result_o
add wave -noupdate -expand -group ALU /core_tb/dut/ex_stage_i/alu_i/is_equal_result_o
add wave -noupdate -expand -group ALU /core_tb/dut/ex_stage_i/alu_i/operand_a_rev
add wave -noupdate -expand -group ALU /core_tb/dut/ex_stage_i/alu_i/operand_a_rev32
add wave -noupdate -expand -group ALU /core_tb/dut/ex_stage_i/alu_i/operand_b_neg
add wave -noupdate -expand -group ALU /core_tb/dut/ex_stage_i/alu_i/adder_op_b_negate
add wave -noupdate -expand -group ALU /core_tb/dut/ex_stage_i/alu_i/adder_in_a
add wave -noupdate -expand -group ALU /core_tb/dut/ex_stage_i/alu_i/adder_in_b
add wave -noupdate -expand -group ALU /core_tb/dut/ex_stage_i/alu_i/adder_result
add wave -noupdate -expand -group ALU /core_tb/dut/ex_stage_i/alu_i/shift_left
add wave -noupdate -expand -group ALU /core_tb/dut/ex_stage_i/alu_i/shift_arithmetic
add wave -noupdate -expand -group ALU /core_tb/dut/ex_stage_i/alu_i/shift_amt
add wave -noupdate -expand -group ALU /core_tb/dut/ex_stage_i/alu_i/shift_op_a
add wave -noupdate -expand -group ALU /core_tb/dut/ex_stage_i/alu_i/shift_op_a32
add wave -noupdate -expand -group ALU /core_tb/dut/ex_stage_i/alu_i/shift_result
add wave -noupdate -expand -group ALU /core_tb/dut/ex_stage_i/alu_i/shift_result32
add wave -noupdate -expand -group ALU /core_tb/dut/ex_stage_i/alu_i/shift_right_result
add wave -noupdate -expand -group ALU /core_tb/dut/ex_stage_i/alu_i/shift_right_result32
add wave -noupdate -expand -group ALU /core_tb/dut/ex_stage_i/alu_i/shift_left_result
add wave -noupdate -expand -group ALU /core_tb/dut/ex_stage_i/alu_i/shift_left_result32
add wave -noupdate -expand -group ALU /core_tb/dut/ex_stage_i/alu_i/shift_op_a_64
add wave -noupdate -expand -group ALU /core_tb/dut/ex_stage_i/alu_i/shift_op_a_32
add wave -noupdate -expand -group ALU /core_tb/dut/ex_stage_i/alu_i/is_equal
add wave -noupdate -expand -group ALU /core_tb/dut/ex_stage_i/alu_i/is_greater_equal
add wave -noupdate -expand -group ALU /core_tb/dut/ex_stage_i/alu_i/cmp_signed
add wave -noupdate -expand -group ALU /core_tb/dut/ex_stage_i/alu_i/cmp_result
add wave -noupdate -expand -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/clk_i
add wave -noupdate -expand -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/rst_ni
add wave -noupdate -expand -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/test_en_i
add wave -noupdate -expand -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/flush_i
add wave -noupdate -expand -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/issue_instr_i
add wave -noupdate -expand -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/issue_instr_valid_i
add wave -noupdate -expand -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/issue_ack_o
add wave -noupdate -expand -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/rs1_o
add wave -noupdate -expand -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/rs1_i
add wave -noupdate -expand -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/rs1_valid_i
add wave -noupdate -expand -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/rs2_o
add wave -noupdate -expand -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/rs2_i
add wave -noupdate -expand -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/rs2_valid_i
add wave -noupdate -expand -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/rd_clobber_i
add wave -noupdate -expand -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/operator_o
add wave -noupdate -expand -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/operand_a_o
add wave -noupdate -expand -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/operand_b_o
add wave -noupdate -expand -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/trans_id_o
add wave -noupdate -expand -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/alu_ready_i
add wave -noupdate -expand -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/alu_valid_o
add wave -noupdate -expand -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/lsu_ready_i
add wave -noupdate -expand -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/lsu_valid_o
add wave -noupdate -expand -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/mult_ready_i
add wave -noupdate -expand -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/mult_valid_o
add wave -noupdate -expand -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/waddr_a_i
add wave -noupdate -expand -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/wdata_a_i
add wave -noupdate -expand -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/we_a_i
add wave -noupdate -expand -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/stall
add wave -noupdate -expand -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/fu_busy
add wave -noupdate -expand -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/operand_a_regfile
add wave -noupdate -expand -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/operand_b_regfile
add wave -noupdate -expand -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/operand_a_n
add wave -noupdate -expand -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/operand_a_q
add wave -noupdate -expand -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/operand_b_n
add wave -noupdate -expand -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/operand_b_q
add wave -noupdate -expand -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/alu_valid_n
add wave -noupdate -expand -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/alu_valid_q
add wave -noupdate -expand -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/trans_id_n
add wave -noupdate -expand -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/trans_id_q
add wave -noupdate -expand -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/operator_n
add wave -noupdate -expand -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/operator_q
add wave -noupdate -expand -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/forward_rs1
add wave -noupdate -expand -group issue_read_operands /core_tb/dut/id_stage_i/issue_read_operands_i/forward_rs2
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {499 ns} 0} {{Cursor 2} {278 ns} 1}
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
WaveRestoreZoom {0 ns} {840 ns}
