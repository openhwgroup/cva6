onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /tb/KILL_RATE
add wave -noupdate /tb/MEM_BYTES
add wave -noupdate /tb/MEM_RAND_HIT_RATE
add wave -noupdate /tb/MEM_RAND_INV_RATE
add wave -noupdate /tb/MEM_WORDS
add wave -noupdate /tb/NC_ADDR_BEGIN
add wave -noupdate /tb/amo_ack_o
add wave -noupdate /tb/amo_rand_en
add wave -noupdate /tb/amo_req_i
add wave -noupdate /tb/clk_i
add wave -noupdate /tb/enable_i
add wave -noupdate /tb/end_of_sim
add wave -noupdate /tb/flush_ack_o
add wave -noupdate /tb/flush_i
add wave -noupdate /tb/inv_rand_en
add wave -noupdate /tb/mem_array
add wave -noupdate /tb/mem_data_ack_i
add wave -noupdate /tb/mem_data_o
add wave -noupdate /tb/mem_data_req_o
add wave -noupdate /tb/mem_rand_en
add wave -noupdate -expand /tb/mem_rtrn_i
add wave -noupdate /tb/mem_rtrn_vld_i
add wave -noupdate /tb/miss_o
add wave -noupdate /tb/req_ports_i
add wave -noupdate /tb/req_ports_o
add wave -noupdate /tb/rst_ni
add wave -noupdate /tb/seq_done
add wave -noupdate /tb/seq_last
add wave -noupdate /tb/seq_num_resp
add wave -noupdate /tb/seq_run
add wave -noupdate /tb/seq_type
add wave -noupdate /tb/test_name
add wave -noupdate /tb/wbuffer_empty_o
add wave -noupdate -divider Programs
add wave -noupdate -group Writeport /tb/i_tb_writeport/clk_i
add wave -noupdate -group Writeport /tb/i_tb_writeport/rst_ni
add wave -noupdate -group Writeport /tb/i_tb_writeport/req_rate_i
add wave -noupdate -group Writeport /tb/i_tb_writeport/seq_type_i
add wave -noupdate -group Writeport /tb/i_tb_writeport/seq_run_i
add wave -noupdate -group Writeport /tb/i_tb_writeport/seq_num_vect_i
add wave -noupdate -group Writeport /tb/i_tb_writeport/seq_last_i
add wave -noupdate -group Writeport /tb/i_tb_writeport/dut_req_port_i
add wave -noupdate -group Writeport /tb/i_tb_writeport/MEM_WORDS
add wave -noupdate -group Writeport /tb/i_tb_writeport/RND_SEED
add wave -noupdate -group Writeport /tb/i_tb_writeport/VERBOSE
add wave -noupdate -group Writeport /tb/i_tb_writeport/test_name_i
add wave -noupdate -group Writeport /tb/i_tb_writeport/paddr
add wave -noupdate -group Writeport /tb/i_tb_writeport/seq_done_o
add wave -noupdate -group Writeport /tb/i_tb_writeport/dut_req_port_o
add wave -noupdate -group {Readport 0} /tb/i_tb_readport0/clk_i
add wave -noupdate -group {Readport 0} /tb/i_tb_readport0/rst_ni
add wave -noupdate -group {Readport 0} /tb/i_tb_readport0/seq_type_i
add wave -noupdate -group {Readport 0} /tb/i_tb_readport0/seq_run_i
add wave -noupdate -group {Readport 0} /tb/i_tb_readport0/seq_num_resp_i
add wave -noupdate -group {Readport 0} /tb/i_tb_readport0/seq_last_i
add wave -noupdate -group {Readport 0} /tb/i_tb_readport0/seq_done_o
add wave -noupdate -group {Readport 0} -expand /tb/i_tb_readport0/dut_req_port_o
add wave -noupdate -group {Readport 0} -expand /tb/i_tb_readport0/dut_req_port_i
add wave -noupdate -group {Readport 0} /tb/i_tb_readport0/paddr
add wave -noupdate -group {Readport 0} /tb/i_tb_readport0/seq_end_req
add wave -noupdate -group {Readport 0} /tb/i_tb_readport0/seq_end_ack
add wave -noupdate -group {Readport 0} /tb/i_tb_readport0/tag_q
add wave -noupdate -group {Readport 0} /tb/i_tb_readport0/tag_vld_q
add wave -noupdate -group {Readport 1} /tb/i_tb_readport1/clk_i
add wave -noupdate -group {Readport 1} /tb/i_tb_readport1/rst_ni
add wave -noupdate -group {Readport 1} /tb/i_tb_readport1/seq_type_i
add wave -noupdate -group {Readport 1} /tb/i_tb_readport1/seq_run_i
add wave -noupdate -group {Readport 1} /tb/i_tb_readport1/seq_num_resp_i
add wave -noupdate -group {Readport 1} /tb/i_tb_readport1/seq_last_i
add wave -noupdate -group {Readport 1} /tb/i_tb_readport1/seq_done_o
add wave -noupdate -group {Readport 1} -expand /tb/i_tb_readport1/dut_req_port_o
add wave -noupdate -group {Readport 1} -expand /tb/i_tb_readport1/dut_req_port_i
add wave -noupdate -group {Readport 1} /tb/i_tb_readport1/paddr
add wave -noupdate -group {Readport 1} /tb/i_tb_readport1/seq_end_req
add wave -noupdate -group {Readport 1} /tb/i_tb_readport1/seq_end_ack
add wave -noupdate -group {Readport 1} /tb/i_tb_readport1/tag_q
add wave -noupdate -group {Readport 1} /tb/i_tb_readport1/tag_vld_q
add wave -noupdate -group i_tb_mem /tb/i_tb_mem/clk_i
add wave -noupdate -group i_tb_mem /tb/i_tb_mem/rst_ni
add wave -noupdate -group i_tb_mem /tb/i_tb_mem/mem_rand_en_i
add wave -noupdate -group i_tb_mem /tb/i_tb_mem/inv_rand_en_i
add wave -noupdate -group i_tb_mem /tb/i_tb_mem/amo_rand_en_i
add wave -noupdate -group i_tb_mem /tb/i_tb_mem/mem_data_req_i
add wave -noupdate -group i_tb_mem /tb/i_tb_mem/mem_data_i
add wave -noupdate -group i_tb_mem /tb/i_tb_mem/seq_last_i
add wave -noupdate -group i_tb_mem /tb/i_tb_mem/check_en_i
add wave -noupdate -group i_tb_mem /tb/i_tb_mem/commit_en_i
add wave -noupdate -group i_tb_mem /tb/i_tb_mem/commit_be_i
add wave -noupdate -group i_tb_mem /tb/i_tb_mem/commit_paddr_i
add wave -noupdate -group i_tb_mem /tb/i_tb_mem/write_en_i
add wave -noupdate -group i_tb_mem /tb/i_tb_mem/write_be_i
add wave -noupdate -group i_tb_mem /tb/i_tb_mem/write_data_i
add wave -noupdate -group i_tb_mem /tb/i_tb_mem/write_paddr_i
add wave -noupdate -group i_tb_mem /tb/i_tb_mem/MEM_RAND_HIT_RATE
add wave -noupdate -group i_tb_mem /tb/i_tb_mem/MEM_RAND_INV_RATE
add wave -noupdate -group i_tb_mem /tb/i_tb_mem/MEM_WORDS
add wave -noupdate -group i_tb_mem /tb/i_tb_mem/NC_ADDR_BEGIN
add wave -noupdate -group i_tb_mem /tb/i_tb_mem/NC_ADDR_GE_LT
add wave -noupdate -group i_tb_mem /tb/i_tb_mem/mem_ready_q
add wave -noupdate -group i_tb_mem /tb/i_tb_mem/mem_inv_q
add wave -noupdate -group i_tb_mem /tb/i_tb_mem/rand_addr_q
add wave -noupdate -group i_tb_mem /tb/i_tb_mem/outfifo_data
add wave -noupdate -group i_tb_mem /tb/i_tb_mem/outfifo_pop
add wave -noupdate -group i_tb_mem /tb/i_tb_mem/outfifo_push
add wave -noupdate -group i_tb_mem /tb/i_tb_mem/outfifo_full
add wave -noupdate -group i_tb_mem /tb/i_tb_mem/outfifo_empty
add wave -noupdate -group i_tb_mem /tb/i_tb_mem/infifo_data
add wave -noupdate -group i_tb_mem /tb/i_tb_mem/infifo_pop
add wave -noupdate -group i_tb_mem /tb/i_tb_mem/infifo_push
add wave -noupdate -group i_tb_mem /tb/i_tb_mem/infifo_full
add wave -noupdate -group i_tb_mem /tb/i_tb_mem/infifo_empty
add wave -noupdate -group i_tb_mem /tb/i_tb_mem/initialized_q
add wave -noupdate -group i_tb_mem /tb/i_tb_mem/write_en
add wave -noupdate -group i_tb_mem -color Magenta /tb/i_tb_mem/mem_array_q
add wave -noupdate -group i_tb_mem -color Magenta /tb/i_tb_mem/mem_array_shadow_q
add wave -noupdate -group i_tb_mem -color Magenta /tb/i_tb_mem/mem_array_dirty_q
add wave -noupdate -group i_tb_mem /tb/i_tb_mem/mem_rtrn_vld_o
add wave -noupdate -group i_tb_mem /tb/i_tb_mem/mem_rtrn_o
add wave -noupdate -group i_tb_mem /tb/i_tb_mem/mem_data_ack_o
add wave -noupdate -group i_tb_mem /tb/i_tb_mem/mem_array_o
add wave -noupdate -divider Modules
add wave -noupdate -group i_dut /tb/i_dut/clk_i
add wave -noupdate -group i_dut /tb/i_dut/rst_ni
add wave -noupdate -group i_dut /tb/i_dut/enable_i
add wave -noupdate -group i_dut /tb/i_dut/flush_i
add wave -noupdate -group i_dut /tb/i_dut/amo_req_i
add wave -noupdate -group i_dut /tb/i_dut/req_ports_i
add wave -noupdate -group i_dut /tb/i_dut/mem_rtrn_vld_i
add wave -noupdate -group i_dut /tb/i_dut/mem_rtrn_i
add wave -noupdate -group i_dut /tb/i_dut/mem_data_ack_i
add wave -noupdate -group i_dut /tb/i_dut/NC_ADDR_BEGIN
add wave -noupdate -group i_dut /tb/i_dut/NC_ADDR_GE_LT
add wave -noupdate -group i_dut /tb/i_dut/NUM_PORTS
add wave -noupdate -group i_dut /tb/i_dut/cache_en
add wave -noupdate -group i_dut /tb/i_dut/flush_en
add wave -noupdate -group i_dut /tb/i_dut/wr_cl_vld
add wave -noupdate -group i_dut /tb/i_dut/wr_cl_tag
add wave -noupdate -group i_dut /tb/i_dut/wr_cl_idx
add wave -noupdate -group i_dut /tb/i_dut/wr_cl_off
add wave -noupdate -group i_dut /tb/i_dut/wr_cl_data
add wave -noupdate -group i_dut /tb/i_dut/wr_cl_data_be
add wave -noupdate -group i_dut /tb/i_dut/wr_vld_bits
add wave -noupdate -group i_dut /tb/i_dut/wr_req
add wave -noupdate -group i_dut /tb/i_dut/wr_ack
add wave -noupdate -group i_dut /tb/i_dut/wr_idx
add wave -noupdate -group i_dut /tb/i_dut/wr_off
add wave -noupdate -group i_dut /tb/i_dut/wr_data
add wave -noupdate -group i_dut /tb/i_dut/wr_data_be
add wave -noupdate -group i_dut /tb/i_dut/miss_req
add wave -noupdate -group i_dut /tb/i_dut/miss_ack
add wave -noupdate -group i_dut /tb/i_dut/miss_nc
add wave -noupdate -group i_dut /tb/i_dut/miss_we
add wave -noupdate -group i_dut /tb/i_dut/miss_wdata
add wave -noupdate -group i_dut /tb/i_dut/miss_paddr
add wave -noupdate -group i_dut /tb/i_dut/miss_vld_bits
add wave -noupdate -group i_dut /tb/i_dut/miss_size
add wave -noupdate -group i_dut /tb/i_dut/miss_wr_id
add wave -noupdate -group i_dut /tb/i_dut/miss_rtrn_vld
add wave -noupdate -group i_dut /tb/i_dut/miss_rtrn_id
add wave -noupdate -group i_dut /tb/i_dut/rd_req
add wave -noupdate -group i_dut /tb/i_dut/rd_ack
add wave -noupdate -group i_dut /tb/i_dut/rd_tag
add wave -noupdate -group i_dut /tb/i_dut/rd_idx
add wave -noupdate -group i_dut /tb/i_dut/rd_off
add wave -noupdate -group i_dut /tb/i_dut/rd_data
add wave -noupdate -group i_dut /tb/i_dut/rd_vld_bits
add wave -noupdate -group i_dut /tb/i_dut/rd_hit_oh
add wave -noupdate -group i_dut /tb/i_dut/wbuffer_data
add wave -noupdate -group i_dut /tb/i_dut/flush_ack_o
add wave -noupdate -group i_dut /tb/i_dut/miss_o
add wave -noupdate -group i_dut /tb/i_dut/wbuffer_empty_o
add wave -noupdate -group i_dut /tb/i_dut/amo_ack_o
add wave -noupdate -group i_dut /tb/i_dut/req_ports_o
add wave -noupdate -group i_dut /tb/i_dut/mem_data_req_o
add wave -noupdate -group i_dut /tb/i_dut/mem_data_o
add wave -noupdate -group i_wbuffer /tb/i_dut/i_serpent_dcache_wbuffer/clk_i
add wave -noupdate -group i_wbuffer /tb/i_dut/i_serpent_dcache_wbuffer/rst_ni
add wave -noupdate -group i_wbuffer /tb/i_dut/i_serpent_dcache_wbuffer/cache_en_i
add wave -noupdate -group i_wbuffer -color Magenta /tb/i_dut/i_serpent_dcache_wbuffer/req_port_i
add wave -noupdate -group i_wbuffer -color Magenta /tb/i_dut/i_serpent_dcache_wbuffer/req_port_o
add wave -noupdate -group i_wbuffer /tb/i_dut/i_serpent_dcache_wbuffer/miss_ack_i
add wave -noupdate -group i_wbuffer /tb/i_dut/i_serpent_dcache_wbuffer/miss_rtrn_vld_i
add wave -noupdate -group i_wbuffer /tb/i_dut/i_serpent_dcache_wbuffer/miss_rtrn_id_i
add wave -noupdate -group i_wbuffer /tb/i_dut/i_serpent_dcache_wbuffer/rd_ack_i
add wave -noupdate -group i_wbuffer /tb/i_dut/i_serpent_dcache_wbuffer/rd_data_i
add wave -noupdate -group i_wbuffer /tb/i_dut/i_serpent_dcache_wbuffer/rd_vld_bits_i
add wave -noupdate -group i_wbuffer /tb/i_dut/i_serpent_dcache_wbuffer/rd_hit_oh_i
add wave -noupdate -group i_wbuffer /tb/i_dut/i_serpent_dcache_wbuffer/wr_ack_i
add wave -noupdate -group i_wbuffer /tb/i_dut/i_serpent_dcache_wbuffer/empty_o
add wave -noupdate -group i_wbuffer /tb/i_dut/i_serpent_dcache_wbuffer/miss_paddr_o
add wave -noupdate -group i_wbuffer /tb/i_dut/i_serpent_dcache_wbuffer/miss_req_o
add wave -noupdate -group i_wbuffer /tb/i_dut/i_serpent_dcache_wbuffer/miss_we_o
add wave -noupdate -group i_wbuffer /tb/i_dut/i_serpent_dcache_wbuffer/miss_wdata_o
add wave -noupdate -group i_wbuffer /tb/i_dut/i_serpent_dcache_wbuffer/miss_vld_bits_o
add wave -noupdate -group i_wbuffer /tb/i_dut/i_serpent_dcache_wbuffer/miss_nc_o
add wave -noupdate -group i_wbuffer /tb/i_dut/i_serpent_dcache_wbuffer/miss_size_o
add wave -noupdate -group i_wbuffer /tb/i_dut/i_serpent_dcache_wbuffer/miss_wr_id_o
add wave -noupdate -group i_wbuffer /tb/i_dut/i_serpent_dcache_wbuffer/rd_tag_o
add wave -noupdate -group i_wbuffer /tb/i_dut/i_serpent_dcache_wbuffer/rd_idx_o
add wave -noupdate -group i_wbuffer /tb/i_dut/i_serpent_dcache_wbuffer/rd_off_o
add wave -noupdate -group i_wbuffer /tb/i_dut/i_serpent_dcache_wbuffer/rd_req_o
add wave -noupdate -group i_wbuffer /tb/i_dut/i_serpent_dcache_wbuffer/wr_req_o
add wave -noupdate -group i_wbuffer /tb/i_dut/i_serpent_dcache_wbuffer/wr_idx_o
add wave -noupdate -group i_wbuffer /tb/i_dut/i_serpent_dcache_wbuffer/wr_off_o
add wave -noupdate -group i_wbuffer /tb/i_dut/i_serpent_dcache_wbuffer/wr_data_o
add wave -noupdate -group i_wbuffer /tb/i_dut/i_serpent_dcache_wbuffer/wr_data_be_o
add wave -noupdate -group i_wbuffer /tb/i_dut/i_serpent_dcache_wbuffer/wbuffer_data_o
add wave -noupdate -group i_wbuffer /tb/i_dut/i_serpent_dcache_wbuffer/NC_ADDR_BEGIN
add wave -noupdate -group i_wbuffer /tb/i_dut/i_serpent_dcache_wbuffer/NC_ADDR_GE_LT
add wave -noupdate -group i_wbuffer /tb/i_dut/i_serpent_dcache_wbuffer/tx_stat_d
add wave -noupdate -group i_wbuffer /tb/i_dut/i_serpent_dcache_wbuffer/tx_stat_q
add wave -noupdate -group i_wbuffer /tb/i_dut/i_serpent_dcache_wbuffer/wbuffer_q
add wave -noupdate -group i_wbuffer /tb/i_dut/i_serpent_dcache_wbuffer/wbuffer_d
add wave -noupdate -group i_wbuffer /tb/i_dut/i_serpent_dcache_wbuffer/valid
add wave -noupdate -group i_wbuffer -color Magenta /tb/i_dut/i_serpent_dcache_wbuffer/debug_paddr
add wave -noupdate -group i_wbuffer /tb/i_dut/i_serpent_dcache_wbuffer/dirty
add wave -noupdate -group i_wbuffer /tb/i_dut/i_serpent_dcache_wbuffer/tocheck
add wave -noupdate -group i_wbuffer /tb/i_dut/i_serpent_dcache_wbuffer/wbuffer_hit_oh
add wave -noupdate -group i_wbuffer /tb/i_dut/i_serpent_dcache_wbuffer/inval_hit
add wave -noupdate -group i_wbuffer /tb/i_dut/i_serpent_dcache_wbuffer/bdirty
add wave -noupdate -group i_wbuffer /tb/i_dut/i_serpent_dcache_wbuffer/next_ptr
add wave -noupdate -group i_wbuffer /tb/i_dut/i_serpent_dcache_wbuffer/dirty_ptr
add wave -noupdate -group i_wbuffer /tb/i_dut/i_serpent_dcache_wbuffer/hit_ptr
add wave -noupdate -group i_wbuffer /tb/i_dut/i_serpent_dcache_wbuffer/wr_ptr
add wave -noupdate -group i_wbuffer /tb/i_dut/i_serpent_dcache_wbuffer/check_ptr_d
add wave -noupdate -group i_wbuffer /tb/i_dut/i_serpent_dcache_wbuffer/check_ptr_q
add wave -noupdate -group i_wbuffer /tb/i_dut/i_serpent_dcache_wbuffer/rtrn_ptr
add wave -noupdate -group i_wbuffer /tb/i_dut/i_serpent_dcache_wbuffer/tx_cnt_q
add wave -noupdate -group i_wbuffer /tb/i_dut/i_serpent_dcache_wbuffer/tx_cnt_d
add wave -noupdate -group i_wbuffer /tb/i_dut/i_serpent_dcache_wbuffer/tx_id_q
add wave -noupdate -group i_wbuffer /tb/i_dut/i_serpent_dcache_wbuffer/tx_id_d
add wave -noupdate -group i_wbuffer /tb/i_dut/i_serpent_dcache_wbuffer/rtrn_id
add wave -noupdate -group i_wbuffer /tb/i_dut/i_serpent_dcache_wbuffer/bdirty_off
add wave -noupdate -group i_wbuffer /tb/i_dut/i_serpent_dcache_wbuffer/tx_be
add wave -noupdate -group i_wbuffer /tb/i_dut/i_serpent_dcache_wbuffer/wr_paddr
add wave -noupdate -group i_wbuffer /tb/i_dut/i_serpent_dcache_wbuffer/rd_paddr
add wave -noupdate -group i_wbuffer /tb/i_dut/i_serpent_dcache_wbuffer/check_en_d
add wave -noupdate -group i_wbuffer /tb/i_dut/i_serpent_dcache_wbuffer/check_en_q
add wave -noupdate -group i_wbuffer /tb/i_dut/i_serpent_dcache_wbuffer/full
add wave -noupdate -group i_wbuffer /tb/i_dut/i_serpent_dcache_wbuffer/dirty_rd_en
add wave -noupdate -group i_wbuffer /tb/i_dut/i_serpent_dcache_wbuffer/rdy
add wave -noupdate -group i_wbuffer /tb/i_dut/i_serpent_dcache_wbuffer/rtrn_empty
add wave -noupdate -group i_wbuffer /tb/i_dut/i_serpent_dcache_wbuffer/evict
add wave -noupdate -group i_wbuffer /tb/i_dut/i_serpent_dcache_wbuffer/nc_pending_d
add wave -noupdate -group i_wbuffer /tb/i_dut/i_serpent_dcache_wbuffer/nc_pending_q
add wave -noupdate -group i_wbuffer /tb/i_dut/i_serpent_dcache_wbuffer/addr_is_nc
add wave -noupdate -group i_missunit /tb/i_dut/i_serpent_dcache_missunit/clk_i
add wave -noupdate -group i_missunit /tb/i_dut/i_serpent_dcache_missunit/rst_ni
add wave -noupdate -group i_missunit /tb/i_dut/i_serpent_dcache_missunit/enable_i
add wave -noupdate -group i_missunit /tb/i_dut/i_serpent_dcache_missunit/flush_i
add wave -noupdate -group i_missunit /tb/i_dut/i_serpent_dcache_missunit/wbuffer_empty_i
add wave -noupdate -group i_missunit /tb/i_dut/i_serpent_dcache_missunit/amo_req_i
add wave -noupdate -group i_missunit -expand /tb/i_dut/i_serpent_dcache_missunit/miss_req_i
add wave -noupdate -group i_missunit /tb/i_dut/i_serpent_dcache_missunit/miss_nc_i
add wave -noupdate -group i_missunit /tb/i_dut/i_serpent_dcache_missunit/miss_we_i
add wave -noupdate -group i_missunit /tb/i_dut/i_serpent_dcache_missunit/miss_wdata_i
add wave -noupdate -group i_missunit /tb/i_dut/i_serpent_dcache_missunit/miss_paddr_i
add wave -noupdate -group i_missunit /tb/i_dut/i_serpent_dcache_missunit/miss_vld_bits_i
add wave -noupdate -group i_missunit /tb/i_dut/i_serpent_dcache_missunit/miss_size_i
add wave -noupdate -group i_missunit /tb/i_dut/i_serpent_dcache_missunit/miss_wr_id_i
add wave -noupdate -group i_missunit /tb/i_dut/i_serpent_dcache_missunit/mem_rtrn_vld_i
add wave -noupdate -group i_missunit /tb/i_dut/i_serpent_dcache_missunit/mem_rtrn_i
add wave -noupdate -group i_missunit /tb/i_dut/i_serpent_dcache_missunit/mem_data_ack_i
add wave -noupdate -group i_missunit /tb/i_dut/i_serpent_dcache_missunit/flush_ack_o
add wave -noupdate -group i_missunit /tb/i_dut/i_serpent_dcache_missunit/miss_o
add wave -noupdate -group i_missunit /tb/i_dut/i_serpent_dcache_missunit/cache_en_o
add wave -noupdate -group i_missunit /tb/i_dut/i_serpent_dcache_missunit/flush_en_o
add wave -noupdate -group i_missunit /tb/i_dut/i_serpent_dcache_missunit/amo_ack_o
add wave -noupdate -group i_missunit /tb/i_dut/i_serpent_dcache_missunit/miss_ack_o
add wave -noupdate -group i_missunit /tb/i_dut/i_serpent_dcache_missunit/miss_replay_o
add wave -noupdate -group i_missunit /tb/i_dut/i_serpent_dcache_missunit/miss_rtrn_vld_o
add wave -noupdate -group i_missunit /tb/i_dut/i_serpent_dcache_missunit/miss_rtrn_id_o
add wave -noupdate -group i_missunit /tb/i_dut/i_serpent_dcache_missunit/wr_cl_vld_o
add wave -noupdate -group i_missunit /tb/i_dut/i_serpent_dcache_missunit/wr_cl_nc_o
add wave -noupdate -group i_missunit /tb/i_dut/i_serpent_dcache_missunit/wr_cl_we_o
add wave -noupdate -group i_missunit /tb/i_dut/i_serpent_dcache_missunit/wr_cl_tag_o
add wave -noupdate -group i_missunit /tb/i_dut/i_serpent_dcache_missunit/wr_cl_idx_o
add wave -noupdate -group i_missunit /tb/i_dut/i_serpent_dcache_missunit/wr_cl_off_o
add wave -noupdate -group i_missunit /tb/i_dut/i_serpent_dcache_missunit/wr_cl_data_o
add wave -noupdate -group i_missunit /tb/i_dut/i_serpent_dcache_missunit/wr_cl_data_be_o
add wave -noupdate -group i_missunit /tb/i_dut/i_serpent_dcache_missunit/wr_vld_bits_o
add wave -noupdate -group i_missunit /tb/i_dut/i_serpent_dcache_missunit/mem_data_req_o
add wave -noupdate -group i_missunit /tb/i_dut/i_serpent_dcache_missunit/mem_data_o
add wave -noupdate -group i_missunit /tb/i_dut/i_serpent_dcache_missunit/NUM_PORTS
add wave -noupdate -group i_missunit /tb/i_dut/i_serpent_dcache_missunit/state_d
add wave -noupdate -group i_missunit /tb/i_dut/i_serpent_dcache_missunit/state_q
add wave -noupdate -group i_missunit /tb/i_dut/i_serpent_dcache_missunit/mshr_d
add wave -noupdate -group i_missunit /tb/i_dut/i_serpent_dcache_missunit/mshr_q
add wave -noupdate -group i_missunit /tb/i_dut/i_serpent_dcache_missunit/repl_way
add wave -noupdate -group i_missunit /tb/i_dut/i_serpent_dcache_missunit/inv_way
add wave -noupdate -group i_missunit /tb/i_dut/i_serpent_dcache_missunit/rnd_way
add wave -noupdate -group i_missunit /tb/i_dut/i_serpent_dcache_missunit/mshr_vld_d
add wave -noupdate -group i_missunit /tb/i_dut/i_serpent_dcache_missunit/mshr_vld_q
add wave -noupdate -group i_missunit /tb/i_dut/i_serpent_dcache_missunit/mshr_allocate
add wave -noupdate -group i_missunit /tb/i_dut/i_serpent_dcache_missunit/update_lfsr
add wave -noupdate -group i_missunit /tb/i_dut/i_serpent_dcache_missunit/all_ways_valid
add wave -noupdate -group i_missunit /tb/i_dut/i_serpent_dcache_missunit/enable_d
add wave -noupdate -group i_missunit /tb/i_dut/i_serpent_dcache_missunit/enable_q
add wave -noupdate -group i_missunit /tb/i_dut/i_serpent_dcache_missunit/flush_ack_d
add wave -noupdate -group i_missunit /tb/i_dut/i_serpent_dcache_missunit/flush_ack_q
add wave -noupdate -group i_missunit /tb/i_dut/i_serpent_dcache_missunit/amo_sel
add wave -noupdate -group i_missunit /tb/i_dut/i_serpent_dcache_missunit/flush_done
add wave -noupdate -group i_missunit /tb/i_dut/i_serpent_dcache_missunit/mask_reads
add wave -noupdate -group i_missunit /tb/i_dut/i_serpent_dcache_missunit/miss_is_write
add wave -noupdate -group i_missunit /tb/i_dut/i_serpent_dcache_missunit/amo_data
add wave -noupdate -group i_missunit /tb/i_dut/i_serpent_dcache_missunit/miss_port_idx
add wave -noupdate -group i_missunit /tb/i_dut/i_serpent_dcache_missunit/cnt_d
add wave -noupdate -group i_missunit /tb/i_dut/i_serpent_dcache_missunit/cnt_q
add wave -noupdate -group i_missunit /tb/i_dut/i_serpent_dcache_missunit/miss_req
add wave -noupdate -group i_missunit /tb/i_dut/i_serpent_dcache_missunit/inv_vld
add wave -noupdate -group i_missunit /tb/i_dut/i_serpent_dcache_missunit/cl_write_en
add wave -noupdate -group i_missunit /tb/i_dut/i_serpent_dcache_missunit/load_ack
add wave -noupdate -group i_missunit /tb/i_dut/i_serpent_dcache_missunit/store_ack
add wave -noupdate -group i_missunit /tb/i_dut/i_serpent_dcache_missunit/amo_ack
add wave -noupdate -expand -group i_mem /tb/i_dut/i_serpent_dcache_mem/clk_i
add wave -noupdate -expand -group i_mem /tb/i_dut/i_serpent_dcache_mem/rst_ni
add wave -noupdate -expand -group i_mem /tb/i_dut/i_serpent_dcache_mem/rd_tag_i
add wave -noupdate -expand -group i_mem /tb/i_dut/i_serpent_dcache_mem/rd_idx_i
add wave -noupdate -expand -group i_mem /tb/i_dut/i_serpent_dcache_mem/rd_off_i
add wave -noupdate -expand -group i_mem /tb/i_dut/i_serpent_dcache_mem/rd_req_i
add wave -noupdate -expand -group i_mem /tb/i_dut/i_serpent_dcache_mem/wr_cl_vld_i
add wave -noupdate -expand -group i_mem /tb/i_dut/i_serpent_dcache_mem/wr_cl_tag_i
add wave -noupdate -expand -group i_mem /tb/i_dut/i_serpent_dcache_mem/wr_cl_idx_i
add wave -noupdate -expand -group i_mem /tb/i_dut/i_serpent_dcache_mem/wr_cl_off_i
add wave -noupdate -expand -group i_mem /tb/i_dut/i_serpent_dcache_mem/wr_cl_data_i
add wave -noupdate -expand -group i_mem /tb/i_dut/i_serpent_dcache_mem/wr_cl_data_be_i
add wave -noupdate -expand -group i_mem -expand /tb/i_dut/i_serpent_dcache_mem/wr_vld_bits_i
add wave -noupdate -expand -group i_mem /tb/i_dut/i_serpent_dcache_mem/wr_req_i
add wave -noupdate -expand -group i_mem /tb/i_dut/i_serpent_dcache_mem/wr_idx_i
add wave -noupdate -expand -group i_mem /tb/i_dut/i_serpent_dcache_mem/wr_off_i
add wave -noupdate -expand -group i_mem /tb/i_dut/i_serpent_dcache_mem/wr_data_i
add wave -noupdate -expand -group i_mem /tb/i_dut/i_serpent_dcache_mem/wr_data_be_i
add wave -noupdate -expand -group i_mem /tb/i_dut/i_serpent_dcache_mem/wbuffer_data_i
add wave -noupdate -expand -group i_mem /tb/i_dut/i_serpent_dcache_mem/rd_ack_o
add wave -noupdate -expand -group i_mem /tb/i_dut/i_serpent_dcache_mem/rd_vld_bits_o
add wave -noupdate -expand -group i_mem /tb/i_dut/i_serpent_dcache_mem/rd_hit_oh_o
add wave -noupdate -expand -group i_mem /tb/i_dut/i_serpent_dcache_mem/rd_data_o
add wave -noupdate -expand -group i_mem /tb/i_dut/i_serpent_dcache_mem/wr_ack_o
add wave -noupdate -expand -group i_mem /tb/i_dut/i_serpent_dcache_mem/NUM_PORTS
add wave -noupdate -expand -group i_mem /tb/i_dut/i_serpent_dcache_mem/bank_req
add wave -noupdate -expand -group i_mem /tb/i_dut/i_serpent_dcache_mem/bank_we
add wave -noupdate -expand -group i_mem /tb/i_dut/i_serpent_dcache_mem/bank_be
add wave -noupdate -expand -group i_mem /tb/i_dut/i_serpent_dcache_mem/bank_idx
add wave -noupdate -expand -group i_mem /tb/i_dut/i_serpent_dcache_mem/bank_idx_d
add wave -noupdate -expand -group i_mem /tb/i_dut/i_serpent_dcache_mem/bank_idx_q
add wave -noupdate -expand -group i_mem /tb/i_dut/i_serpent_dcache_mem/bank_off_d
add wave -noupdate -expand -group i_mem /tb/i_dut/i_serpent_dcache_mem/bank_off_q
add wave -noupdate -expand -group i_mem /tb/i_dut/i_serpent_dcache_mem/bank_wdata
add wave -noupdate -expand -group i_mem /tb/i_dut/i_serpent_dcache_mem/bank_rdata
add wave -noupdate -expand -group i_mem /tb/i_dut/i_serpent_dcache_mem/rdata_cl
add wave -noupdate -expand -group i_mem /tb/i_dut/i_serpent_dcache_mem/vld_req
add wave -noupdate -expand -group i_mem /tb/i_dut/i_serpent_dcache_mem/vld_we
add wave -noupdate -expand -group i_mem /tb/i_dut/i_serpent_dcache_mem/vld_wdata
add wave -noupdate -expand -group i_mem /tb/i_dut/i_serpent_dcache_mem/tag_rdata
add wave -noupdate -expand -group i_mem /tb/i_dut/i_serpent_dcache_mem/vld_addr
add wave -noupdate -expand -group i_mem /tb/i_dut/i_serpent_dcache_mem/vld_sel_d
add wave -noupdate -expand -group i_mem /tb/i_dut/i_serpent_dcache_mem/vld_sel_q
add wave -noupdate -expand -group i_mem /tb/i_dut/i_serpent_dcache_mem/wbuffer_hit_oh
add wave -noupdate -expand -group i_mem /tb/i_dut/i_serpent_dcache_mem/wbuffer_be
add wave -noupdate -expand -group i_mem /tb/i_dut/i_serpent_dcache_mem/wbuffer_rdata
add wave -noupdate -expand -group i_mem /tb/i_dut/i_serpent_dcache_mem/rdata
add wave -noupdate -expand -group i_mem /tb/i_dut/i_serpent_dcache_mem/wbuffer_cmp_addr
add wave -noupdate -expand -group i_mem /tb/i_dut/i_serpent_dcache_mem/wbuffer_bvalid
add wave -noupdate -expand -group i_mem /tb/i_dut/i_serpent_dcache_mem/wbuffer_data
add wave -noupdate -expand -group i_mem /tb/i_dut/i_serpent_dcache_mem/vld_tag_rdata
add wave -noupdate -group i_ctrl0 {/tb/i_dut/genblk1[0]/i_serpent_dcache_ctrl/clk_i}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/genblk1[0]/i_serpent_dcache_ctrl/rst_ni}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/genblk1[0]/i_serpent_dcache_ctrl/flush_i}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/genblk1[0]/i_serpent_dcache_ctrl/cache_en_i}
add wave -noupdate -group i_ctrl0 -expand {/tb/i_dut/genblk1[0]/i_serpent_dcache_ctrl/req_port_i}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/genblk1[0]/i_serpent_dcache_ctrl/miss_ack_i}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/genblk1[0]/i_serpent_dcache_ctrl/miss_replay_i}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/genblk1[0]/i_serpent_dcache_ctrl/miss_rtrn_vld_i}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/genblk1[0]/i_serpent_dcache_ctrl/rd_ack_i}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/genblk1[0]/i_serpent_dcache_ctrl/rd_data_i}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/genblk1[0]/i_serpent_dcache_ctrl/rd_vld_bits_i}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/genblk1[0]/i_serpent_dcache_ctrl/rd_hit_oh_i}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/genblk1[0]/i_serpent_dcache_ctrl/req_port_o}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/genblk1[0]/i_serpent_dcache_ctrl/miss_req_o}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/genblk1[0]/i_serpent_dcache_ctrl/miss_we_o}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/genblk1[0]/i_serpent_dcache_ctrl/miss_wdata_o}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/genblk1[0]/i_serpent_dcache_ctrl/miss_vld_bits_o}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/genblk1[0]/i_serpent_dcache_ctrl/miss_paddr_o}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/genblk1[0]/i_serpent_dcache_ctrl/miss_nc_o}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/genblk1[0]/i_serpent_dcache_ctrl/miss_size_o}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/genblk1[0]/i_serpent_dcache_ctrl/miss_wr_id_o}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/genblk1[0]/i_serpent_dcache_ctrl/rd_tag_o}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/genblk1[0]/i_serpent_dcache_ctrl/rd_idx_o}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/genblk1[0]/i_serpent_dcache_ctrl/rd_off_o}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/genblk1[0]/i_serpent_dcache_ctrl/rd_req_o}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/genblk1[0]/i_serpent_dcache_ctrl/NC_ADDR_BEGIN}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/genblk1[0]/i_serpent_dcache_ctrl/NC_ADDR_GE_LT}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/genblk1[0]/i_serpent_dcache_ctrl/state_d}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/genblk1[0]/i_serpent_dcache_ctrl/state_q}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/genblk1[0]/i_serpent_dcache_ctrl/address_tag_d}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/genblk1[0]/i_serpent_dcache_ctrl/address_tag_q}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/genblk1[0]/i_serpent_dcache_ctrl/address_idx_d}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/genblk1[0]/i_serpent_dcache_ctrl/address_idx_q}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/genblk1[0]/i_serpent_dcache_ctrl/address_off_d}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/genblk1[0]/i_serpent_dcache_ctrl/address_off_q}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/genblk1[0]/i_serpent_dcache_ctrl/vld_data_d}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/genblk1[0]/i_serpent_dcache_ctrl/vld_data_q}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/genblk1[0]/i_serpent_dcache_ctrl/save_tag}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/genblk1[0]/i_serpent_dcache_ctrl/rd_req_d}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/genblk1[0]/i_serpent_dcache_ctrl/rd_req_q}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/genblk1[0]/i_serpent_dcache_ctrl/data_size_d}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/genblk1[0]/i_serpent_dcache_ctrl/data_size_q}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/genblk1[1]/i_serpent_dcache_ctrl/clk_i}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/genblk1[1]/i_serpent_dcache_ctrl/rst_ni}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/genblk1[1]/i_serpent_dcache_ctrl/flush_i}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/genblk1[1]/i_serpent_dcache_ctrl/cache_en_i}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/genblk1[1]/i_serpent_dcache_ctrl/req_port_i}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/genblk1[1]/i_serpent_dcache_ctrl/miss_ack_i}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/genblk1[1]/i_serpent_dcache_ctrl/miss_replay_i}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/genblk1[1]/i_serpent_dcache_ctrl/miss_rtrn_vld_i}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/genblk1[1]/i_serpent_dcache_ctrl/rd_ack_i}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/genblk1[1]/i_serpent_dcache_ctrl/rd_data_i}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/genblk1[1]/i_serpent_dcache_ctrl/rd_vld_bits_i}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/genblk1[1]/i_serpent_dcache_ctrl/rd_hit_oh_i}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/genblk1[1]/i_serpent_dcache_ctrl/req_port_o}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/genblk1[1]/i_serpent_dcache_ctrl/miss_req_o}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/genblk1[1]/i_serpent_dcache_ctrl/miss_we_o}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/genblk1[1]/i_serpent_dcache_ctrl/miss_wdata_o}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/genblk1[1]/i_serpent_dcache_ctrl/miss_vld_bits_o}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/genblk1[1]/i_serpent_dcache_ctrl/miss_paddr_o}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/genblk1[1]/i_serpent_dcache_ctrl/miss_nc_o}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/genblk1[1]/i_serpent_dcache_ctrl/miss_size_o}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/genblk1[1]/i_serpent_dcache_ctrl/miss_wr_id_o}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/genblk1[1]/i_serpent_dcache_ctrl/rd_tag_o}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/genblk1[1]/i_serpent_dcache_ctrl/rd_idx_o}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/genblk1[1]/i_serpent_dcache_ctrl/rd_off_o}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/genblk1[1]/i_serpent_dcache_ctrl/rd_req_o}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/genblk1[1]/i_serpent_dcache_ctrl/NC_ADDR_BEGIN}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/genblk1[1]/i_serpent_dcache_ctrl/NC_ADDR_GE_LT}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/genblk1[1]/i_serpent_dcache_ctrl/state_d}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/genblk1[1]/i_serpent_dcache_ctrl/state_q}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/genblk1[1]/i_serpent_dcache_ctrl/address_tag_d}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/genblk1[1]/i_serpent_dcache_ctrl/address_tag_q}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/genblk1[1]/i_serpent_dcache_ctrl/address_idx_d}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/genblk1[1]/i_serpent_dcache_ctrl/address_idx_q}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/genblk1[1]/i_serpent_dcache_ctrl/address_off_d}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/genblk1[1]/i_serpent_dcache_ctrl/address_off_q}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/genblk1[1]/i_serpent_dcache_ctrl/vld_data_d}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/genblk1[1]/i_serpent_dcache_ctrl/vld_data_q}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/genblk1[1]/i_serpent_dcache_ctrl/save_tag}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/genblk1[1]/i_serpent_dcache_ctrl/rd_req_d}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/genblk1[1]/i_serpent_dcache_ctrl/rd_req_q}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/genblk1[1]/i_serpent_dcache_ctrl/data_size_d}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/genblk1[1]/i_serpent_dcache_ctrl/data_size_q}
TreeUpdate [SetDefaultTree]
quietly WaveActivateNextPane
add wave -noupdate {/tb/i_tb_mem/mem_array_q[6741]}
add wave -noupdate {/tb/i_tb_mem/mem_array_shadow_q[6741]}
add wave -noupdate {/tb/i_tb_mem/mem_array_dirty_q[6741]}
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {31432807547 ps} 0} {{Cursor 2} {29040000 ps} 0} {{Cursor 3} {1027790000 ps} 0}
quietly wave cursor active 2
configure wave -namecolwidth 375
configure wave -valuecolwidth 224
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
WaveRestoreZoom {0 ps} {103267500 ps}
