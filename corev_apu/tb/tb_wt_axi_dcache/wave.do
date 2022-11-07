onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /tb/*
add wave -noupdate -divider Modules
add wave -noupdate -expand -group i_dut /tb/i_dut/i_wt_dcache/clk_i
add wave -noupdate -expand -group i_dut /tb/i_dut/i_wt_dcache/rst_ni
add wave -noupdate -expand -group i_dut /tb/i_dut/i_wt_dcache/enable_i
add wave -noupdate -expand -group i_dut /tb/i_dut/i_wt_dcache/flush_i
add wave -noupdate -expand -group i_dut /tb/i_dut/i_wt_dcache/amo_req_i
add wave -noupdate -expand -group i_dut -expand -subitemconfig {{/tb/i_dut/i_wt_dcache/req_ports_i[1]} -expand} /tb/i_dut/i_wt_dcache/req_ports_i
add wave -noupdate -expand -group i_dut /tb/i_dut/i_wt_dcache/mem_rtrn_vld_i
add wave -noupdate -expand -group i_dut /tb/i_dut/i_wt_dcache/mem_rtrn_i
add wave -noupdate -expand -group i_dut /tb/i_dut/i_wt_dcache/mem_data_ack_i
add wave -noupdate -expand -group i_dut /tb/i_dut/i_wt_dcache/cache_en
add wave -noupdate -expand -group i_dut /tb/i_dut/i_wt_dcache/wr_cl_vld
add wave -noupdate -expand -group i_dut /tb/i_dut/i_wt_dcache/wr_cl_tag
add wave -noupdate -expand -group i_dut /tb/i_dut/i_wt_dcache/wr_cl_idx
add wave -noupdate -expand -group i_dut /tb/i_dut/i_wt_dcache/wr_cl_off
add wave -noupdate -expand -group i_dut /tb/i_dut/i_wt_dcache/wr_cl_data
add wave -noupdate -expand -group i_dut /tb/i_dut/i_wt_dcache/wr_cl_data_be
add wave -noupdate -expand -group i_dut /tb/i_dut/i_wt_dcache/wr_vld_bits
add wave -noupdate -expand -group i_dut /tb/i_dut/i_wt_dcache/wr_req
add wave -noupdate -expand -group i_dut /tb/i_dut/i_wt_dcache/wr_ack
add wave -noupdate -expand -group i_dut /tb/i_dut/i_wt_dcache/wr_idx
add wave -noupdate -expand -group i_dut /tb/i_dut/i_wt_dcache/wr_off
add wave -noupdate -expand -group i_dut /tb/i_dut/i_wt_dcache/wr_data
add wave -noupdate -expand -group i_dut /tb/i_dut/i_wt_dcache/wr_data_be
add wave -noupdate -expand -group i_dut /tb/i_dut/i_wt_dcache/miss_req
add wave -noupdate -expand -group i_dut /tb/i_dut/i_wt_dcache/miss_ack
add wave -noupdate -expand -group i_dut /tb/i_dut/i_wt_dcache/miss_nc
add wave -noupdate -expand -group i_dut /tb/i_dut/i_wt_dcache/miss_we
add wave -noupdate -expand -group i_dut /tb/i_dut/i_wt_dcache/miss_wdata
add wave -noupdate -expand -group i_dut /tb/i_dut/i_wt_dcache/miss_paddr
add wave -noupdate -expand -group i_dut /tb/i_dut/i_wt_dcache/miss_vld_bits
add wave -noupdate -expand -group i_dut /tb/i_dut/i_wt_dcache/miss_size
add wave -noupdate -expand -group i_dut /tb/i_dut/i_wt_dcache/miss_rtrn_vld
add wave -noupdate -expand -group i_dut /tb/i_dut/i_wt_dcache/miss_rtrn_id
add wave -noupdate -expand -group i_dut /tb/i_dut/i_wt_dcache/rd_req
add wave -noupdate -expand -group i_dut /tb/i_dut/i_wt_dcache/rd_ack
add wave -noupdate -expand -group i_dut /tb/i_dut/i_wt_dcache/rd_tag
add wave -noupdate -expand -group i_dut /tb/i_dut/i_wt_dcache/rd_idx
add wave -noupdate -expand -group i_dut /tb/i_dut/i_wt_dcache/rd_off
add wave -noupdate -expand -group i_dut /tb/i_dut/i_wt_dcache/rd_data
add wave -noupdate -expand -group i_dut /tb/i_dut/i_wt_dcache/rd_vld_bits
add wave -noupdate -expand -group i_dut /tb/i_dut/i_wt_dcache/rd_hit_oh
add wave -noupdate -expand -group i_dut /tb/i_dut/i_wt_dcache/wbuffer_data
add wave -noupdate -expand -group i_dut /tb/i_dut/i_wt_dcache/flush_ack_o
add wave -noupdate -expand -group i_dut /tb/i_dut/i_wt_dcache/miss_o
add wave -noupdate -expand -group i_dut /tb/i_dut/i_wt_dcache/wbuffer_empty_o
add wave -noupdate -expand -group i_dut /tb/i_dut/i_wt_dcache/req_ports_o
add wave -noupdate -expand -group i_dut /tb/i_dut/i_wt_dcache/mem_data_req_o
add wave -noupdate -expand -group i_dut /tb/i_dut/i_wt_dcache/mem_data_o
add wave -noupdate -group i_wbuffer /tb/i_dut/i_wt_dcache/i_wt_dcache_wbuffer/clk_i
add wave -noupdate -group i_wbuffer /tb/i_dut/i_wt_dcache/i_wt_dcache_wbuffer/rst_ni
add wave -noupdate -group i_wbuffer /tb/i_dut/i_wt_dcache/i_wt_dcache_wbuffer/cache_en_i
add wave -noupdate -group i_wbuffer -color Magenta /tb/i_dut/i_wt_dcache/i_wt_dcache_wbuffer/req_port_i
add wave -noupdate -group i_wbuffer -color Magenta /tb/i_dut/i_wt_dcache/i_wt_dcache_wbuffer/req_port_o
add wave -noupdate -group i_wbuffer /tb/i_dut/i_wt_dcache/i_wt_dcache_wbuffer/miss_ack_i
add wave -noupdate -group i_wbuffer /tb/i_dut/i_wt_dcache/i_wt_dcache_wbuffer/miss_rtrn_vld_i
add wave -noupdate -group i_wbuffer /tb/i_dut/i_wt_dcache/i_wt_dcache_wbuffer/miss_rtrn_id_i
add wave -noupdate -group i_wbuffer /tb/i_dut/i_wt_dcache/i_wt_dcache_wbuffer/rd_ack_i
add wave -noupdate -group i_wbuffer /tb/i_dut/i_wt_dcache/i_wt_dcache_wbuffer/rd_data_i
add wave -noupdate -group i_wbuffer /tb/i_dut/i_wt_dcache/i_wt_dcache_wbuffer/rd_vld_bits_i
add wave -noupdate -group i_wbuffer /tb/i_dut/i_wt_dcache/i_wt_dcache_wbuffer/rd_hit_oh_i
add wave -noupdate -group i_wbuffer /tb/i_dut/i_wt_dcache/i_wt_dcache_wbuffer/wr_ack_i
add wave -noupdate -group i_wbuffer /tb/i_dut/i_wt_dcache/i_wt_dcache_wbuffer/empty_o
add wave -noupdate -group i_wbuffer /tb/i_dut/i_wt_dcache/i_wt_dcache_wbuffer/miss_paddr_o
add wave -noupdate -group i_wbuffer /tb/i_dut/i_wt_dcache/i_wt_dcache_wbuffer/miss_req_o
add wave -noupdate -group i_wbuffer /tb/i_dut/i_wt_dcache/i_wt_dcache_wbuffer/miss_we_o
add wave -noupdate -group i_wbuffer /tb/i_dut/i_wt_dcache/i_wt_dcache_wbuffer/miss_wdata_o
add wave -noupdate -group i_wbuffer /tb/i_dut/i_wt_dcache/i_wt_dcache_wbuffer/miss_vld_bits_o
add wave -noupdate -group i_wbuffer /tb/i_dut/i_wt_dcache/i_wt_dcache_wbuffer/miss_nc_o
add wave -noupdate -group i_wbuffer /tb/i_dut/i_wt_dcache/i_wt_dcache_wbuffer/miss_size_o
add wave -noupdate -group i_wbuffer /tb/i_dut/i_wt_dcache/i_wt_dcache_wbuffer/rd_tag_o
add wave -noupdate -group i_wbuffer /tb/i_dut/i_wt_dcache/i_wt_dcache_wbuffer/rd_idx_o
add wave -noupdate -group i_wbuffer /tb/i_dut/i_wt_dcache/i_wt_dcache_wbuffer/rd_off_o
add wave -noupdate -group i_wbuffer /tb/i_dut/i_wt_dcache/i_wt_dcache_wbuffer/rd_req_o
add wave -noupdate -group i_wbuffer /tb/i_dut/i_wt_dcache/i_wt_dcache_wbuffer/wr_req_o
add wave -noupdate -group i_wbuffer /tb/i_dut/i_wt_dcache/i_wt_dcache_wbuffer/wr_idx_o
add wave -noupdate -group i_wbuffer /tb/i_dut/i_wt_dcache/i_wt_dcache_wbuffer/wr_off_o
add wave -noupdate -group i_wbuffer /tb/i_dut/i_wt_dcache/i_wt_dcache_wbuffer/wr_data_o
add wave -noupdate -group i_wbuffer /tb/i_dut/i_wt_dcache/i_wt_dcache_wbuffer/wr_data_be_o
add wave -noupdate -group i_wbuffer /tb/i_dut/i_wt_dcache/i_wt_dcache_wbuffer/wbuffer_data_o
add wave -noupdate -group i_wbuffer /tb/i_dut/i_wt_dcache/i_wt_dcache_wbuffer/tx_stat_d
add wave -noupdate -group i_wbuffer /tb/i_dut/i_wt_dcache/i_wt_dcache_wbuffer/tx_stat_q
add wave -noupdate -group i_wbuffer /tb/i_dut/i_wt_dcache/i_wt_dcache_wbuffer/wbuffer_q
add wave -noupdate -group i_wbuffer /tb/i_dut/i_wt_dcache/i_wt_dcache_wbuffer/wbuffer_d
add wave -noupdate -group i_wbuffer /tb/i_dut/i_wt_dcache/i_wt_dcache_wbuffer/valid
add wave -noupdate -group i_wbuffer -color Magenta /tb/i_dut/i_wt_dcache/i_wt_dcache_wbuffer/debug_paddr
add wave -noupdate -group i_wbuffer /tb/i_dut/i_wt_dcache/i_wt_dcache_wbuffer/dirty
add wave -noupdate -group i_wbuffer /tb/i_dut/i_wt_dcache/i_wt_dcache_wbuffer/tocheck
add wave -noupdate -group i_wbuffer /tb/i_dut/i_wt_dcache/i_wt_dcache_wbuffer/wbuffer_hit_oh
add wave -noupdate -group i_wbuffer /tb/i_dut/i_wt_dcache/i_wt_dcache_wbuffer/inval_hit
add wave -noupdate -group i_wbuffer /tb/i_dut/i_wt_dcache/i_wt_dcache_wbuffer/bdirty
add wave -noupdate -group i_wbuffer /tb/i_dut/i_wt_dcache/i_wt_dcache_wbuffer/next_ptr
add wave -noupdate -group i_wbuffer /tb/i_dut/i_wt_dcache/i_wt_dcache_wbuffer/dirty_ptr
add wave -noupdate -group i_wbuffer /tb/i_dut/i_wt_dcache/i_wt_dcache_wbuffer/hit_ptr
add wave -noupdate -group i_wbuffer /tb/i_dut/i_wt_dcache/i_wt_dcache_wbuffer/wr_ptr
add wave -noupdate -group i_wbuffer /tb/i_dut/i_wt_dcache/i_wt_dcache_wbuffer/check_ptr_d
add wave -noupdate -group i_wbuffer /tb/i_dut/i_wt_dcache/i_wt_dcache_wbuffer/check_ptr_q
add wave -noupdate -group i_wbuffer /tb/i_dut/i_wt_dcache/i_wt_dcache_wbuffer/rtrn_ptr
add wave -noupdate -group i_wbuffer /tb/i_dut/i_wt_dcache/i_wt_dcache_wbuffer/rtrn_id
add wave -noupdate -group i_wbuffer /tb/i_dut/i_wt_dcache/i_wt_dcache_wbuffer/bdirty_off
add wave -noupdate -group i_wbuffer /tb/i_dut/i_wt_dcache/i_wt_dcache_wbuffer/tx_be
add wave -noupdate -group i_wbuffer /tb/i_dut/i_wt_dcache/i_wt_dcache_wbuffer/wr_paddr
add wave -noupdate -group i_wbuffer /tb/i_dut/i_wt_dcache/i_wt_dcache_wbuffer/rd_paddr
add wave -noupdate -group i_wbuffer /tb/i_dut/i_wt_dcache/i_wt_dcache_wbuffer/check_en_d
add wave -noupdate -group i_wbuffer /tb/i_dut/i_wt_dcache/i_wt_dcache_wbuffer/check_en_q
add wave -noupdate -group i_wbuffer /tb/i_dut/i_wt_dcache/i_wt_dcache_wbuffer/full
add wave -noupdate -group i_wbuffer /tb/i_dut/i_wt_dcache/i_wt_dcache_wbuffer/dirty_rd_en
add wave -noupdate -group i_wbuffer /tb/i_dut/i_wt_dcache/i_wt_dcache_wbuffer/rdy
add wave -noupdate -group i_wbuffer /tb/i_dut/i_wt_dcache/i_wt_dcache_wbuffer/rtrn_empty
add wave -noupdate -group i_wbuffer /tb/i_dut/i_wt_dcache/i_wt_dcache_wbuffer/evict
add wave -noupdate -group i_wbuffer /tb/i_dut/i_wt_dcache/i_wt_dcache_wbuffer/ni_pending_d
add wave -noupdate -group i_wbuffer /tb/i_dut/i_wt_dcache/i_wt_dcache_wbuffer/ni_pending_q
add wave -noupdate -group i_wbuffer /tb/i_dut/i_wt_dcache/i_wt_dcache_wbuffer/is_ni
add wave -noupdate -group i_wbuffer /tb/i_dut/i_wt_dcache/i_wt_dcache_wbuffer/is_nc_miss
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/clk_i
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/rst_ni
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/enable_i
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/flush_i
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/wbuffer_empty_i
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/amo_req_i
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/miss_req_i
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/miss_nc_i
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/miss_we_i
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/miss_wdata_i
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/miss_paddr_i
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/miss_vld_bits_i
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/miss_size_i
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/miss_id_i
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/tx_paddr_i
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/tx_vld_i
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/mem_rtrn_vld_i
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/mem_rtrn_i
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/mem_data_ack_i
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/AxiCompliant
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/AmoTxId
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/NumPorts
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/state_d
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/state_q
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/mshr_d
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/mshr_q
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/repl_way
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/inv_way
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/rnd_way
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/mshr_vld_d
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/mshr_vld_q
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/mshr_vld_q1
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/mshr_allocate
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/update_lfsr
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/all_ways_valid
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/enable_d
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/enable_q
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/flush_ack_d
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/flush_ack_q
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/flush_en
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/flush_done
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/mask_reads
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/lock_reqs
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/amo_sel
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/miss_is_write
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/amo_data
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/tmp_paddr
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/amo_rtrn_mux
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/miss_port_idx
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/cnt_d
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/cnt_q
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/miss_req_masked_d
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/miss_req_masked_q
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/inv_vld
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/inv_vld_all
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/cl_write_en
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/load_ack
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/store_ack
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/amo_ack
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/mshr_rdrd_collision_d
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/mshr_rdrd_collision_q
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/mshr_rdrd_collision
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/tx_rdwr_collision
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/mshr_rdwr_collision
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/flush_ack_o
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/miss_o
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/cache_en_o
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/amo_resp_o
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/miss_ack_o
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/miss_replay_o
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/miss_rtrn_vld_o
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/miss_rtrn_id_o
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/wr_cl_vld_o
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/wr_cl_nc_o
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/wr_cl_we_o
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/wr_cl_tag_o
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/wr_cl_idx_o
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/wr_cl_off_o
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/wr_cl_data_o
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/wr_cl_data_be_o
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/wr_vld_bits_o
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/mem_data_req_o
add wave -noupdate -group i_missunit /tb/i_dut/i_wt_dcache/i_wt_dcache_missunit/mem_data_o
add wave -noupdate -group i_mem /tb/i_dut/i_wt_dcache/i_wt_dcache_mem/clk_i
add wave -noupdate -group i_mem /tb/i_dut/i_wt_dcache/i_wt_dcache_mem/rst_ni
add wave -noupdate -group i_mem /tb/i_dut/i_wt_dcache/i_wt_dcache_mem/rd_tag_i
add wave -noupdate -group i_mem /tb/i_dut/i_wt_dcache/i_wt_dcache_mem/rd_idx_i
add wave -noupdate -group i_mem /tb/i_dut/i_wt_dcache/i_wt_dcache_mem/rd_off_i
add wave -noupdate -group i_mem -expand /tb/i_dut/i_wt_dcache/i_wt_dcache_mem/rd_req_i
add wave -noupdate -group i_mem /tb/i_dut/i_wt_dcache/i_wt_dcache_mem/wr_cl_vld_i
add wave -noupdate -group i_mem /tb/i_dut/i_wt_dcache/i_wt_dcache_mem/wr_cl_tag_i
add wave -noupdate -group i_mem /tb/i_dut/i_wt_dcache/i_wt_dcache_mem/wr_cl_idx_i
add wave -noupdate -group i_mem /tb/i_dut/i_wt_dcache/i_wt_dcache_mem/wr_cl_off_i
add wave -noupdate -group i_mem /tb/i_dut/i_wt_dcache/i_wt_dcache_mem/wr_cl_data_i
add wave -noupdate -group i_mem /tb/i_dut/i_wt_dcache/i_wt_dcache_mem/wr_cl_data_be_i
add wave -noupdate -group i_mem /tb/i_dut/i_wt_dcache/i_wt_dcache_mem/wr_vld_bits_i
add wave -noupdate -group i_mem /tb/i_dut/i_wt_dcache/i_wt_dcache_mem/wr_req_i
add wave -noupdate -group i_mem /tb/i_dut/i_wt_dcache/i_wt_dcache_mem/wr_idx_i
add wave -noupdate -group i_mem /tb/i_dut/i_wt_dcache/i_wt_dcache_mem/wr_off_i
add wave -noupdate -group i_mem /tb/i_dut/i_wt_dcache/i_wt_dcache_mem/wr_data_i
add wave -noupdate -group i_mem /tb/i_dut/i_wt_dcache/i_wt_dcache_mem/wr_data_be_i
add wave -noupdate -group i_mem /tb/i_dut/i_wt_dcache/i_wt_dcache_mem/wbuffer_data_i
add wave -noupdate -group i_mem -expand /tb/i_dut/i_wt_dcache/i_wt_dcache_mem/rd_ack_o
add wave -noupdate -group i_mem /tb/i_dut/i_wt_dcache/i_wt_dcache_mem/rd_vld_bits_o
add wave -noupdate -group i_mem /tb/i_dut/i_wt_dcache/i_wt_dcache_mem/rd_hit_oh_o
add wave -noupdate -group i_mem /tb/i_dut/i_wt_dcache/i_wt_dcache_mem/rd_data_o
add wave -noupdate -group i_mem /tb/i_dut/i_wt_dcache/i_wt_dcache_mem/wr_ack_o
add wave -noupdate -group i_mem /tb/i_dut/i_wt_dcache/i_wt_dcache_mem/bank_req
add wave -noupdate -group i_mem /tb/i_dut/i_wt_dcache/i_wt_dcache_mem/bank_we
add wave -noupdate -group i_mem /tb/i_dut/i_wt_dcache/i_wt_dcache_mem/bank_be
add wave -noupdate -group i_mem /tb/i_dut/i_wt_dcache/i_wt_dcache_mem/bank_idx
add wave -noupdate -group i_mem /tb/i_dut/i_wt_dcache/i_wt_dcache_mem/bank_idx_d
add wave -noupdate -group i_mem /tb/i_dut/i_wt_dcache/i_wt_dcache_mem/bank_idx_q
add wave -noupdate -group i_mem /tb/i_dut/i_wt_dcache/i_wt_dcache_mem/bank_off_d
add wave -noupdate -group i_mem /tb/i_dut/i_wt_dcache/i_wt_dcache_mem/bank_off_q
add wave -noupdate -group i_mem /tb/i_dut/i_wt_dcache/i_wt_dcache_mem/bank_wdata
add wave -noupdate -group i_mem /tb/i_dut/i_wt_dcache/i_wt_dcache_mem/bank_rdata
add wave -noupdate -group i_mem /tb/i_dut/i_wt_dcache/i_wt_dcache_mem/rdata_cl
add wave -noupdate -group i_mem /tb/i_dut/i_wt_dcache/i_wt_dcache_mem/vld_req
add wave -noupdate -group i_mem /tb/i_dut/i_wt_dcache/i_wt_dcache_mem/vld_we
add wave -noupdate -group i_mem /tb/i_dut/i_wt_dcache/i_wt_dcache_mem/vld_wdata
add wave -noupdate -group i_mem /tb/i_dut/i_wt_dcache/i_wt_dcache_mem/tag_rdata
add wave -noupdate -group i_mem /tb/i_dut/i_wt_dcache/i_wt_dcache_mem/vld_addr
add wave -noupdate -group i_mem /tb/i_dut/i_wt_dcache/i_wt_dcache_mem/vld_sel_d
add wave -noupdate -group i_mem /tb/i_dut/i_wt_dcache/i_wt_dcache_mem/vld_sel_q
add wave -noupdate -group i_mem /tb/i_dut/i_wt_dcache/i_wt_dcache_mem/wbuffer_hit_oh
add wave -noupdate -group i_mem /tb/i_dut/i_wt_dcache/i_wt_dcache_mem/wbuffer_be
add wave -noupdate -group i_mem /tb/i_dut/i_wt_dcache/i_wt_dcache_mem/wbuffer_rdata
add wave -noupdate -group i_mem /tb/i_dut/i_wt_dcache/i_wt_dcache_mem/rdata
add wave -noupdate -group i_mem /tb/i_dut/i_wt_dcache/i_wt_dcache_mem/wbuffer_cmp_addr
add wave -noupdate -group i_mem /tb/i_dut/i_wt_dcache/i_wt_dcache_mem/vld_tag_rdata
add wave -noupdate -group i_ctrl0 {/tb/i_dut/i_wt_dcache/gen_rd_ports[0]/i_wt_dcache_ctrl/clk_i}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/i_wt_dcache/gen_rd_ports[0]/i_wt_dcache_ctrl/rst_ni}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/i_wt_dcache/gen_rd_ports[0]/i_wt_dcache_ctrl/cache_en_i}
add wave -noupdate -group i_ctrl0 -expand {/tb/i_dut/i_wt_dcache/gen_rd_ports[0]/i_wt_dcache_ctrl/req_port_i}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/i_wt_dcache/gen_rd_ports[0]/i_wt_dcache_ctrl/miss_ack_i}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/i_wt_dcache/gen_rd_ports[0]/i_wt_dcache_ctrl/miss_replay_i}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/i_wt_dcache/gen_rd_ports[0]/i_wt_dcache_ctrl/miss_rtrn_vld_i}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/i_wt_dcache/gen_rd_ports[0]/i_wt_dcache_ctrl/rd_ack_i}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/i_wt_dcache/gen_rd_ports[0]/i_wt_dcache_ctrl/rd_data_i}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/i_wt_dcache/gen_rd_ports[0]/i_wt_dcache_ctrl/rd_vld_bits_i}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/i_wt_dcache/gen_rd_ports[0]/i_wt_dcache_ctrl/rd_hit_oh_i}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/i_wt_dcache/gen_rd_ports[0]/i_wt_dcache_ctrl/req_port_o}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/i_wt_dcache/gen_rd_ports[0]/i_wt_dcache_ctrl/miss_req_o}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/i_wt_dcache/gen_rd_ports[0]/i_wt_dcache_ctrl/miss_we_o}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/i_wt_dcache/gen_rd_ports[0]/i_wt_dcache_ctrl/miss_wdata_o}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/i_wt_dcache/gen_rd_ports[0]/i_wt_dcache_ctrl/miss_vld_bits_o}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/i_wt_dcache/gen_rd_ports[0]/i_wt_dcache_ctrl/miss_paddr_o}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/i_wt_dcache/gen_rd_ports[0]/i_wt_dcache_ctrl/miss_nc_o}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/i_wt_dcache/gen_rd_ports[0]/i_wt_dcache_ctrl/miss_size_o}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/i_wt_dcache/gen_rd_ports[0]/i_wt_dcache_ctrl/rd_tag_o}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/i_wt_dcache/gen_rd_ports[0]/i_wt_dcache_ctrl/rd_idx_o}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/i_wt_dcache/gen_rd_ports[0]/i_wt_dcache_ctrl/rd_off_o}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/i_wt_dcache/gen_rd_ports[0]/i_wt_dcache_ctrl/rd_req_o}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/i_wt_dcache/gen_rd_ports[0]/i_wt_dcache_ctrl/state_d}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/i_wt_dcache/gen_rd_ports[0]/i_wt_dcache_ctrl/state_q}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/i_wt_dcache/gen_rd_ports[0]/i_wt_dcache_ctrl/address_tag_d}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/i_wt_dcache/gen_rd_ports[0]/i_wt_dcache_ctrl/address_tag_q}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/i_wt_dcache/gen_rd_ports[0]/i_wt_dcache_ctrl/address_idx_d}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/i_wt_dcache/gen_rd_ports[0]/i_wt_dcache_ctrl/address_idx_q}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/i_wt_dcache/gen_rd_ports[0]/i_wt_dcache_ctrl/address_off_d}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/i_wt_dcache/gen_rd_ports[0]/i_wt_dcache_ctrl/address_off_q}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/i_wt_dcache/gen_rd_ports[0]/i_wt_dcache_ctrl/vld_data_d}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/i_wt_dcache/gen_rd_ports[0]/i_wt_dcache_ctrl/vld_data_q}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/i_wt_dcache/gen_rd_ports[0]/i_wt_dcache_ctrl/save_tag}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/i_wt_dcache/gen_rd_ports[0]/i_wt_dcache_ctrl/rd_req_d}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/i_wt_dcache/gen_rd_ports[0]/i_wt_dcache_ctrl/rd_req_q}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/i_wt_dcache/gen_rd_ports[0]/i_wt_dcache_ctrl/data_size_d}
add wave -noupdate -group i_ctrl0 {/tb/i_dut/i_wt_dcache/gen_rd_ports[0]/i_wt_dcache_ctrl/data_size_q}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/i_wt_dcache/gen_rd_ports[1]/i_wt_dcache_ctrl/clk_i}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/i_wt_dcache/gen_rd_ports[1]/i_wt_dcache_ctrl/rst_ni}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/i_wt_dcache/gen_rd_ports[1]/i_wt_dcache_ctrl/cache_en_i}
add wave -noupdate -group i_ctrl1 -expand {/tb/i_dut/i_wt_dcache/gen_rd_ports[1]/i_wt_dcache_ctrl/req_port_i}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/i_wt_dcache/gen_rd_ports[1]/i_wt_dcache_ctrl/miss_ack_i}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/i_wt_dcache/gen_rd_ports[1]/i_wt_dcache_ctrl/miss_replay_i}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/i_wt_dcache/gen_rd_ports[1]/i_wt_dcache_ctrl/miss_rtrn_vld_i}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/i_wt_dcache/gen_rd_ports[1]/i_wt_dcache_ctrl/rd_ack_i}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/i_wt_dcache/gen_rd_ports[1]/i_wt_dcache_ctrl/rd_data_i}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/i_wt_dcache/gen_rd_ports[1]/i_wt_dcache_ctrl/rd_vld_bits_i}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/i_wt_dcache/gen_rd_ports[1]/i_wt_dcache_ctrl/rd_hit_oh_i}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/i_wt_dcache/gen_rd_ports[1]/i_wt_dcache_ctrl/req_port_o}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/i_wt_dcache/gen_rd_ports[1]/i_wt_dcache_ctrl/miss_req_o}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/i_wt_dcache/gen_rd_ports[1]/i_wt_dcache_ctrl/miss_we_o}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/i_wt_dcache/gen_rd_ports[1]/i_wt_dcache_ctrl/miss_wdata_o}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/i_wt_dcache/gen_rd_ports[1]/i_wt_dcache_ctrl/miss_vld_bits_o}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/i_wt_dcache/gen_rd_ports[1]/i_wt_dcache_ctrl/miss_paddr_o}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/i_wt_dcache/gen_rd_ports[1]/i_wt_dcache_ctrl/miss_nc_o}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/i_wt_dcache/gen_rd_ports[1]/i_wt_dcache_ctrl/miss_size_o}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/i_wt_dcache/gen_rd_ports[1]/i_wt_dcache_ctrl/rd_tag_o}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/i_wt_dcache/gen_rd_ports[1]/i_wt_dcache_ctrl/rd_idx_o}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/i_wt_dcache/gen_rd_ports[1]/i_wt_dcache_ctrl/rd_off_o}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/i_wt_dcache/gen_rd_ports[1]/i_wt_dcache_ctrl/rd_req_o}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/i_wt_dcache/gen_rd_ports[1]/i_wt_dcache_ctrl/state_d}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/i_wt_dcache/gen_rd_ports[1]/i_wt_dcache_ctrl/state_q}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/i_wt_dcache/gen_rd_ports[1]/i_wt_dcache_ctrl/address_tag_d}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/i_wt_dcache/gen_rd_ports[1]/i_wt_dcache_ctrl/address_tag_q}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/i_wt_dcache/gen_rd_ports[1]/i_wt_dcache_ctrl/address_idx_d}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/i_wt_dcache/gen_rd_ports[1]/i_wt_dcache_ctrl/address_idx_q}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/i_wt_dcache/gen_rd_ports[1]/i_wt_dcache_ctrl/address_off_d}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/i_wt_dcache/gen_rd_ports[1]/i_wt_dcache_ctrl/address_off_q}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/i_wt_dcache/gen_rd_ports[1]/i_wt_dcache_ctrl/vld_data_d}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/i_wt_dcache/gen_rd_ports[1]/i_wt_dcache_ctrl/vld_data_q}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/i_wt_dcache/gen_rd_ports[1]/i_wt_dcache_ctrl/save_tag}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/i_wt_dcache/gen_rd_ports[1]/i_wt_dcache_ctrl/rd_req_d}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/i_wt_dcache/gen_rd_ports[1]/i_wt_dcache_ctrl/rd_req_q}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/i_wt_dcache/gen_rd_ports[1]/i_wt_dcache_ctrl/data_size_d}
add wave -noupdate -group i_ctrl1 {/tb/i_dut/i_wt_dcache/gen_rd_ports[1]/i_wt_dcache_ctrl/data_size_q}
add wave -noupdate -group i_axi_adapter {/tb/i_dut/i_adapter/*}
add wave -noupdate -group i_axi_shim {/tb/i_dut/i_adapter/i_axi_shim/*}
TreeUpdate [SetDefaultTree]
quietly WaveActivateNextPane
add wave -position insertpoint {sim:/tb_pkg::tb_mem_port::tb_mem_port__1::memory_q[8]}
add wave -position insertpoint {sim:/tb_pkg::tb_mem_port::tb_mem_port__1::shadow_q[8]}
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {31432807547 ps} 0} {{Cursor 2} {17675291 ps} 0} {{Cursor 3} {1027790000 ps} 0}
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
WaveRestoreZoom {0 ps} {56623104 ps}
