onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -group TB /tb/clk_i
add wave -noupdate -group TB /tb/rst_ni
add wave -noupdate -group TB /tb/flush_i
add wave -noupdate -group TB /tb/en_i
add wave -noupdate -group TB /tb/miss_o
add wave -noupdate -group TB /tb/areq_i
add wave -noupdate -group TB /tb/areq_o
add wave -noupdate -group TB /tb/dreq_i
add wave -noupdate -group TB /tb/dreq_o
add wave -noupdate -group TB /tb/mem_rtrn_vld_i
add wave -noupdate -group TB /tb/mem_rtrn_i
add wave -noupdate -group TB /tb/mem_data_req_o
add wave -noupdate -group TB /tb/mem_data_ack_i
add wave -noupdate -group TB /tb/mem_data_o
add wave -noupdate -group TB /tb/stim_start
add wave -noupdate -group TB /tb/stim_end
add wave -noupdate -group TB /tb/end_of_sim
add wave -noupdate -group TB /tb/acq_done
add wave -noupdate -group TB /tb/mem_rand_en
add wave -noupdate -group TB /tb/inv_rand_en
add wave -noupdate -group TB /tb/io_rand_en
add wave -noupdate -group TB /tb/tlb_rand_en
add wave -noupdate -group TB /tb/exception_en
add wave -noupdate -group TB /tb/tlb_offset
add wave -noupdate -group TB /tb/stim_vaddr
add wave -noupdate -group TB /tb/exp_data
add wave -noupdate -group TB /tb/exp_vaddr
add wave -noupdate -group TB /tb/stim_push
add wave -noupdate -group TB /tb/stim_flush
add wave -noupdate -group TB /tb/stim_full
add wave -noupdate -group TB /tb/exp_empty
add wave -noupdate -group TB /tb/exp_pop
add wave -noupdate -group TB /tb/dut_out_vld
add wave -noupdate -group TB /tb/dut_in_rdy
add wave -noupdate -expand -group icache /tb/dut/clk_i
add wave -noupdate -expand -group icache /tb/dut/rst_ni
add wave -noupdate -expand -group icache /tb/dut/flush_i
add wave -noupdate -expand -group icache /tb/dut/en_i
add wave -noupdate -expand -group icache /tb/dut/areq_i
add wave -noupdate -expand -group icache /tb/dut/dreq_i
add wave -noupdate -expand -group icache /tb/dut/mem_rtrn_vld_i
add wave -noupdate -expand -group icache /tb/dut/mem_rtrn_i
add wave -noupdate -expand -group icache /tb/dut/mem_data_ack_i
add wave -noupdate -expand -group icache /tb/dut/NC_ADDR_BEGIN
add wave -noupdate -expand -group icache /tb/dut/NC_ADDR_GE_LE
add wave -noupdate -expand -group icache /tb/dut/cache_en_d
add wave -noupdate -expand -group icache /tb/dut/cache_en_q
add wave -noupdate -expand -group icache /tb/dut/exception_d
add wave -noupdate -expand -group icache /tb/dut/exception_q
add wave -noupdate -expand -group icache /tb/dut/paddr_vld_d
add wave -noupdate -expand -group icache /tb/dut/paddr_vld_q
add wave -noupdate -expand -group icache /tb/dut/vaddr_d
add wave -noupdate -expand -group icache /tb/dut/vaddr_q
add wave -noupdate -expand -group icache /tb/dut/paddr_is_io
add wave -noupdate -expand -group icache /tb/dut/paddr_is_nc
add wave -noupdate -expand -group icache /tb/dut/cl_hit
add wave -noupdate -expand -group icache /tb/dut/cache_rden
add wave -noupdate -expand -group icache /tb/dut/cache_wren
add wave -noupdate -expand -group icache /tb/dut/cmp_en_d
add wave -noupdate -expand -group icache /tb/dut/cmp_en_q
add wave -noupdate -expand -group icache /tb/dut/flush_d
add wave -noupdate -expand -group icache /tb/dut/flush_q
add wave -noupdate -expand -group icache /tb/dut/update_lfsr
add wave -noupdate -expand -group icache /tb/dut/inv_way
add wave -noupdate -expand -group icache /tb/dut/rnd_way
add wave -noupdate -expand -group icache /tb/dut/repl_way
add wave -noupdate -expand -group icache /tb/dut/all_ways_valid
add wave -noupdate -expand -group icache /tb/dut/inv_en
add wave -noupdate -expand -group icache /tb/dut/flush_en
add wave -noupdate -expand -group icache /tb/dut/flush_done
add wave -noupdate -expand -group icache /tb/dut/flush_cnt_d
add wave -noupdate -expand -group icache /tb/dut/flush_cnt_q
add wave -noupdate -expand -group icache /tb/dut/cl_we
add wave -noupdate -expand -group icache /tb/dut/cl_req
add wave -noupdate -expand -group icache /tb/dut/cl_index
add wave -noupdate -expand -group icache /tb/dut/cl_offset_d
add wave -noupdate -expand -group icache /tb/dut/cl_offset_q
add wave -noupdate -expand -group icache /tb/dut/cl_tag_d
add wave -noupdate -expand -group icache /tb/dut/cl_tag_q
add wave -noupdate -expand -group icache /tb/dut/cl_tag_rdata
add wave -noupdate -expand -group icache /tb/dut/cl_rdata
add wave -noupdate -expand -group icache /tb/dut/cl_sel
add wave -noupdate -expand -group icache /tb/dut/vld_biten
add wave -noupdate -expand -group icache /tb/dut/vld_we
add wave -noupdate -expand -group icache /tb/dut/vld_req
add wave -noupdate -expand -group icache /tb/dut/vld_wdata
add wave -noupdate -expand -group icache /tb/dut/vld_rdata
add wave -noupdate -expand -group icache /tb/dut/vld_addr
add wave -noupdate -expand -group icache /tb/dut/state_d
add wave -noupdate -expand -group icache /tb/dut/state_q
add wave -noupdate -expand -group icache /tb/dut/miss_o
add wave -noupdate -expand -group icache /tb/dut/areq_o
add wave -noupdate -expand -group icache /tb/dut/dreq_o
add wave -noupdate -expand -group icache /tb/dut/mem_data_req_o
add wave -noupdate -expand -group icache /tb/dut/mem_data_o
add wave -noupdate -group mem_emul /tb/i_mem_emul/clk_i
add wave -noupdate -group mem_emul /tb/i_mem_emul/rst_ni
add wave -noupdate -group mem_emul /tb/i_mem_emul/mem_rand_en_i
add wave -noupdate -group mem_emul /tb/i_mem_emul/io_rand_en_i
add wave -noupdate -group mem_emul /tb/i_mem_emul/inv_rand_en_i
add wave -noupdate -group mem_emul /tb/i_mem_emul/tlb_offset_i
add wave -noupdate -group mem_emul /tb/i_mem_emul/stim_vaddr_i
add wave -noupdate -group mem_emul /tb/i_mem_emul/stim_push_i
add wave -noupdate -group mem_emul /tb/i_mem_emul/stim_flush_i
add wave -noupdate -group mem_emul /tb/i_mem_emul/stim_full_o
add wave -noupdate -group mem_emul /tb/i_mem_emul/exp_data_o
add wave -noupdate -group mem_emul /tb/i_mem_emul/exp_vaddr_o
add wave -noupdate -group mem_emul /tb/i_mem_emul/exp_empty_o
add wave -noupdate -group mem_emul /tb/i_mem_emul/exp_pop_i
add wave -noupdate -group mem_emul /tb/i_mem_emul/mem_rtrn_vld_o
add wave -noupdate -group mem_emul -expand /tb/i_mem_emul/mem_rtrn_o
add wave -noupdate -group mem_emul /tb/i_mem_emul/mem_data_req_i
add wave -noupdate -group mem_emul /tb/i_mem_emul/mem_data_ack_o
add wave -noupdate -group mem_emul /tb/i_mem_emul/mem_data_i
add wave -noupdate -group mem_emul /tb/i_mem_emul/mem_ready_q
add wave -noupdate -group mem_emul /tb/i_mem_emul/mem_inv_q
add wave -noupdate -group mem_emul /tb/i_mem_emul/rand_addr_q
add wave -noupdate -group mem_emul /tb/i_mem_emul/rand_data_q
add wave -noupdate -group mem_emul /tb/i_mem_emul/outfifo_data
add wave -noupdate -group mem_emul /tb/i_mem_emul/outfifo_pop
add wave -noupdate -group mem_emul /tb/i_mem_emul/outfifo_push
add wave -noupdate -group mem_emul /tb/i_mem_emul/outfifo_full
add wave -noupdate -group mem_emul /tb/i_mem_emul/outfifo_empty
add wave -noupdate -group mem_emul /tb/i_mem_emul/infifo_data
add wave -noupdate -group mem_emul /tb/i_mem_emul/infifo_pop
add wave -noupdate -group mem_emul /tb/i_mem_emul/infifo_push
add wave -noupdate -group mem_emul /tb/i_mem_emul/infifo_full
add wave -noupdate -group mem_emul /tb/i_mem_emul/infifo_empty
add wave -noupdate -group mem_emul /tb/i_mem_emul/stim_addr
add wave -noupdate -group mem_emul /tb/i_mem_emul/exp_empty
add wave -noupdate -group mem_emul /tb/i_mem_emul/initialized_q
add wave -noupdate -group tlb_emul /tb/i_tlb_emul/clk_i
add wave -noupdate -group tlb_emul /tb/i_tlb_emul/rst_ni
add wave -noupdate -group tlb_emul /tb/i_tlb_emul/tlb_rand_en_i
add wave -noupdate -group tlb_emul /tb/i_tlb_emul/exception_en_i
add wave -noupdate -group tlb_emul /tb/i_tlb_emul/tlb_offset_i
add wave -noupdate -group tlb_emul /tb/i_tlb_emul/req_i
add wave -noupdate -group tlb_emul /tb/i_tlb_emul/req_o
add wave -noupdate -group tlb_emul /tb/i_tlb_emul/tlb_ready_d
add wave -noupdate -group tlb_emul /tb/i_tlb_emul/tlb_ready_q
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {3047 ps} 0}
quietly wave cursor active 1
configure wave -namecolwidth 208
configure wave -valuecolwidth 420
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
WaveRestoreZoom {3049926 ps} {3050004 ps}
