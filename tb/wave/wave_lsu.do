onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate -expand -group LSU /lsu_tb/dut/clk_i
add wave -noupdate -expand -group LSU /lsu_tb/dut/rst_ni
add wave -noupdate -expand -group LSU /lsu_tb/dut/flush_i
add wave -noupdate -expand -group LSU /lsu_tb/dut/operator_i
add wave -noupdate -expand -group LSU /lsu_tb/dut/operand_a_i
add wave -noupdate -expand -group LSU /lsu_tb/dut/operand_b_i
add wave -noupdate -expand -group LSU /lsu_tb/dut/imm_i
add wave -noupdate -expand -group LSU /lsu_tb/dut/lsu_ready_o
add wave -noupdate -expand -group LSU /lsu_tb/dut/lsu_valid_i
add wave -noupdate -expand -group LSU /lsu_tb/dut/lsu_trans_id_i
add wave -noupdate -expand -group LSU /lsu_tb/dut/lsu_trans_id_o
add wave -noupdate -expand -group LSU /lsu_tb/dut/lsu_result_o
add wave -noupdate -expand -group LSU /lsu_tb/dut/lsu_valid_o
add wave -noupdate -expand -group LSU /lsu_tb/dut/commit_i
add wave -noupdate -expand -group LSU /lsu_tb/dut/enable_translation_i
add wave -noupdate -expand -group LSU /lsu_tb/dut/fetch_req_i
add wave -noupdate -expand -group LSU /lsu_tb/dut/fetch_gnt_o
add wave -noupdate -expand -group LSU /lsu_tb/dut/fetch_valid_o
add wave -noupdate -expand -group LSU /lsu_tb/dut/fetch_err_o
add wave -noupdate -expand -group LSU /lsu_tb/dut/fetch_vaddr_i
add wave -noupdate -expand -group LSU /lsu_tb/dut/fetch_rdata_o
add wave -noupdate -expand -group LSU /lsu_tb/dut/priv_lvl_i
add wave -noupdate -expand -group LSU /lsu_tb/dut/flag_pum_i
add wave -noupdate -expand -group LSU /lsu_tb/dut/flag_mxr_i
add wave -noupdate -expand -group LSU /lsu_tb/dut/pd_ppn_i
add wave -noupdate -expand -group LSU /lsu_tb/dut/asid_i
add wave -noupdate -expand -group LSU /lsu_tb/dut/flush_tlb_i
add wave -noupdate -expand -group LSU /lsu_tb/dut/lsu_exception_o
add wave -noupdate -expand -group LSU /lsu_tb/dut/data_misaligned
add wave -noupdate -expand -group LSU /lsu_tb/dut/CS
add wave -noupdate -expand -group LSU /lsu_tb/dut/NS
add wave -noupdate -expand -group LSU /lsu_tb/dut/vaddr_i
add wave -noupdate -expand -group LSU /lsu_tb/dut/stall
add wave -noupdate -expand -group LSU /lsu_tb/dut/get_from_register
add wave -noupdate -expand -group LSU /lsu_tb/dut/vaddr
add wave -noupdate -expand -group LSU /lsu_tb/dut/data
add wave -noupdate -expand -group LSU /lsu_tb/dut/be
add wave -noupdate -expand -group LSU /lsu_tb/dut/operator
add wave -noupdate -expand -group LSU /lsu_tb/dut/trans_id
add wave -noupdate -expand -group LSU /lsu_tb/dut/vaddr_q
add wave -noupdate -expand -group LSU /lsu_tb/dut/data_q
add wave -noupdate -expand -group LSU /lsu_tb/dut/operator_q
add wave -noupdate -expand -group LSU /lsu_tb/dut/trans_id_q
add wave -noupdate -expand -group LSU /lsu_tb/dut/st_buffer_paddr
add wave -noupdate -expand -group LSU /lsu_tb/dut/st_buffer_data
add wave -noupdate -expand -group LSU /lsu_tb/dut/st_buffer_be
add wave -noupdate -expand -group LSU /lsu_tb/dut/st_buffer_valid
add wave -noupdate -expand -group LSU /lsu_tb/dut/st_ready
add wave -noupdate -expand -group LSU /lsu_tb/dut/st_valid
add wave -noupdate -expand -group LSU /lsu_tb/dut/translation_req
add wave -noupdate -expand -group LSU /lsu_tb/dut/translation_valid
add wave -noupdate -expand -group LSU /lsu_tb/dut/paddr_o
add wave -noupdate -expand -group LSU /lsu_tb/dut/address_i
add wave -noupdate -expand -group LSU -expand /lsu_tb/dut/data_wdata_i
add wave -noupdate -expand -group LSU -expand /lsu_tb/dut/data_req_i
add wave -noupdate -expand -group LSU /lsu_tb/dut/data_we_i
add wave -noupdate -expand -group LSU /lsu_tb/dut/data_be_i
add wave -noupdate -expand -group LSU /lsu_tb/dut/data_gnt_o
add wave -noupdate -expand -group LSU /lsu_tb/dut/data_rvalid_o
add wave -noupdate -expand -group LSU /lsu_tb/dut/data_rdata_o
add wave -noupdate -expand -group LSU /lsu_tb/dut/rdata
add wave -noupdate -expand -group LSU /lsu_tb/dut/address_match
add wave -noupdate -expand -group LSU /lsu_tb/dut/op
add wave -noupdate -expand -group LSU /lsu_tb/dut/rdata_d_ext
add wave -noupdate -expand -group LSU /lsu_tb/dut/rdata_w_ext
add wave -noupdate -expand -group LSU /lsu_tb/dut/rdata_h_ext
add wave -noupdate -expand -group LSU /lsu_tb/dut/rdata_b_ext
add wave -noupdate -expand -group mem_arbiter /lsu_tb/dut/mem_arbiter_i/clk_i
add wave -noupdate -expand -group mem_arbiter /lsu_tb/dut/mem_arbiter_i/rst_ni
add wave -noupdate -expand -group mem_arbiter /lsu_tb/dut/mem_arbiter_i/flush_ready_o
add wave -noupdate -expand -group mem_arbiter -expand -group Master /lsu_tb/dut/mem_arbiter_i/address_o
add wave -noupdate -expand -group mem_arbiter -expand -group Master /lsu_tb/dut/mem_arbiter_i/data_wdata_o
add wave -noupdate -expand -group mem_arbiter -expand -group Master /lsu_tb/dut/mem_arbiter_i/data_req_o
add wave -noupdate -expand -group mem_arbiter -expand -group Master /lsu_tb/dut/mem_arbiter_i/data_we_o
add wave -noupdate -expand -group mem_arbiter -expand -group Master /lsu_tb/dut/mem_arbiter_i/data_be_o
add wave -noupdate -expand -group mem_arbiter -expand -group Master /lsu_tb/dut/mem_arbiter_i/data_gnt_i
add wave -noupdate -expand -group mem_arbiter -expand -group Master /lsu_tb/dut/mem_arbiter_i/data_rvalid_i
add wave -noupdate -expand -group mem_arbiter -expand -group Master /lsu_tb/dut/mem_arbiter_i/data_rdata_i
add wave -noupdate -expand -group mem_arbiter /lsu_tb/dut/mem_arbiter_i/address_i
add wave -noupdate -expand -group mem_arbiter /lsu_tb/dut/mem_arbiter_i/data_wdata_i
add wave -noupdate -expand -group mem_arbiter -expand /lsu_tb/dut/mem_arbiter_i/data_req_i
add wave -noupdate -expand -group mem_arbiter /lsu_tb/dut/mem_arbiter_i/data_we_i
add wave -noupdate -expand -group mem_arbiter /lsu_tb/dut/mem_arbiter_i/data_be_i
add wave -noupdate -expand -group mem_arbiter /lsu_tb/dut/mem_arbiter_i/data_gnt_o
add wave -noupdate -expand -group mem_arbiter /lsu_tb/dut/mem_arbiter_i/data_rvalid_o
add wave -noupdate -expand -group mem_arbiter /lsu_tb/dut/mem_arbiter_i/data_rdata_o
add wave -noupdate -expand -group mem_arbiter /lsu_tb/dut/mem_arbiter_i/full_o
add wave -noupdate -expand -group mem_arbiter /lsu_tb/dut/mem_arbiter_i/empty_o
add wave -noupdate -expand -group mem_arbiter /lsu_tb/dut/mem_arbiter_i/data_i
add wave -noupdate -expand -group mem_arbiter /lsu_tb/dut/mem_arbiter_i/push_i
add wave -noupdate -expand -group mem_arbiter /lsu_tb/dut/mem_arbiter_i/data_o
add wave -noupdate -expand -group mem_arbiter /lsu_tb/dut/mem_arbiter_i/pop_i
add wave -noupdate -expand -group mem_arbiter /lsu_tb/dut/mem_arbiter_i/single_element_o
add wave -noupdate -group store_queue /lsu_tb/dut/store_queue_i/clk_i
add wave -noupdate -group store_queue /lsu_tb/dut/store_queue_i/rst_ni
add wave -noupdate -group store_queue /lsu_tb/dut/store_queue_i/flush_i
add wave -noupdate -group store_queue /lsu_tb/dut/store_queue_i/paddr_o
add wave -noupdate -group store_queue /lsu_tb/dut/store_queue_i/data_o
add wave -noupdate -group store_queue /lsu_tb/dut/store_queue_i/valid_o
add wave -noupdate -group store_queue /lsu_tb/dut/store_queue_i/be_o
add wave -noupdate -group store_queue /lsu_tb/dut/store_queue_i/commit_i
add wave -noupdate -group store_queue /lsu_tb/dut/store_queue_i/ready_o
add wave -noupdate -group store_queue /lsu_tb/dut/store_queue_i/valid_i
add wave -noupdate -group store_queue /lsu_tb/dut/store_queue_i/paddr_i
add wave -noupdate -group store_queue /lsu_tb/dut/store_queue_i/data_i
add wave -noupdate -group store_queue /lsu_tb/dut/store_queue_i/be_i
add wave -noupdate -group store_queue /lsu_tb/dut/store_queue_i/address_o
add wave -noupdate -group store_queue /lsu_tb/dut/store_queue_i/data_wdata_o
add wave -noupdate -group store_queue /lsu_tb/dut/store_queue_i/data_req_o
add wave -noupdate -group store_queue /lsu_tb/dut/store_queue_i/data_we_o
add wave -noupdate -group store_queue /lsu_tb/dut/store_queue_i/data_be_o
add wave -noupdate -group store_queue /lsu_tb/dut/store_queue_i/data_gnt_i
add wave -noupdate -group store_queue /lsu_tb/dut/store_queue_i/data_rvalid_i
add wave -noupdate -group store_queue /lsu_tb/dut/store_queue_i/commit_queue_n
add wave -noupdate -group store_queue /lsu_tb/dut/store_queue_i/commit_queue_q
add wave -noupdate -group mmu /lsu_tb/dut/i_mmu/clk_i
add wave -noupdate -group mmu /lsu_tb/dut/i_mmu/rst_ni
add wave -noupdate -group mmu /lsu_tb/dut/i_mmu/enable_translation_i
add wave -noupdate -group mmu /lsu_tb/dut/i_mmu/fetch_req_i
add wave -noupdate -group mmu /lsu_tb/dut/i_mmu/fetch_gnt_o
add wave -noupdate -group mmu /lsu_tb/dut/i_mmu/fetch_valid_o
add wave -noupdate -group mmu /lsu_tb/dut/i_mmu/fetch_err_o
add wave -noupdate -group mmu /lsu_tb/dut/i_mmu/fetch_vaddr_i
add wave -noupdate -group mmu /lsu_tb/dut/i_mmu/fetch_rdata_o
add wave -noupdate -group mmu /lsu_tb/dut/i_mmu/lsu_req_i
add wave -noupdate -group mmu /lsu_tb/dut/i_mmu/lsu_vaddr_i
add wave -noupdate -group mmu /lsu_tb/dut/i_mmu/lsu_valid_o
add wave -noupdate -group mmu /lsu_tb/dut/i_mmu/lsu_paddr_o
add wave -noupdate -group mmu /lsu_tb/dut/i_mmu/priv_lvl_i
add wave -noupdate -group mmu /lsu_tb/dut/i_mmu/flag_pum_i
add wave -noupdate -group mmu /lsu_tb/dut/i_mmu/flag_mxr_i
add wave -noupdate -group mmu /lsu_tb/dut/i_mmu/pd_ppn_i
add wave -noupdate -group mmu /lsu_tb/dut/i_mmu/asid_i
add wave -noupdate -group mmu /lsu_tb/dut/i_mmu/flush_tlb_i
add wave -noupdate -group mmu /lsu_tb/dut/i_mmu/fetch_paddr
add wave -noupdate -group mmu /lsu_tb/dut/i_mmu/fetch_req
add wave -noupdate -group mmu /lsu_tb/dut/i_mmu/ierr_valid_q
add wave -noupdate -group mmu /lsu_tb/dut/i_mmu/ierr_valid_n
add wave -noupdate -group mmu /lsu_tb/dut/i_mmu/iaccess_err
add wave -noupdate -group mmu /lsu_tb/dut/i_mmu/ptw_active
add wave -noupdate -group mmu /lsu_tb/dut/i_mmu/walking_instr
add wave -noupdate -group mmu /lsu_tb/dut/i_mmu/ptw_error
add wave -noupdate -group mmu /lsu_tb/dut/i_mmu/update_is_2M
add wave -noupdate -group mmu /lsu_tb/dut/i_mmu/update_is_1G
add wave -noupdate -group mmu /lsu_tb/dut/i_mmu/update_vpn
add wave -noupdate -group mmu /lsu_tb/dut/i_mmu/update_asid
add wave -noupdate -group mmu /lsu_tb/dut/i_mmu/update_content
add wave -noupdate -group mmu /lsu_tb/dut/i_mmu/itlb_update
add wave -noupdate -group mmu /lsu_tb/dut/i_mmu/itlb_lu_access
add wave -noupdate -group mmu /lsu_tb/dut/i_mmu/itlb_content
add wave -noupdate -group mmu /lsu_tb/dut/i_mmu/itlb_is_2M
add wave -noupdate -group mmu /lsu_tb/dut/i_mmu/itlb_is_1G
add wave -noupdate -group mmu /lsu_tb/dut/i_mmu/itlb_lu_hit
add wave -noupdate -group mmu /lsu_tb/dut/i_mmu/dtlb_update
add wave -noupdate -group mmu /lsu_tb/dut/i_mmu/dtlb_lu_access
add wave -noupdate -group mmu /lsu_tb/dut/i_mmu/dtlb_content
add wave -noupdate -group mmu /lsu_tb/dut/i_mmu/dtlb_is_2M
add wave -noupdate -group mmu /lsu_tb/dut/i_mmu/dtlb_is_1G
add wave -noupdate -group mmu /lsu_tb/dut/i_mmu/dtlb_lu_hit
add wave -noupdate -group PTW /lsu_tb/dut/i_mmu/ptw_i/clk_i
add wave -noupdate -group PTW /lsu_tb/dut/i_mmu/ptw_i/rst_ni
add wave -noupdate -group PTW /lsu_tb/dut/i_mmu/ptw_i/flush_i
add wave -noupdate -group PTW /lsu_tb/dut/i_mmu/ptw_i/ptw_active_o
add wave -noupdate -group PTW /lsu_tb/dut/i_mmu/ptw_i/walking_instr_o
add wave -noupdate -group PTW /lsu_tb/dut/i_mmu/ptw_i/ptw_error_o
add wave -noupdate -group PTW /lsu_tb/dut/i_mmu/ptw_i/enable_translation_i
add wave -noupdate -group PTW /lsu_tb/dut/i_mmu/ptw_i/address_o
add wave -noupdate -group PTW /lsu_tb/dut/i_mmu/ptw_i/data_wdata_o
add wave -noupdate -group PTW /lsu_tb/dut/i_mmu/ptw_i/data_req_o
add wave -noupdate -group PTW /lsu_tb/dut/i_mmu/ptw_i/data_we_o
add wave -noupdate -group PTW /lsu_tb/dut/i_mmu/ptw_i/data_be_o
add wave -noupdate -group PTW /lsu_tb/dut/i_mmu/ptw_i/data_gnt_i
add wave -noupdate -group PTW /lsu_tb/dut/i_mmu/ptw_i/data_rvalid_i
add wave -noupdate -group PTW /lsu_tb/dut/i_mmu/ptw_i/data_rdata_i
add wave -noupdate -group PTW /lsu_tb/dut/i_mmu/ptw_i/itlb_update_o
add wave -noupdate -group PTW /lsu_tb/dut/i_mmu/ptw_i/dtlb_update_o
add wave -noupdate -group PTW /lsu_tb/dut/i_mmu/ptw_i/update_content_o
add wave -noupdate -group PTW /lsu_tb/dut/i_mmu/ptw_i/update_is_2M_o
add wave -noupdate -group PTW /lsu_tb/dut/i_mmu/ptw_i/update_is_1G_o
add wave -noupdate -group PTW /lsu_tb/dut/i_mmu/ptw_i/update_vpn_o
add wave -noupdate -group PTW /lsu_tb/dut/i_mmu/ptw_i/update_asid_o
add wave -noupdate -group PTW /lsu_tb/dut/i_mmu/ptw_i/asid_i
add wave -noupdate -group PTW /lsu_tb/dut/i_mmu/ptw_i/itlb_access_i
add wave -noupdate -group PTW /lsu_tb/dut/i_mmu/ptw_i/itlb_miss_i
add wave -noupdate -group PTW /lsu_tb/dut/i_mmu/ptw_i/itlb_vaddr_i
add wave -noupdate -group PTW /lsu_tb/dut/i_mmu/ptw_i/dtlb_access_i
add wave -noupdate -group PTW /lsu_tb/dut/i_mmu/ptw_i/dtlb_miss_i
add wave -noupdate -group PTW /lsu_tb/dut/i_mmu/ptw_i/dtlb_vaddr_i
add wave -noupdate -group PTW /lsu_tb/dut/i_mmu/ptw_i/pd_ppn_i
add wave -noupdate -group PTW /lsu_tb/dut/i_mmu/ptw_i/flag_mxr_i
add wave -noupdate -group PTW /lsu_tb/dut/i_mmu/ptw_i/ptw_pte_i
add wave -noupdate -group PTW /lsu_tb/dut/i_mmu/ptw_i/ptw_state_q
add wave -noupdate -group PTW /lsu_tb/dut/i_mmu/ptw_i/ptw_state_n
add wave -noupdate -group PTW /lsu_tb/dut/i_mmu/ptw_i/ptw_lvl_q
add wave -noupdate -group PTW /lsu_tb/dut/i_mmu/ptw_i/ptw_lvl_n
add wave -noupdate -group PTW /lsu_tb/dut/i_mmu/ptw_i/is_instr_ptw_q
add wave -noupdate -group PTW /lsu_tb/dut/i_mmu/ptw_i/is_instr_ptw_n
add wave -noupdate -group PTW /lsu_tb/dut/i_mmu/ptw_i/tlb_update_asid_q
add wave -noupdate -group PTW /lsu_tb/dut/i_mmu/ptw_i/tlb_update_asid_n
add wave -noupdate -group PTW /lsu_tb/dut/i_mmu/ptw_i/tlb_update_vpn_q
add wave -noupdate -group PTW /lsu_tb/dut/i_mmu/ptw_i/tlb_update_vpn_n
add wave -noupdate -group PTW /lsu_tb/dut/i_mmu/ptw_i/ptw_pptr_q
add wave -noupdate -group PTW /lsu_tb/dut/i_mmu/ptw_i/ptw_pptr_n
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {454 ns} 0}
quietly wave cursor active 1
configure wave -namecolwidth 176
configure wave -valuecolwidth 100
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
WaveRestoreZoom {0 ns} {1260 ns}
