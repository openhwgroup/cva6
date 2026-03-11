# CVA6 top level
if {![info exists CVA6]} {
    set CVA6 "/test/i_dut/i_cva6"
}

add wave -group CVA6 ${CVA6}/clk_i
add wave -group CVA6 ${CVA6}/rst_ni
add wave -group CVA6 ${CVA6}/boot_addr_i
add wave -group CVA6 ${CVA6}/hart_id_i
add wave -group CVA6 ${CVA6}/irq_i
add wave -group CVA6 ${CVA6}/ipi_i
add wave -group CVA6 ${CVA6}/time_irq_i
add wave -group CVA6 ${CVA6}/debug_req_i
add wave -group CVA6 ${CVA6}/clic_irq_valid_i
add wave -group CVA6 ${CVA6}/clic_irq_id_i
add wave -group CVA6 ${CVA6}/clic_irq_level_i
add wave -group CVA6 ${CVA6}/clic_irq_priv_i
add wave -group CVA6 ${CVA6}/clic_irq_v_i
add wave -group CVA6 ${CVA6}/clic_irq_vsid_i
add wave -group CVA6 ${CVA6}/clic_irq_shv_i
add wave -group CVA6 ${CVA6}/clic_irq_ready_o
add wave -group CVA6 ${CVA6}/clic_kill_req_i
add wave -group CVA6 ${CVA6}/clic_kill_ack_o
add wave -group CVA6 ${CVA6}/noc_req_o
add wave -group CVA6 ${CVA6}/noc_resp_i

# add wave -divider "Internal signals"

add wave -group CVA6 ${CVA6}/priv_lvl
add wave -group CVA6 ${CVA6}/v
add wave -group CVA6 ${CVA6}/rst_uarch_n
add wave -group CVA6 ${CVA6}/eret
add wave -group CVA6 ${CVA6}/resolved_branch
add wave -group CVA6 ${CVA6}/ex_commit
add wave -group CVA6 ${CVA6}/pc_commit
add wave -group CVA6 ${CVA6}/commit_ack

add wave -group CVA6 ${CVA6}/fetch_valid_if_id
add wave -group CVA6 ${CVA6}/fetch_ready_id_if
add wave -group CVA6 ${CVA6}/fetch_entry_if_id

add wave -group CVA6 ${CVA6}/issue_entry_valid_id_issue
add wave -group CVA6 ${CVA6}/issue_instr_issue_id
add wave -group CVA6 ${CVA6}/issue_entry_id_issue

add wave -group CVA6 ${CVA6}/commit_ack_commit_id
add wave -group CVA6 ${CVA6}/commit_instr_id_commit

# Frontend
set Frontend "${CVA6}/i_frontend"

add wave -group CVA6 -group Frontend ${Frontend}/clk_i
add wave -group CVA6 -group Frontend ${Frontend}/rst_ni
# add wave -group CVA6 -group Frontend ${Frontend}/boot_addr_i
add wave -group CVA6 -group Frontend ${Frontend}/flush_bp_i
add wave -group CVA6 -group Frontend ${Frontend}/flush_i
add wave -group CVA6 -group Frontend ${Frontend}/halt_i
add wave -group CVA6 -group Frontend ${Frontend}/halt_frontend_i
add wave -group CVA6 -group Frontend ${Frontend}/set_pc_commit_i
add wave -group CVA6 -group Frontend ${Frontend}/pc_commit_i
add wave -group CVA6 -group Frontend ${Frontend}/ex_valid_i
add wave -group CVA6 -group Frontend ${Frontend}/resolved_branch_i
add wave -group CVA6 -group Frontend ${Frontend}/eret_i
# add wave -group CVA6 -group Frontend ${Frontend}/epc_i
# add wave -group CVA6 -group Frontend ${Frontend}/trap_vector_base_i
add wave -group CVA6 -group Frontend ${Frontend}/set_debug_pc_i
add wave -group CVA6 -group Frontend ${Frontend}/debug_mode_i
add wave -group CVA6 -group Frontend ${Frontend}/icache_dreq_o
add wave -group CVA6 -group Frontend ${Frontend}/icache_dreq_i
add wave -group CVA6 -group Frontend ${Frontend}/fetch_entry_o
add wave -group CVA6 -group Frontend ${Frontend}/fetch_entry_valid_o
add wave -group CVA6 -group Frontend ${Frontend}/fetch_entry_ready_i

# Instruction cache
set icache "${CVA6}/gen_cache_wb/i_cache_subsystem/i_cva6_icache_axi_wrapper"

add wave -group CVA6 -group ICache ${icache}/clk_i
add wave -group CVA6 -group ICache ${icache}/rst_ni
# add wave -group CVA6 -group ICache ${icache}/priv_lvl_i
add wave -group CVA6 -group ICache ${icache}/flush_i
add wave -group CVA6 -group ICache ${icache}/en_i
add wave -group CVA6 -group ICache ${icache}/miss_o
add wave -group CVA6 -group ICache ${icache}/busy_o
add wave -group CVA6 -group ICache ${icache}/stall_i
add wave -group CVA6 -group ICache ${icache}/init_ni
add wave -group CVA6 -group ICache ${icache}/areq_i
add wave -group CVA6 -group ICache ${icache}/areq_o
add wave -group CVA6 -group ICache ${icache}/dreq_i
add wave -group CVA6 -group ICache ${icache}/dreq_o
add wave -group CVA6 -group ICache ${icache}/axi_req_o
add wave -group CVA6 -group ICache ${icache}/axi_resp_i
add wave -group CVA6 -group ICache ${icache}/i_cva6_icache/state_q
add wave -group CVA6 -group ICache ${icache}/i_cva6_icache/flush_cnt_q

# Data cache
set dcache "${CVA6}/gen_cache_wb/i_cache_subsystem/i_nbdcache"

add wave -group CVA6 -group DCache ${dcache}/clk_i
add wave -group CVA6 -group DCache ${dcache}/rst_ni
add wave -group CVA6 -group DCache ${dcache}/enable_i
add wave -group CVA6 -group DCache ${dcache}/flush_i
add wave -group CVA6 -group DCache ${dcache}/flush_ack_o
add wave -group CVA6 -group DCache ${dcache}/miss_o
add wave -group CVA6 -group DCache ${dcache}/busy_o
add wave -group CVA6 -group DCache ${dcache}/stall_i
add wave -group CVA6 -group DCache ${dcache}/init_ni
add wave -group CVA6 -group DCache ${dcache}/axi_bypass_o
add wave -group CVA6 -group DCache ${dcache}/axi_bypass_i
add wave -group CVA6 -group DCache ${dcache}/axi_data_o
add wave -group CVA6 -group DCache ${dcache}/axi_data_i
add wave -group CVA6 -group DCache ${dcache}/req_ports_i
add wave -group CVA6 -group DCache ${dcache}/req_ports_o
add wave -group CVA6 -group DCache ${dcache}/amo_req_i
add wave -group CVA6 -group DCache ${dcache}/amo_resp_o
