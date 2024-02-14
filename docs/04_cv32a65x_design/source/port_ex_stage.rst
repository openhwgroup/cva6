..
   Copyright 2024 Thales DIS France SAS
   Licensed under the Solderpad Hardware License, Version 2.1 (the "License");
   you may not use this file except in compliance with the License.
   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
   You may obtain a copy of the License at https://solderpad.org/licenses/

   Original Author: Jean-Roch COULON - Thales

.. _CVA6_ex_stage_ports:

.. list-table:: ex_stage module IO ports
   :header-rows: 1

   * - Signal
     - IO
     - Description
     - Connection
     - Type

   * - ``clk_i``
     - in
     - Subsystem Clock
     - SUBSYSTEM
     - logic

   * - ``rst_ni``
     - in
     - Asynchronous reset active low
     - SUBSYSTEM
     - logic

   * - ``flush_i``
     - in
     - Fetch flush request
     - CONTROLLER
     - logic

   * - ``debug_mode_i``
     - in
     - TO_BE_COMPLETED
     - CSR_REGFILE
     - logic

   * - ``rs1_forwarding_i``
     - in
     - TO_BE_COMPLETED
     - ID_STAGE
     - logic[riscv::VLEN-1:0]

   * - ``rs2_forwarding_i``
     - in
     - TO_BE_COMPLETED
     - ID_STAGE
     - logic[riscv::VLEN-1:0]

   * - ``fu_data_i``
     - in
     - TO_BE_COMPLETED
     - ID_STAGE
     - fu_data_t

   * - ``pc_i``
     - in
     - PC of the current instruction
     - ID_STAGE
     - logic[riscv::VLEN-1:0]

   * - ``is_compressed_instr_i``
     - in
     - Report whether isntruction is compressed
     - ID_STAGE
     - logic

   * - ``flu_result_o``
     - out
     - TO_BE_COMPLETED
     - ID_STAGE
     - riscv::xlen_t

   * - ``flu_trans_id_o``
     - out
     - ID of the scoreboard entry at which a=to write back
     - ID_STAGE
     - logic[TRANS_ID_BITS-1:0]

   * - ``flu_exception_o``
     - out
     - TO_BE_COMPLETED
     - ID_STAGE
     - exception_t

   * - ``flu_ready_o``
     - out
     - FLU is ready
     - ID_STAGE
     - logic

   * - ``flu_valid_o``
     - out
     - FLU result is valid
     - ID_STAGE
     - logic

   * - ``alu_valid_i``
     - in
     - ALU result is valid
     - ID_STAGE
     - logic

   * - ``branch_valid_i``
     - in
     - Branch unit result is valid
     - ID_STAGE
     - logic

   * - ``branch_predict_i``
     - in
     - TO_BE_COMPLETED
     - ID_STAGE
     - branchpredict_sbe_t

   * - ``resolved_branch_o``
     - out
     - none
     - none
     - bp_resolve_t

   * - ``resolve_branch_o``
     - out
     - ID signaling that we resolved the branch
     - ID_STAGE
     - logic

   * - ``csr_valid_i``
     - in
     - TO_BE_COMPLETED
     - ID_STAGE
     - logic

   * - ``csr_addr_o``
     - out
     - TO_BE_COMPLETED
     - CSR_REGISTERS
     - logic[11:0]

   * - ``csr_commit_i``
     - in
     - TO_BE_COMPLETED
     - COMMIT_STAGE
     - logic

   * - ``mult_valid_i``
     - in
     - MULT result is valid
     - ID_STAGE
     - logic

   * - ``lsu_ready_o``
     - out
     - FU is ready
     - ID_STAGE
     - logic

   * - ``lsu_valid_i``
     - in
     - LSU result is valid
     - ID_STAGE
     - logic

   * - ``load_valid_o``
     - out
     - TO_BE_COMPLETED
     - ID_STAGE
     - logic

   * - ``load_result_o``
     - out
     - TO_BE_COMPLETED
     - ID_STAGE
     - riscv::xlen_t

   * - ``load_trans_id_o``
     - out
     - TO_BE_COMPLETED
     - ID_STAGE
     - logic[TRANS_ID_BITS-1:0]

   * - ``load_exception_o``
     - out
     - TO_BE_COMPLETED
     - ID_STAGE
     - exception_t

   * - ``store_valid_o``
     - out
     - TO_BE_COMPLETED
     - ID_STAGE
     - logic

   * - ``store_result_o``
     - out
     - TO_BE_COMPLETED
     - ID_STAGE
     - riscv::xlen_t

   * - ``store_trans_id_o``
     - out
     - TO_BE_COMPLETED
     - ID_STAGE
     - logic[TRANS_ID_BITS-1:0]

   * - ``store_exception_o``
     - out
     - TO_BE_COMPLETED
     - ID_STAGE
     - exception_t

   * - ``lsu_commit_i``
     - in
     - TO_BE_COMPLETED
     - COMMIT_STAGE
     - logic

   * - ``lsu_commit_ready_o``
     - out
     - Commit queue is ready to accept another commit request
     - COMMIT_STAGE
     - logic

   * - ``commit_tran_id_i``
     - in
     - TO_BE_COMPLETED
     - COMMIT_STAGE
     - logic[TRANS_ID_BITS-1:0]

   * - ``stall_st_pending_i``
     - in
     - TO_BE_COMPLETED
     - ACC_DISPATCHER
     - logic

   * - ``no_st_pending_o``
     - out
     - TO_BE_COMPLETED
     - COMMIT_STAGE
     - logic

   * - ``amo_valid_commit_i``
     - in
     - TO_BE_COMPLETED
     - COMMIT_STAGE
     - logic

   * - ``fpu_ready_o``
     - out
     - FU is ready
     - ID_STAGE
     - logic

   * - ``fpu_valid_i``
     - in
     - Output is ready
     - ID_STAGE
     - logic

   * - ``fpu_fmt_i``
     - in
     - report FP format
     - ID_STAGE
     - logic[1:0]

   * - ``fpu_rm_i``
     - in
     - FP rm
     - ID_STAGE
     - logic[2:0]

   * - ``fpu_frm_i``
     - in
     - FP frm
     - ID_STAGE
     - logic[2:0]

   * - ``fpu_prec_i``
     - in
     - FP precision control
     - CSR_REGFILE
     - logic[6:0]

   * - ``fpu_trans_id_o``
     - out
     - TO_BE_COMPLETED
     - ID_STAGE
     - logic[TRANS_ID_BITS-1:0]

   * - ``fpu_result_o``
     - out
     - TO_BE_COMPLETED
     - ID_STAGE
     - riscv::xlen_t

   * - ``fpu_valid_o``
     - out
     - TO_BE_COMPLETED
     - ID_STAGE
     - logic

   * - ``fpu_exception_o``
     - out
     - TO_BE_COMPLETED
     - ID_STAGE
     - exception_t

   * - ``x_valid_i``
     - in
     - TO_BE_COMPLETED
     - ID_STAGE
     - logic

   * - ``x_ready_o``
     - out
     - TO_BE_COMPLETED
     - ID_STAGE
     - logic

   * - ``x_off_instr_i``
     - in
     - TO_BE_COMPLETED
     - ID_STAGE
     - logic[31:0]

   * - ``x_trans_id_o``
     - out
     - TO_BE_COMPLETED
     - ID_STAGE
     - logic[TRANS_ID_BITS-1:0]

   * - ``x_exception_o``
     - out
     - TO_BE_COMPLETED
     - ID_STAGE
     - exception_t

   * - ``x_result_o``
     - out
     - TO_BE_COMPLETED
     - ID_STAGE
     - riscv::xlen_t

   * - ``x_valid_o``
     - out
     - TO_BE_COMPLETED
     - ID_STAGE
     - logic

   * - ``x_we_o``
     - out
     - TO_BE_COMPLETED
     - ID_STAGE
     - logic

   * - ``cvxif_req_o``
     - out
     - TO_BE_COMPLETED
     - SUBSYSTEM
     - cvxif_pkg::cvxif_req_t

   * - ``cvxif_resp_i``
     - in
     - TO_BE_COMPLETED
     - SUBSYSTEM
     - cvxif_pkg::cvxif_resp_t

   * - ``acc_valid_i``
     - in
     - TO_BE_COMPLETED
     - ACC_DISPATCHER
     - logic

   * - ``enable_translation_i``
     - in
     - TO_BE_COMPLETED
     - CSR_REGFILE
     - logic

   * - ``en_ld_st_translation_i``
     - in
     - TO_BE_COMPLETED
     - CSR_REGFILE
     - logic

   * - ``flush_tlb_i``
     - in
     - TO_BE_COMPLETED
     - CONTROLLER
     - logic

   * - ``priv_lvl_i``
     - in
     - TO_BE_COMPLETED
     - CSR_REGFILE
     - riscv::priv_lvl_t

   * - ``ld_st_priv_lvl_i``
     - in
     - TO_BE_COMPLETED
     - CSR_REGFILE
     - riscv::priv_lvl_t

   * - ``sum_i``
     - in
     - TO_BE_COMPLETED
     - CSR_REGFILE
     - logic

   * - ``mxr_i``
     - in
     - TO_BE_COMPLETED
     - CSR_REGFILE
     - logic

   * - ``satp_ppn_i``
     - in
     - TO_BE_COMPLETED
     - CSR_REGFILE
     - logic[riscv::PPNW-1:0]

   * - ``asid_i``
     - in
     - TO_BE_COMPLETED
     - CSR_REGFILE
     - logic[ASID_WIDTH-1:0]

   * - ``icache_areq_i``
     - in
     - icache translation response
     - CACHE
     - icache_arsp_t

   * - ``icache_areq_o``
     - out
     - icache translation request
     - CACHE
     - icache_areq_t

   * - ``dcache_req_ports_i``
     - in
     - TO_BE_COMPLETED
     - CACHE
     - dcache_req_o_t[2:0]

   * - ``dcache_req_ports_o``
     - out
     - TO_BE_COMPLETED
     - CACHE
     - dcache_req_i_t[2:0]

   * - ``dcache_wbuffer_empty_i``
     - in
     - TO_BE_COMPLETED
     - CACHE
     - logic

   * - ``dcache_wbuffer_not_ni_i``
     - in
     - TO_BE_COMPLETED
     - CACHE
     - logic

   * - ``amo_req_o``
     - out
     - AMO request
     - CACHE
     - amo_req_t

   * - ``amo_resp_i``
     - in
     - AMO response from cache
     - CACHE
     - amo_resp_t

   * - ``itlb_miss_o``
     - out
     - To count the instruction TLB misses
     - PERF_COUNTERS
     - logic

   * - ``dtlb_miss_o``
     - out
     - To count the data TLB misses
     - PERF_COUNTERS
     - logic

   * - ``pmpcfg_i``
     - in
     - Report the PMP configuration
     - CSR_REGFILE
     - riscv::pmpcfg_t[15:0]

   * - ``pmpaddr_i``
     - in
     - Report the PMP addresses
     - CSR_REGFILE
     - logic[15:0][riscv::PLEN-3:0]

   * - ``rvfi_lsu_ctrl_o``
     - out
     - Information dedicated to RVFI
     - SUBSYSTEM
     - lsu_ctrl_t

   * - ``rvfi_mem_paddr_o``
     - out
     - Information dedicated to RVFI
     - SUBSYSTEM
     - [riscv::PLEN-1:0]
