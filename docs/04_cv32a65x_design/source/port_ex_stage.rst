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
     - Connection
     - Type
     - Description

   * - ``clk_i``
     - in
     - SUBSYSTEM
     - Subsystem Clock
     - logic

   * - ``rst_ni``
     - in
     - SUBSYSTEM
     - Asynchronous reset active low
     - logic

   * - ``flush_i``
     - in
     - CONTROLLER
     - Fetch flush request
     - logic

   * - ``debug_mode_i``
     - in
     - CSR_REGFILE
     - TO_BE_COMPLETED
     - logic

   * - ``rs1_forwarding_i``
     - in
     - ID_STAGE
     - TO_BE_COMPLETED
     - logic[riscv::VLEN-1:0]

   * - ``rs2_forwarding_i``
     - in
     - ID_STAGE
     - TO_BE_COMPLETED
     - logic[riscv::VLEN-1:0]

   * - ``fu_data_i``
     - in
     - ID_STAGE
     - TO_BE_COMPLETED
     - fu_data_t

   * - ``pc_i``
     - in
     - ID_STAGE
     - PC of the current instruction
     - logic[riscv::VLEN-1:0]

   * - ``is_compressed_instr_i``
     - in
     - ID_STAGE
     - Report whether isntruction is compressed
     - logic

   * - ``flu_result_o``
     - out
     - ID_STAGE
     - TO_BE_COMPLETED
     - riscv::xlen_t

   * - ``flu_trans_id_o``
     - out
     - ID_STAGE
     - ID of the scoreboard entry at which a=to write back
     - logic[TRANS_ID_BITS-1:0]

   * - ``flu_exception_o``
     - out
     - ID_STAGE
     - TO_BE_COMPLETED
     - exception_t

   * - ``flu_ready_o``
     - out
     - ID_STAGE
     - FLU is ready
     - logic

   * - ``flu_valid_o``
     - out
     - ID_STAGE
     - FLU result is valid
     - logic

   * - ``alu_valid_i``
     - in
     - ID_STAGE
     - ALU result is valid
     - logic

   * - ``branch_valid_i``
     - in
     - ID_STAGE
     - Branch unit result is valid
     - logic

   * - ``branch_predict_i``
     - in
     - ID_STAGE
     - TO_BE_COMPLETED
     - branchpredict_sbe_t

   * - ``resolved_branch_o``
     - out
     - none
     - none
     - bp_resolve_t

   * - ``resolve_branch_o``
     - out
     - ID_STAGE
     - ID signaling that we resolved the branch
     - logic

   * - ``csr_valid_i``
     - in
     - ID_STAGE
     - TO_BE_COMPLETED
     - logic

   * - ``csr_addr_o``
     - out
     - CSR_REGISTERS
     - TO_BE_COMPLETED
     - logic[11:0]

   * - ``csr_commit_i``
     - in
     - COMMIT_STAGE
     - TO_BE_COMPLETED
     - logic

   * - ``mult_valid_i``
     - in
     - ID_STAGE
     - MULT result is valid
     - logic

   * - ``lsu_ready_o``
     - out
     - ID_STAGE
     - FU is ready
     - logic

   * - ``lsu_valid_i``
     - in
     - ID_STAGE
     - LSU result is valid
     - logic

   * - ``load_valid_o``
     - out
     - ID_STAGE
     - TO_BE_COMPLETED
     - logic

   * - ``load_result_o``
     - out
     - ID_STAGE
     - TO_BE_COMPLETED
     - riscv::xlen_t

   * - ``load_trans_id_o``
     - out
     - ID_STAGE
     - TO_BE_COMPLETED
     - logic[TRANS_ID_BITS-1:0]

   * - ``load_exception_o``
     - out
     - ID_STAGE
     - TO_BE_COMPLETED
     - exception_t

   * - ``store_valid_o``
     - out
     - ID_STAGE
     - TO_BE_COMPLETED
     - logic

   * - ``store_result_o``
     - out
     - ID_STAGE
     - TO_BE_COMPLETED
     - riscv::xlen_t

   * - ``store_trans_id_o``
     - out
     - ID_STAGE
     - TO_BE_COMPLETED
     - logic[TRANS_ID_BITS-1:0]

   * - ``store_exception_o``
     - out
     - ID_STAGE
     - TO_BE_COMPLETED
     - exception_t

   * - ``lsu_commit_i``
     - in
     - COMMIT_STAGE
     - TO_BE_COMPLETED
     - logic

   * - ``lsu_commit_ready_o``
     - out
     - COMMIT_STAGE
     - Commit queue is ready to accept another commit request
     - logic

   * - ``commit_tran_id_i``
     - in
     - COMMIT_STAGE
     - TO_BE_COMPLETED
     - logic[TRANS_ID_BITS-1:0]

   * - ``stall_st_pending_i``
     - in
     - ACC_DISPATCHER
     - TO_BE_COMPLETED
     - logic

   * - ``no_st_pending_o``
     - out
     - COMMIT_STAGE
     - TO_BE_COMPLETED
     - logic

   * - ``amo_valid_commit_i``
     - in
     - COMMIT_STAGE
     - TO_BE_COMPLETED
     - logic

   * - ``fpu_ready_o``
     - out
     - ID_STAGE
     - FU is ready
     - logic

   * - ``fpu_valid_i``
     - in
     - ID_STAGE
     - Output is ready
     - logic

   * - ``fpu_fmt_i``
     - in
     - ID_STAGE
     - report FP format
     - logic[1:0]

   * - ``fpu_rm_i``
     - in
     - ID_STAGE
     - FP rm
     - logic[2:0]

   * - ``fpu_frm_i``
     - in
     - ID_STAGE
     - FP frm
     - logic[2:0]

   * - ``fpu_prec_i``
     - in
     - CSR_REGFILE
     - FP precision control
     - logic[6:0]

   * - ``fpu_trans_id_o``
     - out
     - ID_STAGE
     - TO_BE_COMPLETED
     - logic[TRANS_ID_BITS-1:0]

   * - ``fpu_result_o``
     - out
     - ID_STAGE
     - TO_BE_COMPLETED
     - riscv::xlen_t

   * - ``fpu_valid_o``
     - out
     - ID_STAGE
     - TO_BE_COMPLETED
     - logic

   * - ``fpu_exception_o``
     - out
     - ID_STAGE
     - TO_BE_COMPLETED
     - exception_t

   * - ``x_valid_i``
     - in
     - ID_STAGE
     - TO_BE_COMPLETED
     - logic

   * - ``x_ready_o``
     - out
     - ID_STAGE
     - TO_BE_COMPLETED
     - logic

   * - ``x_off_instr_i``
     - in
     - ID_STAGE
     - TO_BE_COMPLETED
     - logic[31:0]

   * - ``x_trans_id_o``
     - out
     - ID_STAGE
     - TO_BE_COMPLETED
     - logic[TRANS_ID_BITS-1:0]

   * - ``x_exception_o``
     - out
     - ID_STAGE
     - TO_BE_COMPLETED
     - exception_t

   * - ``x_result_o``
     - out
     - ID_STAGE
     - TO_BE_COMPLETED
     - riscv::xlen_t

   * - ``x_valid_o``
     - out
     - ID_STAGE
     - TO_BE_COMPLETED
     - logic

   * - ``x_we_o``
     - out
     - ID_STAGE
     - TO_BE_COMPLETED
     - logic

   * - ``cvxif_req_o``
     - out
     - SUBSYSTEM
     - TO_BE_COMPLETED
     - cvxif_pkg::cvxif_req_t

   * - ``cvxif_resp_i``
     - in
     - SUBSYSTEM
     - TO_BE_COMPLETED
     - cvxif_pkg::cvxif_resp_t

   * - ``acc_valid_i``
     - in
     - ACC_DISPATCHER
     - TO_BE_COMPLETED
     - logic

   * - ``enable_translation_i``
     - in
     - CSR_REGFILE
     - TO_BE_COMPLETED
     - logic

   * - ``en_ld_st_translation_i``
     - in
     - CSR_REGFILE
     - TO_BE_COMPLETED
     - logic

   * - ``flush_tlb_i``
     - in
     - CONTROLLER
     - TO_BE_COMPLETED
     - logic

   * - ``priv_lvl_i``
     - in
     - CSR_REGFILE
     - TO_BE_COMPLETED
     - riscv::priv_lvl_t

   * - ``ld_st_priv_lvl_i``
     - in
     - CSR_REGFILE
     - TO_BE_COMPLETED
     - riscv::priv_lvl_t

   * - ``sum_i``
     - in
     - CSR_REGFILE
     - TO_BE_COMPLETED
     - logic

   * - ``mxr_i``
     - in
     - CSR_REGFILE
     - TO_BE_COMPLETED
     - logic

   * - ``satp_ppn_i``
     - in
     - CSR_REGFILE
     - TO_BE_COMPLETED
     - logic[riscv::PPNW-1:0]

   * - ``asid_i``
     - in
     - CSR_REGFILE
     - TO_BE_COMPLETED
     - logic[ASID_WIDTH-1:0]

   * - ``icache_areq_i``
     - in
     - CACHE
     - icache translation response
     - icache_arsp_t

   * - ``icache_areq_o``
     - out
     - CACHE
     - icache translation request
     - icache_areq_t

   * - ``dcache_req_ports_i``
     - in
     - CACHE
     - TO_BE_COMPLETED
     - dcache_req_o_t[2:0]

   * - ``dcache_req_ports_o``
     - out
     - CACHE
     - TO_BE_COMPLETED
     - dcache_req_i_t[2:0]

   * - ``dcache_wbuffer_empty_i``
     - in
     - CACHE
     - TO_BE_COMPLETED
     - logic

   * - ``dcache_wbuffer_not_ni_i``
     - in
     - CACHE
     - TO_BE_COMPLETED
     - logic

   * - ``amo_req_o``
     - out
     - CACHE
     - AMO request
     - amo_req_t

   * - ``amo_resp_i``
     - in
     - CACHE
     - AMO response from cache
     - amo_resp_t

   * - ``itlb_miss_o``
     - out
     - PERF_COUNTERS
     - To count the instruction TLB misses
     - logic

   * - ``dtlb_miss_o``
     - out
     - PERF_COUNTERS
     - To count the data TLB misses
     - logic

   * - ``pmpcfg_i``
     - in
     - CSR_REGFILE
     - Report the PMP configuration
     - riscv::pmpcfg_t[15:0]

   * - ``pmpaddr_i``
     - in
     - CSR_REGFILE
     - Report the PMP addresses
     - logic[15:0][riscv::PLEN-3:0]

   * - ``rvfi_lsu_ctrl_o``
     - out
     - SUBSYSTEM
     - Information dedicated to RVFI
     - lsu_ctrl_t

   * - ``rvfi_mem_paddr_o``
     - out
     - SUBSYSTEM
     - Information dedicated to RVFI
     - [riscv::PLEN-1:0]
