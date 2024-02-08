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
     - logic
     - Subsystem Clock

   * - ``rst_ni``
     - in
     - SUBSYSTEM
     - logic
     - Asynchronous reset active low

   * - ``flush_i``
     - in
     - CONTROLLER
     - logic
     - Fetch flush request

   * - ``debug_mode_i``
     - in
     - CSR_REGFILE
     - logic
     - TO_BE_COMPLETED

   * - ``rs1_forwarding_i``
     - in
     - ID_STAGE
     - logic[riscv::VLEN-1:0]
     - TO_BE_COMPLETED

   * - ``rs2_forwarding_i``
     - in
     - ID_STAGE
     - logic[riscv::VLEN-1:0]
     - TO_BE_COMPLETED

   * - ``fu_data_i``
     - in
     - ID_STAGE
     - fu_data_t
     - TO_BE_COMPLETED

   * - ``pc_i``
     - in
     - ID_STAGE
     - logic[riscv::VLEN-1:0]
     - PC of the current instruction

   * - ``is_compressed_instr_i``
     - in
     - ID_STAGE
     - logic
     - Report whether isntruction is compressed

   * - ``flu_result_o``
     - out
     - ID_STAGE
     - riscv::xlen_t
     - TO_BE_COMPLETED

   * - ``flu_trans_id_o``
     - out
     - ID_STAGE
     - logic[TRANS_ID_BITS-1:0]
     - ID of the scoreboard entry at which a=to write back

   * - ``flu_exception_o``
     - out
     - ID_STAGE
     - exception_t
     - TO_BE_COMPLETED

   * - ``flu_ready_o``
     - out
     - ID_STAGE
     - logic
     - FLU is ready

   * - ``flu_valid_o``
     - out
     - ID_STAGE
     - logic
     - FLU result is valid

   * - ``alu_valid_i``
     - in
     - ID_STAGE
     - logic
     - ALU result is valid

   * - ``branch_valid_i``
     - in
     - ID_STAGE
     - logic
     - Branch unit result is valid

   * - ``branch_predict_i``
     - in
     - ID_STAGE
     - branchpredict_sbe_t
     - TO_BE_COMPLETED

   * - ``resolved_branch_o``
     - out
     - none
     - bp_resolve_t
     - none

   * - ``resolve_branch_o``
     - out
     - ID_STAGE
     - logic
     - ID signaling that we resolved the branch

   * - ``csr_valid_i``
     - in
     - ID_STAGE
     - logic
     - TO_BE_COMPLETED

   * - ``csr_addr_o``
     - out
     - CSR_REGISTERS
     - logic[11:0]
     - TO_BE_COMPLETED

   * - ``csr_commit_i``
     - in
     - COMMIT_STAGE
     - logic
     - TO_BE_COMPLETED

   * - ``mult_valid_i``
     - in
     - ID_STAGE
     - logic
     - MULT result is valid

   * - ``lsu_ready_o``
     - out
     - ID_STAGE
     - logic
     - FU is ready

   * - ``lsu_valid_i``
     - in
     - ID_STAGE
     - logic
     - LSU result is valid

   * - ``load_valid_o``
     - out
     - ID_STAGE
     - logic
     - TO_BE_COMPLETED

   * - ``load_result_o``
     - out
     - ID_STAGE
     - riscv::xlen_t
     - TO_BE_COMPLETED

   * - ``load_trans_id_o``
     - out
     - ID_STAGE
     - logic[TRANS_ID_BITS-1:0]
     - TO_BE_COMPLETED

   * - ``load_exception_o``
     - out
     - ID_STAGE
     - exception_t
     - TO_BE_COMPLETED

   * - ``store_valid_o``
     - out
     - ID_STAGE
     - logic
     - TO_BE_COMPLETED

   * - ``store_result_o``
     - out
     - ID_STAGE
     - riscv::xlen_t
     - TO_BE_COMPLETED

   * - ``store_trans_id_o``
     - out
     - ID_STAGE
     - logic[TRANS_ID_BITS-1:0]
     - TO_BE_COMPLETED

   * - ``store_exception_o``
     - out
     - ID_STAGE
     - exception_t
     - TO_BE_COMPLETED

   * - ``lsu_commit_i``
     - in
     - COMMIT_STAGE
     - logic
     - TO_BE_COMPLETED

   * - ``lsu_commit_ready_o``
     - out
     - COMMIT_STAGE
     - logic
     - Commit queue is ready to accept another commit request

   * - ``commit_tran_id_i``
     - in
     - COMMIT_STAGE
     - logic[TRANS_ID_BITS-1:0]
     - TO_BE_COMPLETED

   * - ``stall_st_pending_i``
     - in
     - ACC_DISPATCHER
     - logic
     - TO_BE_COMPLETED

   * - ``no_st_pending_o``
     - out
     - COMMIT_STAGE
     - logic
     - TO_BE_COMPLETED

   * - ``amo_valid_commit_i``
     - in
     - COMMIT_STAGE
     - logic
     - TO_BE_COMPLETED

   * - ``fpu_ready_o``
     - out
     - ID_STAGE
     - logic
     - FU is ready

   * - ``fpu_valid_i``
     - in
     - ID_STAGE
     - logic
     - Output is ready

   * - ``fpu_fmt_i``
     - in
     - ID_STAGE
     - logic[1:0]
     - report FP format

   * - ``fpu_rm_i``
     - in
     - ID_STAGE
     - logic[2:0]
     - FP rm

   * - ``fpu_frm_i``
     - in
     - ID_STAGE
     - logic[2:0]
     - FP frm

   * - ``fpu_prec_i``
     - in
     - CSR_REGFILE
     - logic[6:0]
     - FP precision control

   * - ``fpu_trans_id_o``
     - out
     - ID_STAGE
     - logic[TRANS_ID_BITS-1:0]
     - TO_BE_COMPLETED

   * - ``fpu_result_o``
     - out
     - ID_STAGE
     - riscv::xlen_t
     - TO_BE_COMPLETED

   * - ``fpu_valid_o``
     - out
     - ID_STAGE
     - logic
     - TO_BE_COMPLETED

   * - ``fpu_exception_o``
     - out
     - ID_STAGE
     - exception_t
     - TO_BE_COMPLETED

   * - ``x_valid_i``
     - in
     - ID_STAGE
     - logic
     - TO_BE_COMPLETED

   * - ``x_ready_o``
     - out
     - ID_STAGE
     - logic
     - TO_BE_COMPLETED

   * - ``x_off_instr_i``
     - in
     - ID_STAGE
     - logic[31:0]
     - TO_BE_COMPLETED

   * - ``x_trans_id_o``
     - out
     - ID_STAGE
     - logic[TRANS_ID_BITS-1:0]
     - TO_BE_COMPLETED

   * - ``x_exception_o``
     - out
     - ID_STAGE
     - exception_t
     - TO_BE_COMPLETED

   * - ``x_result_o``
     - out
     - ID_STAGE
     - riscv::xlen_t
     - TO_BE_COMPLETED

   * - ``x_valid_o``
     - out
     - ID_STAGE
     - logic
     - TO_BE_COMPLETED

   * - ``x_we_o``
     - out
     - ID_STAGE
     - logic
     - TO_BE_COMPLETED

   * - ``cvxif_req_o``
     - out
     - SUBSYSTEM
     - cvxif_pkg::cvxif_req_t
     - TO_BE_COMPLETED

   * - ``cvxif_resp_i``
     - in
     - SUBSYSTEM
     - cvxif_pkg::cvxif_resp_t
     - TO_BE_COMPLETED

   * - ``acc_valid_i``
     - in
     - ACC_DISPATCHER
     - logic
     - TO_BE_COMPLETED

   * - ``enable_translation_i``
     - in
     - CSR_REGFILE
     - logic
     - TO_BE_COMPLETED

   * - ``en_ld_st_translation_i``
     - in
     - CSR_REGFILE
     - logic
     - TO_BE_COMPLETED

   * - ``flush_tlb_i``
     - in
     - CONTROLLER
     - logic
     - TO_BE_COMPLETED

   * - ``priv_lvl_i``
     - in
     - CSR_REGFILE
     - riscv::priv_lvl_t
     - TO_BE_COMPLETED

   * - ``ld_st_priv_lvl_i``
     - in
     - CSR_REGFILE
     - riscv::priv_lvl_t
     - TO_BE_COMPLETED

   * - ``sum_i``
     - in
     - CSR_REGFILE
     - logic
     - TO_BE_COMPLETED

   * - ``mxr_i``
     - in
     - CSR_REGFILE
     - logic
     - TO_BE_COMPLETED

   * - ``satp_ppn_i``
     - in
     - CSR_REGFILE
     - logic[riscv::PPNW-1:0]
     - TO_BE_COMPLETED

   * - ``asid_i``
     - in
     - CSR_REGFILE
     - logic[ASID_WIDTH-1:0]
     - TO_BE_COMPLETED

   * - ``icache_areq_i``
     - in
     - CACHE
     - icache_arsp_t
     - icache translation response

   * - ``icache_areq_o``
     - out
     - CACHE
     - icache_areq_t
     - icache translation request

   * - ``dcache_req_ports_i``
     - in
     - CACHE
     - dcache_req_o_t[2:0]
     - TO_BE_COMPLETED

   * - ``dcache_req_ports_o``
     - out
     - CACHE
     - dcache_req_i_t[2:0]
     - TO_BE_COMPLETED

   * - ``dcache_wbuffer_empty_i``
     - in
     - CACHE
     - logic
     - TO_BE_COMPLETED

   * - ``dcache_wbuffer_not_ni_i``
     - in
     - CACHE
     - logic
     - TO_BE_COMPLETED

   * - ``amo_req_o``
     - out
     - CACHE
     - amo_req_t
     - AMO request

   * - ``amo_resp_i``
     - in
     - CACHE
     - amo_resp_t
     - AMO response from cache

   * - ``itlb_miss_o``
     - out
     - PERF_COUNTERS
     - logic
     - To count the instruction TLB misses

   * - ``dtlb_miss_o``
     - out
     - PERF_COUNTERS
     - logic
     - To count the data TLB misses

   * - ``pmpcfg_i``
     - in
     - CSR_REGFILE
     - riscv::pmpcfg_t[15:0]
     - Report the PMP configuration

   * - ``pmpaddr_i``
     - in
     - CSR_REGFILE
     - logic[15:0][riscv::PLEN-3:0]
     - Report the PMP addresses

   * - ``rvfi_lsu_ctrl_o``
     - out
     - SUBSYSTEM
     - lsu_ctrl_t
     - Information dedicated to RVFI

   * - ``rvfi_mem_paddr_o``
     - out
     - SUBSYSTEM
     - [riscv::PLEN-1:0]
     - Information dedicated to RVFI
