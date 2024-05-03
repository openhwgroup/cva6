..
   Copyright 2024 Thales DIS France SAS
   Licensed under the Solderpad Hardware License, Version 2.1 (the "License");
   you may not use this file except in compliance with the License.
   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
   You may obtain a copy of the License at https://solderpad.org/licenses/

   Original Author: Jean-Roch COULON - Thales

.. _CVA6_load_store_unit_ports:

.. list-table:: **load_store_unit module** IO ports
   :header-rows: 1

   * - Signal
     - IO
     - Description
     - connexion
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
     - TO_BE_COMPLETED
     - TO_BE_COMPLETED
     - logic

   * - ``stall_st_pending_i``
     - in
     - TO_BE_COMPLETED
     - TO_BE_COMPLETED
     - logic

   * - ``no_st_pending_o``
     - out
     - TO_BE_COMPLETED
     - TO_BE_COMPLETED
     - logic

   * - ``fu_data_i``
     - in
     - FU data needed to execute instruction
     - ISSUE_STAGE
     - fu_data_t

   * - ``lsu_ready_o``
     - out
     - Load Store Unit is ready
     - ISSUE_STAGE
     - logic

   * - ``lsu_valid_i``
     - in
     - Load Store Unit instruction is valid
     - ISSUE_STAGE
     - logic

   * - ``load_trans_id_o``
     - out
     - Load transaction ID
     - ISSUE_STAGE
     - logic[CVA6Cfg.TRANS_ID_BITS-1:0]

   * - ``load_result_o``
     - out
     - Load result
     - ISSUE_STAGE
     - logic[CVA6Cfg.XLEN-1:0]

   * - ``load_valid_o``
     - out
     - Load result is valid
     - ISSUE_STAGE
     - logic

   * - ``load_exception_o``
     - out
     - Load exception
     - ISSUE_STAGE
     - exception_t

   * - ``store_trans_id_o``
     - out
     - Store transaction ID
     - ISSUE_STAGE
     - logic[CVA6Cfg.TRANS_ID_BITS-1:0]

   * - ``store_result_o``
     - out
     - Store result
     - ISSUE_STAGE
     - logic[CVA6Cfg.XLEN-1:0]

   * - ``store_valid_o``
     - out
     - Store result is valid
     - ISSUE_STAGE
     - logic

   * - ``store_exception_o``
     - out
     - Store exception
     - ISSUE_STAGE
     - exception_t

   * - ``commit_i``
     - in
     - Commit the first pending store
     - TO_BE_COMPLETED
     - logic

   * - ``commit_ready_o``
     - out
     - Commit queue is ready to accept another commit request
     - TO_BE_COMPLETED
     - logic

   * - ``commit_tran_id_i``
     - in
     - Commit transaction ID
     - TO_BE_COMPLETED
     - logic[CVA6Cfg.TRANS_ID_BITS-1:0]

   * - ``icache_areq_i``
     - in
     - Instruction cache input request
     - CACHES
     - icache_arsp_t

   * - ``icache_areq_o``
     - out
     - Instruction cache output request
     - CACHES
     - icache_areq_t

   * - ``dcache_req_ports_i``
     - in
     - Data cache request output
     - CACHES
     - dcache_req_o_t[2:0]

   * - ``dcache_req_ports_o``
     - out
     - Data cache request input
     - CACHES
     - dcache_req_i_t[2:0]

   * - ``dcache_wbuffer_empty_i``
     - in
     - TO_BE_COMPLETED
     - TO_BE_COMPLETED
     - logic

   * - ``dcache_wbuffer_not_ni_i``
     - in
     - TO_BE_COMPLETED
     - TO_BE_COMPLETED
     - logic

   * - ``pmpcfg_i``
     - in
     - PMP configuration
     - CSR_REGFILE
     - riscv::pmpcfg_t[15:0]

   * - ``pmpaddr_i``
     - in
     - PMP address
     - CSR_REGFILE
     - logic[15:0][CVA6Cfg.PLEN-3:0]

Due to cv32a65x configuration, some ports are tied to a static value. These ports do not appear in the above table, they are listed below

| As RVA = False,
|   ``amo_valid_commit_i`` input is tied to 0
|   ``amo_req_o`` output is tied to 0
|   ``amo_resp_i`` input is tied to 0
| As RVH = False,
|   ``tinst_i`` input is tied to 0
|   ``enable_g_translation_i`` input is tied to 0
|   ``en_ld_st_g_translation_i`` input is tied to 0
|   ``v_i`` input is tied to 0
|   ``ld_st_v_i`` input is tied to 0
|   ``csr_hs_ld_st_inst_o`` output is tied to 0
|   ``vs_sum_i`` input is tied to 0
|   ``vmxr_i`` input is tied to 0
|   ``vsatp_ppn_i`` input is tied to 0
|   ``vs_asid_i`` input is tied to 0
|   ``hgatp_ppn_i`` input is tied to 0
|   ``vmid_i`` input is tied to 0
|   ``vmid_to_be_flushed_i`` input is tied to 0
|   ``gpaddr_to_be_flushed_i`` input is tied to 0
|   ``flush_tlb_vvma_i`` input is tied to 0
|   ``flush_tlb_gvma_i`` input is tied to 0
| As RVS = False,
|   ``enable_translation_i`` input is tied to 0
|   ``en_ld_st_translation_i`` input is tied to 0
|   ``sum_i`` input is tied to 0
|   ``mxr_i`` input is tied to 0
|   ``satp_ppn_i`` input is tied to 0
|   ``asid_i`` input is tied to 0
|   ``asid_to_be_flushed_i`` input is tied to 0
|   ``vaddr_to_be_flushed_i`` input is tied to 0
| As PRIV = MachineOnly,
|   ``priv_lvl_i`` input is tied to MachineMode
|   ``ld_st_priv_lvl_i`` input is tied to MAchineMode
| As MMUPresent = 0,
|   ``flush_tlb_i`` input is tied to 0
| As PerfCounterEn = 0,
|   ``itlb_miss_o`` output is tied to 0
|   ``dtlb_miss_o`` output is tied to 0
| As IsRVFI = 0,
|   ``rvfi_lsu_ctrl_o`` output is tied to 0
|   ``rvfi_mem_paddr_o`` output is tied to 0

