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
     - Fetch flush request
     - CONTROLLER
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
     - The branch engine uses the write back from the ALU
     - several_modules
     - bp_resolve_t

   * - ``resolve_branch_o``
     - out
     - ID signaling that we resolved the branch
     - ID_STAGE
     - logic

   * - ``csr_valid_i``
     - in
     - CSR result is valid
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
     - Load result is valid
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
     - Store result is valid
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
     - Commit queue ready to accept another commit request
     - COMMIT_STAGE
     - logic

   * - ``commit_tran_id_i``
     - in
     - TO_BE_COMPLETED
     - COMMIT_STAGE
     - logic[TRANS_ID_BITS-1:0]

   * - ``no_st_pending_o``
     - out
     - TO_BE_COMPLETED
     - COMMIT_STAGE
     - logic

   * - ``x_valid_i``
     - in
     - CVXIF result is valid
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

   * - ``sum_i``
     - in
     - Supervisor user memory
     - CSR_REGFILE
     - logic

   * - ``mxr_i``
     - in
     - Make executable readable
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

Due to cv32a65x configuration, some ports are tied to a static value. These ports do not appear in the above table, they are listed below

| As DebugEn = 0,
|   ``debug_mode_i`` input is tied to 0
| As EnableAccelerator = 0,
|   ``stall_st_pending_i`` input is tied to 0
|   ``acc_valid_i`` input is tied to 0
| As RVA = 0,
|   ``amo_valid_commit_i`` input is tied to 0
|   ``amo_req_o`` output is tied to 0
|   ``amo_resp_i`` input is tied to 0
| As RVF = 0,
|   ``fpu_ready_o`` output is tied to 0
|   ``fpu_valid_i`` input is tied to 0
|   ``fpu_fmt_i`` input is tied to 0
|   ``fpu_rm_i`` input is tied to 0
|   ``fpu_frm_i`` input is tied to 0
|   ``fpu_prec_i`` input is tied to 0
|   ``fpu_trans_id_o`` output is tied to 0
|   ``fpu_result_o`` output is tied to 0
|   ``fpu_valid_o`` output is tied to 0
|   ``fpu_exception_o`` output is tied to 0
| As MMUPresent = 0,
|   ``flush_tlb_i`` input is tied to 0
| As PRIV = MachineOnly,
|   ``priv_lvl_i`` input is tied to MachineMode
|   ``ld_st_priv_lvl_i`` input is tied to MAchineMode
| As PerfCounterEn = 0,
|   ``itlb_miss_o`` output is tied to 0
|   ``dtlb_miss_o`` output is tied to 0
| As IsRVFI = 0,
|   ``rvfi_lsu_ctrl_o`` output is tied to 0
|   ``rvfi_mem_paddr_o`` output is tied to 0
none
