..
   Copyright 2024 Thales DIS France SAS
   Licensed under the Solderpad Hardware License, Version 2.1 (the "License");
   you may not use this file except in compliance with the License.
   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
   You may obtain a copy of the License at https://solderpad.org/licenses/

   Original Author: Jean-Roch COULON - Thales

.. _CVA6_commit_stage_ports:

.. list-table:: **commit_stage module** IO ports
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

   * - ``halt_i``
     - in
     - Request to halt the core
     - CONTROLLER
     - logic

   * - ``flush_dcache_i``
     - in
     - request to flush dcache, also flush the pipeline
     - CACHE
     - logic

   * - ``exception_o``
     - out
     - TO_BE_COMPLETED
     - EX_STAGE
     - exception_t

   * - ``commit_instr_i``
     - in
     - The instruction we want to commit
     - ISSUE_STAGE
     - scoreboard_entry_t[CVA6Cfg.NrCommitPorts-1:0]

   * - ``commit_ack_o``
     - out
     - Acknowledge that we are indeed committing
     - ISSUE_STAGE
     - logic[CVA6Cfg.NrCommitPorts-1:0]

   * - ``commit_macro_ack_o``
     - out
     - Acknowledge that we are indeed committing
     - CSR_REGFILE
     - logic[CVA6Cfg.NrCommitPorts-1:0]

   * - ``waddr_o``
     - out
     - Register file write address
     - ISSUE_STAGE
     - logic[CVA6Cfg.NrCommitPorts-1:0][4:0]

   * - ``wdata_o``
     - out
     - Register file write data
     - ISSUE_STAGE
     - logic[CVA6Cfg.NrCommitPorts-1:0][CVA6Cfg.XLEN-1:0]

   * - ``we_gpr_o``
     - out
     - Register file write enable
     - ISSUE_STAGE
     - logic[CVA6Cfg.NrCommitPorts-1:0]

   * - ``we_fpr_o``
     - out
     - Floating point register enable
     - ISSUE_STAGE
     - logic[CVA6Cfg.NrCommitPorts-1:0]

   * - ``pc_o``
     - out
     - TO_BE_COMPLETED
     - FRONTEND_CSR_REGFILE
     - logic[CVA6Cfg.VLEN-1:0]

   * - ``csr_op_o``
     - out
     - Decoded CSR operation
     - CSR_REGFILE
     - fu_op

   * - ``csr_wdata_o``
     - out
     - Data to write to CSR
     - CSR_REGFILE
     - logic[CVA6Cfg.XLEN-1:0]

   * - ``csr_rdata_i``
     - in
     - Data to read from CSR
     - CSR_REGFILE
     - logic[CVA6Cfg.XLEN-1:0]

   * - ``csr_exception_i``
     - in
     - Exception or interrupt occurred in CSR stage (the same as commit)
     - CSR_REGFILE
     - exception_t

   * - ``commit_lsu_o``
     - out
     - Commit the pending store
     - EX_STAGE
     - logic

   * - ``commit_lsu_ready_i``
     - in
     - Commit buffer of LSU is ready
     - EX_STAGE
     - logic

   * - ``commit_tran_id_o``
     - out
     - Transaction id of first commit port
     - ID_STAGE
     - logic[CVA6Cfg.TRANS_ID_BITS-1:0]

   * - ``no_st_pending_i``
     - in
     - no store is pending
     - EX_STAGE
     - logic

   * - ``commit_csr_o``
     - out
     - Commit the pending CSR instruction
     - EX_STAGE
     - logic

   * - ``flush_commit_o``
     - out
     - Request a pipeline flush
     - CONTROLLER
     - logic

Due to cv32a65x configuration, some ports are tied to a static value. These ports do not appear in the above table, they are listed below

| As RVF = 0,
|   ``dirty_fp_state_o`` output is tied to 0
|   ``csr_write_fflags_o`` output is tied to 0
| As DebugEn = False,
|   ``single_step_i`` input is tied to 0
| As RVA = False,
|   ``amo_resp_i`` input is tied to 0
|   ``amo_valid_commit_o`` output is tied to 0
| As FenceEn = 0,
|   ``fence_i_o`` output is tied to 0
|   ``fence_o`` output is tied to 0
| As RVS = False,
|   ``sfence_vma_o`` output is tied to 0
| As RVH = False,
|   ``hfence_vvma_o`` output is tied to 0
|   ``hfence_gvma_o`` output is tied to 0

