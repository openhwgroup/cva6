..
   Copyright 2024 Thales DIS France SAS
   Licensed under the Solderpad Hardware License, Version 2.1 (the "License");
   you may not use this file except in compliance with the License.
   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
   You may obtain a copy of the License at https://solderpad.org/licenses/

   Original Author: Jean-Roch COULON - Thales

.. _CVA6_commit_stage_ports:

.. list-table:: commit_stage module IO ports
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

   * - ``dirty_fp_state_o``
     - out
     - Mark the F state as dirty
     - CSR_REGFILE
     - logic

   * - ``single_step_i``
     - in
     - TO_BE_COMPLETED
     - CSR_REGFILE
     - logic

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

   * - ``waddr_o``
     - out
     - Register file write address
     - ID_STAGE
     - logic[CVA6Cfg.NrCommitPorts-1:0][4:0]

   * - ``wdata_o``
     - out
     - Register file write data
     - ID_STAGE
     - logic[CVA6Cfg.NrCommitPorts-1:0][riscv::XLEN-1:0]

   * - ``we_gpr_o``
     - out
     - Register file write enable
     - ID_STAGE
     - logic[CVA6Cfg.NrCommitPorts-1:0]

   * - ``we_fpr_o``
     - out
     - Floating point register enable
     - ID_STAGE
     - logic[CVA6Cfg.NrCommitPorts-1:0]

   * - ``pc_o``
     - out
     - TO_BE_COMPLETED
     - FRONTEND_CSR
     - logic[riscv::VLEN-1:0]

   * - ``csr_op_o``
     - out
     - Decoded CSR operation
     - CSR_REGFILE
     - fu_op

   * - ``csr_wdata_o``
     - out
     - Data to write to CSR
     - CSR_REGFILE
     - riscv::xlen_t

   * - ``csr_rdata_i``
     - in
     - Data to read from CSR
     - CSR_REGFILE
     - riscv::xlen_t

   * - ``csr_exception_i``
     - in
     - Exception or interrupt occurred in CSR stage (the same as commit)
     - CSR_REGFILE
     - exception_t

   * - ``csr_write_fflags_o``
     - out
     - Write the fflags CSR
     - CSR_REGFILE
     - logic

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
     - logic[TRANS_ID_BITS-1:0]

   * - ``amo_valid_commit_o``
     - out
     - Valid AMO in commit stage
     - EX_STAGE
     - logic

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

   * - ``fence_i_o``
     - out
     - Flush I$ and pipeline
     - CONTROLLER
     - logic

   * - ``fence_o``
     - out
     - Flush D$ and pipeline
     - CONTROLLER
     - logic

   * - ``flush_commit_o``
     - out
     - Request a pipeline flush
     - CONTROLLER
     - logic

   * - ``sfence_vma_o``
     - out
     - Flush TLBs and pipeline
     - CONTROLLER
     - logic

| As A extension is disabled,
|   ``amo_resp_i`` input is tied to zero
