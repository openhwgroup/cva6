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

   * - ``halt_i``
     - in
     - CONTROLLER
     - Request to halt the core
     - logic

   * - ``flush_dcache_i``
     - in
     - CACHE
     - request to flush dcache, also flush the pipeline
     - logic

   * - ``exception_o``
     - out
     - EX_STAGE
     - TO_BE_COMPLETED
     - exception_t

   * - ``dirty_fp_state_o``
     - out
     - CSR_REGFILE
     - Mark the F state as dirty
     - logic

   * - ``single_step_i``
     - in
     - CSR_REGFILE
     - TO_BE_COMPLETED
     - logic

   * - ``commit_instr_i``
     - in
     - ISSUE_STAGE
     - The instruction we want to commit
     - scoreboard_entry_t[CVA6Cfg.NrCommitPorts-1:0]

   * - ``commit_ack_o``
     - out
     - ISSUE_STAGE
     - Acknowledge that we are indeed committing
     - logic[CVA6Cfg.NrCommitPorts-1:0]

   * - ``waddr_o``
     - out
     - ID_STAGE
     - Register file write address
     - logic[CVA6Cfg.NrCommitPorts-1:0][4:0]

   * - ``wdata_o``
     - out
     - ID_STAGE
     - Register file write data
     - logic[CVA6Cfg.NrCommitPorts-1:0][riscv::XLEN-1:0]

   * - ``we_gpr_o``
     - out
     - ID_STAGE
     - Register file write enable
     - logic[CVA6Cfg.NrCommitPorts-1:0]

   * - ``we_fpr_o``
     - out
     - ID_STAGE
     - Floating point register enable
     - logic[CVA6Cfg.NrCommitPorts-1:0]

   * - ``amo_resp_i``
     - in
     - CACHE
     - Result of AMO operation
     - amo_resp_t

   * - ``pc_o``
     - out
     - FRONTEND_CSR
     - TO_BE_COMPLETED
     - logic[riscv::VLEN-1:0]

   * - ``csr_op_o``
     - out
     - CSR_REGFILE
     - Decoded CSR operation
     - fu_op

   * - ``csr_wdata_o``
     - out
     - CSR_REGFILE
     - Data to write to CSR
     - riscv::xlen_t

   * - ``csr_rdata_i``
     - in
     - CSR_REGFILE
     - Data to read from CSR
     - riscv::xlen_t

   * - ``csr_exception_i``
     - in
     - CSR_REGFILE
     - Exception or interrupt occurred in CSR stage (the same as commit)
     - exception_t

   * - ``csr_write_fflags_o``
     - out
     - CSR_REGFILE
     - Write the fflags CSR
     - logic

   * - ``commit_lsu_o``
     - out
     - EX_STAGE
     - Commit the pending store
     - logic

   * - ``commit_lsu_ready_i``
     - in
     - EX_STAGE
     - Commit buffer of LSU is ready
     - logic

   * - ``commit_tran_id_o``
     - out
     - ID_STAGE
     - Transaction id of first commit port
     - logic[TRANS_ID_BITS-1:0]

   * - ``amo_valid_commit_o``
     - out
     - EX_STAGE
     - Valid AMO in commit stage
     - logic

   * - ``no_st_pending_i``
     - in
     - EX_STAGE
     - no store is pending
     - logic

   * - ``commit_csr_o``
     - out
     - EX_STAGE
     - Commit the pending CSR instruction
     - logic

   * - ``fence_i_o``
     - out
     - CONTROLLER
     - Flush I$ and pipeline
     - logic

   * - ``fence_o``
     - out
     - CONTROLLER
     - Flush D$ and pipeline
     - logic

   * - ``flush_commit_o``
     - out
     - CONTROLLER
     - Request a pipeline flush
     - logic

   * - ``sfence_vma_o``
     - out
     - CONTROLLER
     - Flush TLBs and pipeline
     - logic
