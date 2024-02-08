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
     - logic
     - Subsystem Clock

   * - ``rst_ni``
     - in
     - SUBSYSTEM
     - logic
     - Asynchronous reset active low

   * - ``halt_i``
     - in
     - CONTROLLER
     - logic
     - Request to halt the core

   * - ``flush_dcache_i``
     - in
     - CACHE
     - logic
     - request to flush dcache, also flush the pipeline

   * - ``exception_o``
     - out
     - EX_STAGE
     - exception_t
     - TO_BE_COMPLETED

   * - ``dirty_fp_state_o``
     - out
     - CSR_REGFILE
     - logic
     - Mark the F state as dirty

   * - ``single_step_i``
     - in
     - CSR_REGFILE
     - logic
     - TO_BE_COMPLETED

   * - ``commit_instr_i``
     - in
     - ISSUE_STAGE
     - scoreboard_entry_t[CVA6Cfg.NrCommitPorts-1:0]
     - The instruction we want to commit

   * - ``commit_ack_o``
     - out
     - ISSUE_STAGE
     - logic[CVA6Cfg.NrCommitPorts-1:0]
     - Acknowledge that we are indeed committing

   * - ``waddr_o``
     - out
     - ID_STAGE
     - logic[CVA6Cfg.NrCommitPorts-1:0][4:0]
     - Register file write address

   * - ``wdata_o``
     - out
     - ID_STAGE
     - logic[CVA6Cfg.NrCommitPorts-1:0][riscv::XLEN-1:0]
     - Register file write data

   * - ``we_gpr_o``
     - out
     - ID_STAGE
     - logic[CVA6Cfg.NrCommitPorts-1:0]
     - Register file write enable

   * - ``we_fpr_o``
     - out
     - ID_STAGE
     - logic[CVA6Cfg.NrCommitPorts-1:0]
     - Floating point register enable

   * - ``amo_resp_i``
     - in
     - CACHE
     - amo_resp_t
     - Result of AMO operation

   * - ``pc_o``
     - out
     - FRONTEND_CSR
     - logic[riscv::VLEN-1:0]
     - TO_BE_COMPLETED

   * - ``csr_op_o``
     - out
     - CSR_REGFILE
     - fu_op
     - Decoded CSR operation

   * - ``csr_wdata_o``
     - out
     - CSR_REGFILE
     - riscv::xlen_t
     - Data to write to CSR

   * - ``csr_rdata_i``
     - in
     - CSR_REGFILE
     - riscv::xlen_t
     - Data to read from CSR

   * - ``csr_exception_i``
     - in
     - CSR_REGFILE
     - exception_t
     - Exception or interrupt occurred in CSR stage (the same as commit)

   * - ``csr_write_fflags_o``
     - out
     - CSR_REGFILE
     - logic
     - Write the fflags CSR

   * - ``commit_lsu_o``
     - out
     - EX_STAGE
     - logic
     - Commit the pending store

   * - ``commit_lsu_ready_i``
     - in
     - EX_STAGE
     - logic
     - Commit buffer of LSU is ready

   * - ``commit_tran_id_o``
     - out
     - ID_STAGE
     - logic[TRANS_ID_BITS-1:0]
     - Transaction id of first commit port

   * - ``amo_valid_commit_o``
     - out
     - EX_STAGE
     - logic
     - Valid AMO in commit stage

   * - ``no_st_pending_i``
     - in
     - EX_STAGE
     - logic
     - no store is pending

   * - ``commit_csr_o``
     - out
     - EX_STAGE
     - logic
     - Commit the pending CSR instruction

   * - ``fence_i_o``
     - out
     - CONTROLLER
     - logic
     - Flush I$ and pipeline

   * - ``fence_o``
     - out
     - CONTROLLER
     - logic
     - Flush D$ and pipeline

   * - ``flush_commit_o``
     - out
     - CONTROLLER
     - logic
     - Request a pipeline flush

   * - ``sfence_vma_o``
     - out
     - CONTROLLER
     - logic
     - Flush TLBs and pipeline
