..
   Copyright 2024 Thales DIS France SAS
   Licensed under the Solderpad Hardware License, Version 2.1 (the "License");
   you may not use this file except in compliance with the License.
   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
   You may obtain a copy of the License at https://solderpad.org/licenses/

   Original Author: Jean-Roch COULON - Thales

.. _CVA6_controller_ports:

.. list-table:: controller module IO ports
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

   * - ``set_pc_commit_o``
     - out
     - FRONTEND
     - logic
     - Set PC om PC Gen

   * - ``flush_if_o``
     - out
     - FRONTEND
     - logic
     - Flush the IF stage

   * - ``flush_unissued_instr_o``
     - out
     - FRONTEND
     - logic
     - Flush un-issued instructions of the scoreboard

   * - ``flush_id_o``
     - out
     - ID_STAGE
     - logic
     - Flush ID stage

   * - ``flush_ex_o``
     - out
     - EX_STAGE
     - logic
     - Flush EX stage

   * - ``flush_bp_o``
     - out
     - FRONTEND
     - logic
     - Flush branch predictors

   * - ``flush_icache_o``
     - out
     - CACHE
     - logic
     - Flush ICache

   * - ``flush_dcache_o``
     - out
     - CACHE
     - logic
     - Flush DCache

   * - ``flush_dcache_ack_i``
     - in
     - CACHE
     - logic
     - Acknowledge the whole DCache Flush

   * - ``flush_tlb_o``
     - out
     - EX_STAGE
     - logic
     - Flush TLBs

   * - ``halt_csr_i``
     - in
     - CSR_REGFILE
     - logic
     - Halt request from CSR (WFI instruction)

   * - ``halt_acc_i``
     - in
     - ACC_DISPATCHER
     - logic
     - Halt request from accelerator dispatcher

   * - ``halt_o``
     - out
     - COMMIT_STAGE
     - logic
     - Halt signal to commit stage

   * - ``eret_i``
     - in
     - CSR_REGFILE
     - logic
     - Return from exception

   * - ``ex_valid_i``
     - in
     - FRONTEND
     - logic
     - We got an exception, flush the pipeline

   * - ``set_debug_pc_i``
     - in
     - FRONTEND
     - logic
     - set the debug pc from CSR

   * - ``resolved_branch_i``
     - in
     - EX_STAGE
     - bp_resolve_t
     - We got a resolved branch, check if we need to flush the front-end

   * - ``flush_csr_i``
     - in
     - CSR_REGFILE
     - logic
     - We got an instruction which altered the CSR, flush the pipeline

   * - ``fence_i_i``
     - in
     - ACC_DISPATCH
     - logic
     - fence.i in

   * - ``fence_i``
     - in
     - ACC_DISPATCH
     - logic
     - fence in

   * - ``sfence_vma_i``
     - in
     - COMMIT_STAGE
     - logic
     - We got an instruction to flush the TLBs and pipeline

   * - ``flush_commit_i``
     - in
     - COMMIT_STAGE
     - logic
     - Flush request from commit stage

   * - ``flush_acc_i``
     - in
     - ACC_DISPATCHER
     - logic
     - Flush request from accelerator
