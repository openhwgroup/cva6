..
   Copyright 2024 Thales DIS France SAS
   Licensed under the Solderpad Hardware License, Version 2.1 (the "License");
   you may not use this file except in compliance with the License.
   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
   You may obtain a copy of the License at https://solderpad.org/licenses/

   Original Author: Jean-Roch COULON - Thales

.. _CVA6_controller_ports:

.. list-table:: **controller module** IO ports
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

   * - ``set_pc_commit_o``
     - out
     - Set PC om PC Gen
     - FRONTEND
     - logic

   * - ``flush_if_o``
     - out
     - Flush the IF stage
     - FRONTEND
     - logic

   * - ``flush_unissued_instr_o``
     - out
     - Flush un-issued instructions of the scoreboard
     - FRONTEND
     - logic

   * - ``flush_id_o``
     - out
     - Flush ID stage
     - ID_STAGE
     - logic

   * - ``flush_ex_o``
     - out
     - Flush EX stage
     - EX_STAGE
     - logic

   * - ``flush_bp_o``
     - out
     - Flush branch predictors
     - FRONTEND
     - logic

   * - ``flush_icache_o``
     - out
     - Flush ICache
     - CACHE
     - logic

   * - ``flush_dcache_o``
     - out
     - Flush DCache
     - CACHE
     - logic

   * - ``flush_dcache_ack_i``
     - in
     - Acknowledge the whole DCache Flush
     - CACHE
     - logic

   * - ``halt_csr_i``
     - in
     - Halt request from CSR (WFI instruction)
     - CSR_REGFILE
     - logic

   * - ``halt_o``
     - out
     - Halt signal to commit stage
     - COMMIT_STAGE
     - logic

   * - ``eret_i``
     - in
     - Return from exception
     - CSR_REGFILE
     - logic

   * - ``ex_valid_i``
     - in
     - We got an exception, flush the pipeline
     - FRONTEND
     - logic

   * - ``resolved_branch_i``
     - in
     - We got a resolved branch, check if we need to flush the front-end
     - EX_STAGE
     - bp_resolve_t

   * - ``flush_csr_i``
     - in
     - We got an instruction which altered the CSR, flush the pipeline
     - CSR_REGFILE
     - logic

   * - ``flush_commit_i``
     - in
     - Flush request from commit stage
     - COMMIT_STAGE
     - logic

Due to cv32a65x configuration, some ports are tied to a static value. These ports do not appear in the above table, they are listed below

| As RVH = False,
|   ``v_i`` input is tied to 0
|   ``flush_tlb_vvma_o`` output is tied to 0
|   ``flush_tlb_gvma_o`` output is tied to 0
|   ``hfence_vvma_i`` input is tied to 0
|   ``hfence_gvma_i`` input is tied to 0
| As MMUPresent = 0,
|   ``flush_tlb_o`` output is tied to 0
| As EnableAccelerator = 0,
|   ``halt_acc_i`` input is tied to 0
|   ``flush_acc_i`` input is tied to 0
| As DebugEn = False,
|   ``set_debug_pc_i`` input is tied to 0
| As FenceEn = 0,
|   ``fence_i_i`` input is tied to 0
|   ``fence_i`` input is tied to 0
| As RVS = False,
|   ``sfence_vma_i`` input is tied to 0

