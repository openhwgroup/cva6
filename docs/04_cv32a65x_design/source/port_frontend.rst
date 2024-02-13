..
   Copyright 2024 Thales DIS France SAS
   Licensed under the Solderpad Hardware License, Version 2.1 (the "License");
   you may not use this file except in compliance with the License.
   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
   You may obtain a copy of the License at https://solderpad.org/licenses/

   Original Author: Jean-Roch COULON - Thales

.. _CVA6_frontend_ports:

.. list-table:: frontend module IO ports
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

   * - ``flush_bp_i``
     - in
     - zero
     - flush branch prediction
     - logic

   * - ``halt_i``
     - in
     - CONTROLLER
     - halt commit stage
     - logic

   * - ``debug_mode_i``
     - in
     - CSR
     - Debug mode state
     - logic

   * - ``boot_addr_i``
     - in
     - SUBSYSTEM
     - Next PC when reset
     - logic[riscv::VLEN-1:0]

   * - ``resolved_branch_i``
     - in
     - EXECUTE
     - mispredict event and next PC
     - bp_resolve_t

   * - ``set_pc_commit_i``
     - in
     - CONTROLLER
     - Set the PC coming from COMMIT as next PC
     - logic

   * - ``pc_commit_i``
     - in
     - COMMIT
     - Next PC when flushing pipeline
     - logic[riscv::VLEN-1:0]

   * - ``epc_i``
     - in
     - CSR
     - Next PC when returning from exception
     - logic[riscv::VLEN-1:0]

   * - ``eret_i``
     - in
     - CSR
     - Return from exception event
     - logic

   * - ``trap_vector_base_i``
     - in
     - CSR
     - Next PC when jumping into exception
     - logic[riscv::VLEN-1:0]

   * - ``ex_valid_i``
     - in
     - COMMIT
     - Exception event
     - logic

   * - ``set_debug_pc_i``
     - in
     - CSR
     - Debug event
     - logic

   * - ``icache_dreq_o``
     - out
     - CACHES
     - Handshake between CACHE and FRONTEND (fetch)
     - icache_dreq_t

   * - ``icache_dreq_i``
     - in
     - CACHES
     - Handshake between CACHE and FRONTEND (fetch)
     - icache_drsp_t

   * - ``fetch_entry_o``
     - out
     - ID_STAGE
     - Handshake's data between fetch and decode
     - fetch_entry_t

   * - ``fetch_entry_valid_o``
     - out
     - ID_STAGE
     - Handshake's valid between fetch and decode
     - logic

   * - ``fetch_entry_ready_i``
     - in
     - ID_STAGE
     - Handshake's ready between fetch and decode
     - logic
