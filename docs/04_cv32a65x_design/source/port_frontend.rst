..
   Copyright 2024 Thales DIS France SAS
   Licensed under the Solderpad Hardware License, Version 2.1 (the "License");
   you may not use this file except in compliance with the License.
   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
   You may obtain a copy of the License at https://solderpad.org/licenses/

   Original Author: Jean-Roch COULON - Thales

.. _CVA6_frontend:

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

   * - ``flush_bp_i``
     - in
     - zero
     - logic
     - flush branch prediction

   * - ``halt_i``
     - in
     - CONTROLLER
     - logic
     - halt commit stage

   * - ``debug_mode_i``
     - in
     - CSR
     - logic
     - Debug mode state

   * - ``boot_addr_i``
     - in
     - SUBSYSTEM
     - logic [riscv::VLEN-1:0]
     - Next PC when reset

   * - ``resolved_branch_i``
     - in
     - EXECUTE
     - bp_resolve_t
     - mispredict event and next PC

   * - ``set_pc_commit_i``
     - in
     - CONTROLLER
     - logic
     - Set the PC coming from COMMIT as next PC

   * - ``pc_commit_i``
     - in
     - COMMIT
     - logic [riscv::VLEN-1:0]
     - Next PC when flushing pipeline

   * - ``epc_i``
     - in
     - CSR
     - logic [riscv::VLEN-1:0]
     - Next PC when returning from exception

   * - ``eret_i``
     - in
     - CSR
     - logic
     - Return from exception event

   * - ``trap_vector_base_i``
     - in
     - CSR
     - logic [riscv::VLEN-1:0]
     - Next PC when jumping into exception

   * - ``ex_valid_i``
     - in
     - COMMIT
     - logic
     - Exception event

   * - ``set_debug_pc_i``
     - in
     - CSR
     - logic
     - Debug event

   * - ``icache_dreq_o``
     - out
     - CACHES
     - icache_dreq_t
     - Handshake between CACHE and FRONTEND (fetch)

   * - ``icache_dreq_i``
     - in
     - CACHES
     - icache_drsp_t
     - Handshake between CACHE and FRONTEND (fetch)

   * - ``fetch_entry_o``
     - out
     - DECODE
     - fetch_entry_t
     - Handshake's data between fetch and decode

   * - ``fetch_entry_valid_o``
     - out
     - DECODE
     - logic
     - Handshake's valid between fetch and decode

   * - ``fetch_entry_ready_i``
     - in
     - DECODE
     - logic
     - Handshake's ready between fetch and decode
