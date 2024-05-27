..
   Copyright 2024 Thales DIS France SAS
   Licensed under the Solderpad Hardware License, Version 2.1 (the "License");
   you may not use this file except in compliance with the License.
   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
   You may obtain a copy of the License at https://solderpad.org/licenses/

   Original Author: Jean-Roch COULON - Thales

.. _CVA6_frontend_ports:

.. list-table:: **frontend module** IO ports
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

   * - ``boot_addr_i``
     - in
     - Next PC when reset
     - SUBSYSTEM
     - logic[CVA6Cfg.VLEN-1:0]

   * - ``flush_i``
     - in
     - Flush requested by FENCE, mis-predict and exception
     - CONTROLLER
     - logic

   * - ``halt_i``
     - in
     - Halt requested by WFI and Accelerate port
     - CONTROLLER
     - logic

   * - ``set_pc_commit_i``
     - in
     - Set COMMIT PC as next PC requested by FENCE, CSR side-effect and Accelerate port
     - CONTROLLER
     - logic

   * - ``pc_commit_i``
     - in
     - COMMIT PC
     - COMMIT
     - logic[CVA6Cfg.VLEN-1:0]

   * - ``ex_valid_i``
     - in
     - Exception event
     - COMMIT
     - logic

   * - ``resolved_branch_i``
     - in
     - Mispredict event and next PC
     - EXECUTE
     - bp_resolve_t

   * - ``eret_i``
     - in
     - Return from exception event
     - CSR
     - logic

   * - ``epc_i``
     - in
     - Next PC when returning from exception
     - CSR
     - logic[CVA6Cfg.VLEN-1:0]

   * - ``trap_vector_base_i``
     - in
     - Next PC when jumping into exception
     - CSR
     - logic[CVA6Cfg.VLEN-1:0]

   * - ``icache_dreq_o``
     - out
     - Handshake between CACHE and FRONTEND (fetch)
     - CACHES
     - icache_dreq_t

   * - ``icache_dreq_i``
     - in
     - Handshake between CACHE and FRONTEND (fetch)
     - CACHES
     - icache_drsp_t

   * - ``fetch_entry_o``
     - out
     - Handshake's data between fetch and decode
     - ID_STAGE
     - fetch_entry_t[ariane_pkg::SUPERSCALAR:0]

   * - ``fetch_entry_valid_o``
     - out
     - Handshake's valid between fetch and decode
     - ID_STAGE
     - logic[ariane_pkg::SUPERSCALAR:0]

   * - ``fetch_entry_ready_i``
     - in
     - Handshake's ready between fetch and decode
     - ID_STAGE
     - logic[ariane_pkg::SUPERSCALAR:0]

Due to cv32a65x configuration, some ports are tied to a static value. These ports do not appear in the above table, they are listed below

| For any HW configuration,
|   ``flush_bp_i`` input is tied to 0
| As DebugEn = False,
|   ``set_debug_pc_i`` input is tied to 0
|   ``debug_mode_i`` input is tied to 0

