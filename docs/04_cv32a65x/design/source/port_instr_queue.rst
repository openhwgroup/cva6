..
   Copyright 2024 Thales DIS France SAS
   Licensed under the Solderpad Hardware License, Version 2.1 (the "License");
   you may not use this file except in compliance with the License.
   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
   You may obtain a copy of the License at https://solderpad.org/licenses/

   Original Author: Jean-Roch COULON - Thales

.. _CVA6_instr_queue_ports:

.. list-table:: **instr_queue module** IO ports
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

   * - ``instr_i``
     - in
     - Instruction
     - instr_realign
     - logic[CVA6Cfg.INSTR_PER_FETCH-1:0][31:0]

   * - ``addr_i``
     - in
     - Instruction address
     - instr_realign
     - logic[CVA6Cfg.INSTR_PER_FETCH-1:0][CVA6Cfg.VLEN-1:0]

   * - ``valid_i``
     - in
     - Instruction is valid
     - instr_realign
     - logic[CVA6Cfg.INSTR_PER_FETCH-1:0]

   * - ``ready_o``
     - out
     - Handshake’s ready with CACHE
     - CACHE
     - logic

   * - ``consumed_o``
     - out
     - Indicates instructions consummed, or popped by ID_STAGE
     - FRONTEND
     - logic[CVA6Cfg.INSTR_PER_FETCH-1:0]

   * - ``exception_i``
     - in
     - Exception (which is page-table fault)
     - CACHE
     - ariane_pkg::frontend_exception_t

   * - ``exception_addr_i``
     - in
     - Exception address
     - CACHE
     - logic[CVA6Cfg.VLEN-1:0]

   * - ``predict_address_i``
     - in
     - Branch predict
     - FRONTEND
     - logic[CVA6Cfg.VLEN-1:0]

   * - ``cf_type_i``
     - in
     - Instruction predict address
     - FRONTEND
     - ariane_pkg::cf_t[CVA6Cfg.INSTR_PER_FETCH-1:0]

   * - ``replay_o``
     - out
     - Replay instruction because one of the FIFO was  full
     - FRONTEND
     - logic

   * - ``replay_addr_o``
     - out
     - Address at which to replay the fetch
     - FRONTEND
     - logic[CVA6Cfg.VLEN-1:0]

   * - ``fetch_entry_o``
     - out
     - Handshake’s data with ID_STAGE
     - ID_STAGE
     - fetch_entry_t[ariane_pkg::SUPERSCALAR:0]

   * - ``fetch_entry_valid_o``
     - out
     - Handshake’s valid with ID_STAGE
     - ID_STAGE
     - logic[ariane_pkg::SUPERSCALAR:0]

   * - ``fetch_entry_ready_i``
     - in
     - Handshake’s ready with ID_STAGE
     - ID_STAGE
     - logic[ariane_pkg::SUPERSCALAR:0]

Due to cv32a65x configuration, some ports are tied to a static value. These ports do not appear in the above table, they are listed below

| As RVH = False,
|   ``exception_gpaddr_i`` input is tied to 0
|   ``exception_tinst_i`` input is tied to 0
|   ``exception_gva_i`` input is tied to 0

