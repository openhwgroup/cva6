..
   Copyright 2024 Thales DIS France SAS
   Licensed under the Solderpad Hardware License, Version 2.1 (the "License");
   you may not use this file except in compliance with the License.
   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
   You may obtain a copy of the License at https://solderpad.org/licenses/

   Original Author: Jean-Roch COULON - Thales

.. _CVA6_instr_queue_ports:

.. list-table:: instr_queue module IO ports
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

   * - ``instr_i``
     - in
     - instr_realign
     - Instruction
     - logic[ariane_pkg::INSTR_PER_FETCH-1:0][31:0]

   * - ``addr_i``
     - in
     - instr_realign
     - Instruction address
     - logic[ariane_pkg::INSTR_PER_FETCH-1:0][riscv::VLEN-1:0]

   * - ``valid_i``
     - in
     - instr_realign
     - Instruction is valid
     - logic[ariane_pkg::INSTR_PER_FETCH-1:0]

   * - ``ready_o``
     - out
     - CACHE
     - Handshake’s ready with CACHE
     - logic

   * - ``consumed_o``
     - out
     - FRONTEND
     - Indicates instructions consummed, or popped by ID_STAGE
     - logic[ariane_pkg::INSTR_PER_FETCH-1:0]

   * - ``exception_i``
     - in
     - CACHE
     - Exception (which is page-table fault)
     - ariane_pkg::frontend_exception_t

   * - ``exception_addr_i``
     - in
     - CACHE
     - Exception address
     - logic[riscv::VLEN-1:0]

   * - ``predict_address_i``
     - in
     - FRONTEND
     - Branch predict
     - logic[riscv::VLEN-1:0]

   * - ``cf_type_i``
     - in
     - FRONTEND
     - Instruction predict address
     - ariane_pkg::cf_t[ariane_pkg::INSTR_PER_FETCH-1:0]

   * - ``replay_o``
     - out
     - FRONTEND
     - Replay instruction because one of the FIFO was  full
     - logic

   * - ``replay_addr_o``
     - out
     - FRONTEND
     - Address at which to replay the fetch
     - logic[riscv::VLEN-1:0]

   * - ``fetch_entry_o``
     - out
     - ID_STAGE
     - Handshake’s data with ID_STAGE
     - ariane_pkg::fetch_entry_t

   * - ``fetch_entry_valid_o``
     - out
     - ID_STAGE
     - Handshake’s valid with ID_STAGE
     - logic

   * - ``fetch_entry_ready_i``
     - in
     - ID_STAGE
     - Handshake’s ready with ID_STAGE
     - logic
