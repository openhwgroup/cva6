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

   * - ``instr_i``
     - in
     - instr_realign
     - logic[ariane_pkg::INSTR_PER_FETCH-1:0][31:0]
     - Instruction

   * - ``addr_i``
     - in
     - instr_realign
     - logic[ariane_pkg::INSTR_PER_FETCH-1:0][riscv::VLEN-1:0]
     - Instruction address

   * - ``valid_i``
     - in
     - instr_realign
     - logic[ariane_pkg::INSTR_PER_FETCH-1:0]
     - Instruction is valid

   * - ``ready_o``
     - out
     - CACHE
     - logic
     - Handshake’s ready with CACHE

   * - ``consumed_o``
     - out
     - FRONTEND
     - logic[ariane_pkg::INSTR_PER_FETCH-1:0]
     - Indicates instructions consummed, or popped by ID_STAGE

   * - ``exception_i``
     - in
     - CACHE
     - ariane_pkg::frontend_exception_t
     - Exception (which is page-table fault)

   * - ``exception_addr_i``
     - in
     - CACHE
     - logic[riscv::VLEN-1:0]
     - Exception address

   * - ``predict_address_i``
     - in
     - FRONTEND
     - logic[riscv::VLEN-1:0]
     - Branch predict

   * - ``cf_type_i``
     - in
     - FRONTEND
     - ariane_pkg::cf_t[ariane_pkg::INSTR_PER_FETCH-1:0]
     - Instruction predict address

   * - ``replay_o``
     - out
     - FRONTEND
     - logic
     - Replay instruction because one of the FIFO was  full

   * - ``replay_addr_o``
     - out
     - FRONTEND
     - logic[riscv::VLEN-1:0]
     - Address at which to replay the fetch

   * - ``fetch_entry_o``
     - out
     - ID_STAGE
     - ariane_pkg::fetch_entry_t
     - Handshake’s data with ID_STAGE

   * - ``fetch_entry_valid_o``
     - out
     - ID_STAGE
     - logic
     - Handshake’s valid with ID_STAGE

   * - ``fetch_entry_ready_i``
     - in
     - ID_STAGE
     - logic
     - Handshake’s ready with ID_STAGE
