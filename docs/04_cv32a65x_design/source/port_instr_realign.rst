..
   Copyright 2024 Thales DIS France SAS
   Licensed under the Solderpad Hardware License, Version 2.1 (the "License");
   you may not use this file except in compliance with the License.
   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
   You may obtain a copy of the License at https://solderpad.org/licenses/

   Original Author: Jean-Roch COULON - Thales

.. _CVA6_instr_realign_ports:

.. list-table:: instr_realign module IO ports
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

   * - ``valid_i``
     - in
     - CACHE
     - 32-bit block is valid
     - logic

   * - ``serving_unaligned_o``
     - out
     - FRONTEND
     - Instruction is unaligned
     - logic

   * - ``address_i``
     - in
     - CACHE
     - 32-bit block address
     - logic[riscv::VLEN-1:0]

   * - ``data_i``
     - in
     - CACHE
     - 32-bit block
     - logic[FETCH_WIDTH-1:0]

   * - ``valid_o``
     - out
     - FRONTEND
     - instruction is valid
     - logic[INSTR_PER_FETCH-1:0]

   * - ``addr_o``
     - out
     - FRONTEND
     - Instruction address
     - logic[INSTR_PER_FETCH-1:0][riscv::VLEN-1:0]

   * - ``instr_o``
     - out
     - none
     - none
     - logic[INSTR_PER_FETCH-1:0][31:0]
