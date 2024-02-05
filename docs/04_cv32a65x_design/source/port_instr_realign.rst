..
   Copyright 2024 Thales DIS France SAS
   Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
   You may obtain a copy of the License at https://solderpad.org/licenses/

   Original Author: Jean-Roch COULON - Thales

.. _CVA6_instr_realign:

.. list-table:: instr_realign module IO ports
   :header-rows: 1

   * - Signal
     - IO
     - connection
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

   * - ``valid_i``
     - in
     - CACHE
     - logic
     - 32-bit block is valid

   * - ``serving_unaligned_o``
     - out
     - FRONTEND
     - logic
     - Instruction is unaligned

   * - ``address_i``
     - in
     - CACHE
     - logic [riscv::VLEN-1:0]
     - 32-bit block address

   * - ``data_i``
     - in
     - CACHE
     - logic [FETCH_WIDTH-1:0]
     - 32-bit block

   * - ``valid_o``
     - out
     - FRONTEND
     - logic [INSTR_PER_FETCH-1:0]
     - instruction is valid

   * - ``addr_o``
     - out
     - FRONTEND
     - logic [INSTR_PER_FETCH-1:0][riscv::VLEN-1:0]
     - Instruction address

   * - ``instr_o``
     - out
     - none
     - logic [INSTR_PER_FETCH-1:0][31:0]
     - none
