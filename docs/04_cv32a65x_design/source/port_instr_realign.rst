..
   Copyright 2024 Thales DIS France SAS
   Licensed under the Solderpad Hardware License, Version 2.1 (the "License");
   you may not use this file except in compliance with the License.
   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
   You may obtain a copy of the License at https://solderpad.org/licenses/

   Original Author: Jean-Roch COULON - Thales

.. _CVA6_instr_realign_ports:

.. list-table:: **instr_realign module** IO ports
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

   * - ``valid_i``
     - in
     - 32-bit block is valid
     - CACHE
     - logic

   * - ``serving_unaligned_o``
     - out
     - Instruction is unaligned
     - FRONTEND
     - logic

   * - ``address_i``
     - in
     - 32-bit block address
     - CACHE
     - logic[CVA6Cfg.VLEN-1:0]

   * - ``data_i``
     - in
     - 32-bit block
     - CACHE
     - logic[CVA6Cfg.FETCH_WIDTH-1:0]

   * - ``valid_o``
     - out
     - instruction is valid
     - FRONTEND
     - logic[CVA6Cfg.INSTR_PER_FETCH-1:0]

   * - ``addr_o``
     - out
     - Instruction address
     - FRONTEND
     - logic[CVA6Cfg.INSTR_PER_FETCH-1:0][CVA6Cfg.VLEN-1:0]

   * - ``instr_o``
     - out
     - Instruction
     - instr_scan&instr_queue
     - logic[CVA6Cfg.INSTR_PER_FETCH-1:0][31:0]


