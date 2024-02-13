..
   Copyright 2024 Thales DIS France SAS
   Licensed under the Solderpad Hardware License, Version 2.1 (the "License");
   you may not use this file except in compliance with the License.
   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
   You may obtain a copy of the License at https://solderpad.org/licenses/

   Original Author: Jean-Roch COULON - Thales

.. _CVA6_btb_ports:

.. list-table:: btb module IO ports
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

   * - ``debug_mode_i``
     - in
     - CSR
     - Debug mode state
     - logic

   * - ``vpc_i``
     - in
     - CACHE
     - Virtual PC
     - logic[riscv::VLEN-1:0]

   * - ``btb_update_i``
     - in
     - EXECUTE
     - Update BTB with resolved address
     - ariane_pkg::btb_update_t

   * - ``btb_prediction_o``
     - out
     - FRONTEND
     - BTB Prediction
     - ariane_pkg::btb_prediction_t[ariane_pkg::INSTR_PER_FETCH-1:0]
