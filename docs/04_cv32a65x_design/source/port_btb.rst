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
     - Description
     - connexion
     - Type

   * - ``clk_i``
     - in
     - Subsystem Clock
     - SUBSYSTEM
     - Subsystem Clock
     - logic

   * - ``rst_ni``
     - in
     - Asynchronous reset active low
     - SUBSYSTEM
     - Asynchronous reset active low
     - logic

   * - ``flush_i``
     - in
     - Fetch flush request
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
     - Virtual PC
     - CACHE
     - Virtual PC
     - logic[riscv::VLEN-1:0]

   * - ``btb_update_i``
     - in
     - Update BTB with resolved address
     - EXECUTE
     - Update BTB with resolved address
     - ariane_pkg::btb_update_t

   * - ``btb_prediction_o``
     - out
     - BTB Prediction
     - FRONTEND
     - BTB Prediction
     - ariane_pkg::btb_prediction_t[ariane_pkg::INSTR_PER_FETCH-1:0]
