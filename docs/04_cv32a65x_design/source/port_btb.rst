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

   * - ``debug_mode_i``
     - in
     - CSR
     - logic
     - Debug mode state

   * - ``vpc_i``
     - in
     - CACHE
     - logic [riscv::VLEN-1:0]
     - Virtual PC

   * - ``btb_update_i``
     - in
     - EXECUTE
     - ariane_pkg::btb_update_t
     - Update BTB with resolved address

   * - ``btb_prediction_o``
     - out
     - FRONTEND
     - ariane_pkg::btb_prediction_t [ariane_pkg::INSTR_PER_FETCH-1:0]
     - BTB Prediction
