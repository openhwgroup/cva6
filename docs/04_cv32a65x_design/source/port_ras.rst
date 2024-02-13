..
   Copyright 2024 Thales DIS France SAS
   Licensed under the Solderpad Hardware License, Version 2.1 (the "License");
   you may not use this file except in compliance with the License.
   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
   You may obtain a copy of the License at https://solderpad.org/licenses/

   Original Author: Jean-Roch COULON - Thales

.. _CVA6_ras_ports:

.. list-table:: ras module IO ports
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

   * - ``push_i``
     - in
     - Push address in RAS
     - FRONTEND
     - Push address in RAS
     - logic

   * - ``pop_i``
     - in
     - Pop address from RAS
     - FRONTEND
     - Pop address from RAS
     - logic

   * - ``data_i``
     - in
     - Data to be pushed
     - FRONTEND
     - Data to be pushed
     - logic[riscv::VLEN-1:0]

   * - ``data_o``
     - out
     - Popped data
     - FRONTEND
     - Popped data
     - ariane_pkg::ras_t
