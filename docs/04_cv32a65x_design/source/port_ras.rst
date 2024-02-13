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

   * - ``push_i``
     - in
     - FRONTEND
     - Push address in RAS
     - logic

   * - ``pop_i``
     - in
     - FRONTEND
     - Pop address from RAS
     - logic

   * - ``data_i``
     - in
     - FRONTEND
     - Data to be pushed
     - logic[riscv::VLEN-1:0]

   * - ``data_o``
     - out
     - FRONTEND
     - Popped data
     - ariane_pkg::ras_t
