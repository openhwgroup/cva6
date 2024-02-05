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

   * - ``push_i``
     - in
     - FRONTEND
     - logic
     - Push address in RAS

   * - ``pop_i``
     - in
     - FRONTEND
     - logic
     - Pop address from RAS

   * - ``data_i``
     - in
     - FRONTEND
     - logic [riscv::VLEN-1:0]
     - Data to be pushed

   * - ``data_o``
     - out
     - FRONTEND
     - ariane_pkg::ras_t
     - Popped data
