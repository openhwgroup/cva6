..
   Copyright 2024 Thales DIS France SAS
   Licensed under the Solderpad Hardware License, Version 2.1 (the "License");
   you may not use this file except in compliance with the License.
   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
   You may obtain a copy of the License at https://solderpad.org/licenses/

   Original Author: Jean-Roch COULON - Thales

.. _CVA6_lsu_bypass_ports:

.. list-table:: **lsu_bypass module** IO ports
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
     - TO_BE_COMPLETED
     - TO_BE_COMPLETED
     - logic

   * - ``lsu_req_i``
     - in
     - TO_BE_COMPLETED
     - TO_BE_COMPLETED
     - lsu_ctrl_t

   * - ``lsu_req_valid_i``
     - in
     - TO_BE_COMPLETED
     - TO_BE_COMPLETED
     - logic

   * - ``pop_ld_i``
     - in
     - TO_BE_COMPLETED
     - TO_BE_COMPLETED
     - logic

   * - ``pop_st_i``
     - in
     - TO_BE_COMPLETED
     - TO_BE_COMPLETED
     - logic

   * - ``lsu_ctrl_o``
     - out
     - TO_BE_COMPLETED
     - TO_BE_COMPLETED
     - lsu_ctrl_t

   * - ``ready_o``
     - out
     - TO_BE_COMPLETED
     - TO_BE_COMPLETED
     - logic


