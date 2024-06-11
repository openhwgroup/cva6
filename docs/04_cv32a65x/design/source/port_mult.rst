..
   Copyright 2024 Thales DIS France SAS
   Licensed under the Solderpad Hardware License, Version 2.1 (the "License");
   you may not use this file except in compliance with the License.
   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
   You may obtain a copy of the License at https://solderpad.org/licenses/

   Original Author: Jean-Roch COULON - Thales

.. _CVA6_mult_ports:

.. list-table:: **mult module** IO ports
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
     - Flush
     - CONTROLLER
     - logic

   * - ``fu_data_i``
     - in
     - FU data needed to execute instruction
     - ISSUE_STAGE
     - fu_data_t

   * - ``mult_valid_i``
     - in
     - Mult instruction is valid
     - ISSUE_STAGE
     - logic

   * - ``result_o``
     - out
     - Mult result
     - ISSUE_STAGE
     - logic[CVA6Cfg.XLEN-1:0]

   * - ``mult_valid_o``
     - out
     - Mult result is valid
     - ISSUE_STAGE
     - logic

   * - ``mult_ready_o``
     - out
     - Mutl is ready
     - ISSUE_STAGE
     - logic

   * - ``mult_trans_id_o``
     - out
     - Mult transaction ID
     - ISSUE_STAGE
     - logic[CVA6Cfg.TRANS_ID_BITS-1:0]


