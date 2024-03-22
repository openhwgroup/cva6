..
   Copyright 2024 Thales DIS France SAS
   Licensed under the Solderpad Hardware License, Version 2.1 (the "License");
   you may not use this file except in compliance with the License.
   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
   You may obtain a copy of the License at https://solderpad.org/licenses/

   Original Author: Jean-Roch COULON - Thales

.. _CVA6_multiplier_ports:

.. list-table:: **multiplier module** IO ports
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

   * - ``trans_id_i``
     - in
     - Multiplier transaction ID
     - Mult
     - logic[CVA6Cfg.TRANS_ID_BITS-1:0]

   * - ``mult_valid_i``
     - in
     - Multiplier instruction is valid
     - Mult
     - logic

   * - ``operation_i``
     - in
     - Multiplier operation
     - Mult
     - fu_op

   * - ``operand_a_i``
     - in
     - A operand
     - Mult
     - logic[CVA6Cfg.XLEN-1:0]

   * - ``operand_b_i``
     - in
     - B operand
     - Mult
     - logic[CVA6Cfg.XLEN-1:0]

   * - ``result_o``
     - out
     - Multiplier result
     - Mult
     - logic[CVA6Cfg.XLEN-1:0]

   * - ``mult_valid_o``
     - out
     - Mutliplier result is valid
     - Mult
     - logic

   * - ``mult_ready_o``
     - out
     - Multiplier FU is ready
     - Mult
     - logic

   * - ``mult_trans_id_o``
     - out
     - Multiplier transaction ID
     - Mult
     - logic[CVA6Cfg.TRANS_ID_BITS-1:0]


