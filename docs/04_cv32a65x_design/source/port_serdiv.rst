..
   Copyright 2024 Thales DIS France SAS
   Licensed under the Solderpad Hardware License, Version 2.1 (the "License");
   you may not use this file except in compliance with the License.
   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
   You may obtain a copy of the License at https://solderpad.org/licenses/

   Original Author: Jean-Roch COULON - Thales

.. _CVA6_serdiv_ports:

.. list-table:: **serdiv module** IO ports
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

   * - ``id_i``
     - in
     - Serdiv translation ID
     - Mult
     - logic[CVA6Cfg.TRANS_ID_BITS-1:0]

   * - ``op_a_i``
     - in
     - A operand
     - Mult
     - logic[WIDTH-1:0]

   * - ``op_b_i``
     - in
     - B operand
     - Mult
     - logic[WIDTH-1:0]

   * - ``rem``
     - in
     - Serdiv operation
     - Mult
     - logic[1:0]opcode_i,//0:udiv,2:urem,1:div,3:

   * - ``in_vld_i``
     - in
     - Serdiv instruction is valid
     - Mult
     - logic

   * - ``in_rdy_o``
     - out
     - Serdiv FU is ready
     - Mult
     - logic

   * - ``flush_i``
     - in
     - Flush
     - CONTROLLER
     - logic

   * - ``out_vld_o``
     - out
     - Serdiv result is valid
     - Mult
     - logic

   * - ``out_rdy_i``
     - in
     - Serdiv is ready
     - Mult
     - logic

   * - ``id_o``
     - out
     - Serdiv transaction ID
     - Mult
     - logic[CVA6Cfg.TRANS_ID_BITS-1:0]

   * - ``res_o``
     - out
     - Serdiv result
     - Mult
     - logic[WIDTH-1:0]


