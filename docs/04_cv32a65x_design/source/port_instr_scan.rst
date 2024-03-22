..
   Copyright 2024 Thales DIS France SAS
   Licensed under the Solderpad Hardware License, Version 2.1 (the "License");
   you may not use this file except in compliance with the License.
   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
   You may obtain a copy of the License at https://solderpad.org/licenses/

   Original Author: Jean-Roch COULON - Thales

.. _CVA6_instr_scan_ports:

.. list-table:: **instr_scan module** IO ports
   :header-rows: 1

   * - Signal
     - IO
     - Description
     - connexion
     - Type

   * - ``instr_i``
     - in
     - Instruction to be predecoded
     - instr_realign
     - logic[31:0]

   * - ``rvi_return_o``
     - out
     - Return instruction
     - FRONTEND
     - logic

   * - ``rvi_call_o``
     - out
     - JAL instruction
     - FRONTEND
     - logic

   * - ``rvi_branch_o``
     - out
     - Branch instruction
     - FRONTEND
     - logic

   * - ``rvi_jalr_o``
     - out
     - JALR instruction
     - FRONTEND
     - logic

   * - ``rvi_jump_o``
     - out
     - Unconditional jump instruction
     - FRONTEND
     - logic

   * - ``rvi_imm_o``
     - out
     - Instruction immediat
     - FRONTEND
     - logic[CVA6Cfg.VLEN-1:0]

   * - ``rvc_branch_o``
     - out
     - Branch compressed instruction
     - FRONTEND
     - logic

   * - ``rvc_jump_o``
     - out
     - Unconditional jump compressed instruction
     - FRONTEND
     - logic

   * - ``rvc_jr_o``
     - out
     - JR compressed instruction
     - FRONTEND
     - logic

   * - ``rvc_return_o``
     - out
     - Return compressed instruction
     - FRONTEND
     - logic

   * - ``rvc_jalr_o``
     - out
     - JALR compressed instruction
     - FRONTEND
     - logic

   * - ``rvc_call_o``
     - out
     - JAL compressed instruction
     - FRONTEND
     - logic

   * - ``rvc_imm_o``
     - out
     - Instruction compressed immediat
     - FRONTEND
     - logic[CVA6Cfg.VLEN-1:0]


