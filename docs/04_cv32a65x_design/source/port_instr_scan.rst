..
   Copyright 2024 Thales DIS France SAS
   Licensed under the Solderpad Hardware License, Version 2.1 (the "License");
   you may not use this file except in compliance with the License.
   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
   You may obtain a copy of the License at https://solderpad.org/licenses/

   Original Author: Jean-Roch COULON - Thales

.. _CVA6_instr_scan_ports:

.. list-table:: instr_scan module IO ports
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
     - Instruction to be predecoded
     - logic[31:0]

   * - ``rvi_return_o``
     - out
     - Return instruction
     - FRONTEND
     - Return instruction
     - logic

   * - ``rvi_call_o``
     - out
     - JAL instruction
     - FRONTEND
     - JAL instruction
     - logic

   * - ``rvi_branch_o``
     - out
     - Branch instruction
     - FRONTEND
     - Branch instruction
     - logic

   * - ``rvi_jalr_o``
     - out
     - JALR instruction
     - FRONTEND
     - JALR instruction
     - logic

   * - ``rvi_jump_o``
     - out
     - Unconditional jump instruction
     - FRONTEND
     - Unconditional jump instruction
     - logic

   * - ``rvi_imm_o``
     - out
     - Instruction immediat
     - FRONTEND
     - Instruction immediat
     - logic[riscv::VLEN-1:0]

   * - ``rvc_branch_o``
     - out
     - Branch compressed instruction
     - FRONTEND
     - Branch compressed instruction
     - logic

   * - ``rvc_jump_o``
     - out
     - Unconditional jump compressed instruction
     - FRONTEND
     - Unconditional jump compressed instruction
     - logic

   * - ``rvc_jr_o``
     - out
     - JR compressed instruction
     - FRONTEND
     - JR compressed instruction
     - logic

   * - ``rvc_return_o``
     - out
     - Return compressed instruction
     - FRONTEND
     - Return compressed instruction
     - logic

   * - ``rvc_jalr_o``
     - out
     - JALR compressed instruction
     - FRONTEND
     - JALR compressed instruction
     - logic

   * - ``rvc_call_o``
     - out
     - JAL compressed instruction
     - FRONTEND
     - JAL compressed instruction
     - logic

   * - ``rvc_imm_o``
     - out
     - Instruction compressed immediat
     - FRONTEND
     - Instruction compressed immediat
     - logic[riscv::VLEN-1:0]
