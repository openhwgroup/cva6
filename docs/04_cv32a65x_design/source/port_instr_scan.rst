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
     - Connection
     - Type
     - Description

   * - ``instr_i``
     - in
     - instr_realign
     - Instruction to be predecoded
     - logic[31:0]

   * - ``rvi_return_o``
     - out
     - FRONTEND
     - Return instruction
     - logic

   * - ``rvi_call_o``
     - out
     - FRONTEND
     - JAL instruction
     - logic

   * - ``rvi_branch_o``
     - out
     - FRONTEND
     - Branch instruction
     - logic

   * - ``rvi_jalr_o``
     - out
     - FRONTEND
     - JALR instruction
     - logic

   * - ``rvi_jump_o``
     - out
     - FRONTEND
     - Unconditional jump instruction
     - logic

   * - ``rvi_imm_o``
     - out
     - FRONTEND
     - Instruction immediat
     - logic[riscv::VLEN-1:0]

   * - ``rvc_branch_o``
     - out
     - FRONTEND
     - Branch compressed instruction
     - logic

   * - ``rvc_jump_o``
     - out
     - FRONTEND
     - Unconditional jump compressed instruction
     - logic

   * - ``rvc_jr_o``
     - out
     - FRONTEND
     - JR compressed instruction
     - logic

   * - ``rvc_return_o``
     - out
     - FRONTEND
     - Return compressed instruction
     - logic

   * - ``rvc_jalr_o``
     - out
     - FRONTEND
     - JALR compressed instruction
     - logic

   * - ``rvc_call_o``
     - out
     - FRONTEND
     - JAL compressed instruction
     - logic

   * - ``rvc_imm_o``
     - out
     - FRONTEND
     - Instruction compressed immediat
     - logic[riscv::VLEN-1:0]
