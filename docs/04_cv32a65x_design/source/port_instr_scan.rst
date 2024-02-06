..
   Copyright 2024 Thales DIS France SAS
   Licensed under the Solderpad Hardware License, Version 2.1 (the "License");
   you may not use this file except in compliance with the License.
   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
   You may obtain a copy of the License at https://solderpad.org/licenses/

   Original Author: Jean-Roch COULON - Thales

.. _CVA6_instr_scan:

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
     - logic [31:0]
     - Instruction to be predecoded

   * - ``rvi_return_o``
     - out
     - FRONTEND
     - logic
     - Return instruction

   * - ``rvi_call_o``
     - out
     - FRONTEND
     - logic
     - JAL instruction

   * - ``rvi_branch_o``
     - out
     - FRONTEND
     - logic
     - Branch instruction

   * - ``rvi_jalr_o``
     - out
     - FRONTEND
     - logic
     - JALR instruction

   * - ``rvi_jump_o``
     - out
     - FRONTEND
     - logic
     - Unconditional jump instruction

   * - ``rvi_imm_o``
     - out
     - FRONTEND
     - logic [riscv::VLEN-1:0]
     - Instruction immediat

   * - ``rvc_branch_o``
     - out
     - FRONTEND
     - logic
     - Branch compressed instruction

   * - ``rvc_jump_o``
     - out
     - FRONTEND
     - logic
     - Unconditional jump compressed instruction

   * - ``rvc_jr_o``
     - out
     - FRONTEND
     - logic
     - JR compressed instruction

   * - ``rvc_return_o``
     - out
     - FRONTEND
     - logic
     - Return compressed instruction

   * - ``rvc_jalr_o``
     - out
     - FRONTEND
     - logic
     - JALR compressed instruction

   * - ``rvc_call_o``
     - out
     - FRONTEND
     - logic
     - JAL compressed instruction

   * - ``rvc_imm_o``
     - out
     - FRONTEND
     - logic [riscv::VLEN-1:0]
     - Instruction compressed immediat
