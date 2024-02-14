..
   Copyright 2024 Thales DIS France SAS
   Licensed under the Solderpad Hardware License, Version 2.1 (the "License");
   you may not use this file except in compliance with the License.
   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
   You may obtain a copy of the License at https://solderpad.org/licenses/

   Original Author: Jean-Roch COULON - Thales

.. _CVA6_decoder_ports:

.. list-table:: decoder module IO ports
   :header-rows: 1

   * - Signal
     - IO
     - Connection
     - Type
     - Description

   * - ``debug_req_i``
     - in
     - TO_BE_COMPLETED
     - External debug request
     - logic

   * - ``pc_i``
     - in
     - TO_BE_COMPLETED
     - PC from IF
     - logic[riscv::VLEN-1:0]

   * - ``is_compressed_i``
     - in
     - TO_BE_COMPLETED
     - Is a compressed instruction
     - logic

   * - ``compressed_instr_i``
     - in
     - TO_BE_COMPLETED
     - Compressed form of instruction
     - logic[15:0]

   * - ``is_illegal_i``
     - in
     - TO_BE_COMPLETED
     - Illegal compressed instruction
     - logic

   * - ``instruction_i``
     - in
     - TO_BE_COMPLETED
     - Instruction from IF
     - logic[31:0]

   * - ``branch_predict_i``
     - in
     - TO_BE_COMPLETED
     - TO_BE_COMPLETED
     - branchpredict_sbe_t

   * - ``ex_i``
     - in
     - TO_BE_COMPLETED
     - If an exception occured in if
     - exception_t

   * - ``irq_i``
     - in
     - TO_BE_COMPLETED
     - External interrupt
     - logic[1:0]

   * - ``irq_ctrl_i``
     - in
     - TO_BE_COMPLETED
     - Interrupt control and status information from CSRs
     - irq_ctrl_t

   * - ``priv_lvl_i``
     - in
     - CSR_REGFILE
     - Current privilege level
     - riscv::priv_lvl_t

   * - ``debug_mode_i``
     - in
     - CSR_REGFILE
     - We are in debug mode
     - logic

   * - ``fs_i``
     - in
     - CSR_REGFILE
     - Floating point extension status
     - riscv::xs_t

   * - ``frm_i``
     - in
     - CSR_REGFILE
     - Floating-point dynamic rounding mode
     - logic[2:0]

   * - ``vs_i``
     - in
     - CSR_REGFILE
     - Vector extension status
     - riscv::xs_t

   * - ``tvm_i``
     - in
     - CSR_REGFILE
     - Trap virtual memory
     - logic

   * - ``tw_i``
     - in
     - CSR_REGFILE
     - Timeout wait
     - logic

   * - ``tsr_i``
     - in
     - CSR_REGFILE
     - Trap sret
     - logic

   * - ``instruction_o``
     - out
     - COMMIT_STAGE
     - Scoreboard entry to scoreboard
     - scoreboard_entry_t

   * - ``orig_instr_o``
     - out
     - TO_BE_COMPLETED
     - Instruction opcode to issue read operand for CVXIF
     - logic[31:0]

   * - ``is_control_flow_instr_o``
     - out
     - TO_BE_COMPLETED
     - This instruction will change the control flow
     - logic
