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
     - Description
     - Connection
     - Type

   * - ``debug_req_i``
     - in
     - Debug (async) request
     - SUBSYSTEM
     - logic

   * - ``pc_i``
     - in
     - PC from fetch stage
     - FRONTEND
     - logic[riscv::VLEN-1:0]

   * - ``is_compressed_i``
     - in
     - Is a compressed instruction
     - ID_STAGE
     - logic

   * - ``compressed_instr_i``
     - in
     - Compressed form of instruction
     - FRONTEND
     - logic[15:0]

   * - ``is_illegal_i``
     - in
     - Illegal compressed instruction
     - ID_STAGE
     - logic

   * - ``instruction_i``
     - in
     - Instruction from fetch stage
     - FRONTEND
     - logic[31:0]

   * - ``branch_predict_i``
     - in
     - Is a branch predict instruction
     - ID_STAGE
     - branchpredict_sbe_t

   * - ``ex_i``
     - in
     - If an exception occured in fetch stage
     - FRONTEND
     - exception_t

   * - ``irq_i``
     - in
     - Level sensitive (async) interrupts
     - SUBSYSTEM
     - logic[1:0]

   * - ``irq_ctrl_i``
     - in
     - Interrupt control status
     - CSR_REGFILE
     - irq_ctrl_t

   * - ``priv_lvl_i``
     - in
     - Current privilege level
     - CSR_REGFILE
     - riscv::priv_lvl_t

   * - ``debug_mode_i``
     - in
     - Is debug mode
     - CSR_REGFILE
     - logic

   * - ``fs_i``
     - in
     - Floating point extension status
     - CSR_REGFILE
     - riscv::xs_t

   * - ``frm_i``
     - in
     - Floating-point dynamic rounding mode
     - CSR_REGFILE
     - logic[2:0]

   * - ``vs_i``
     - in
     - Vector extension status
     - CSR_REGFILE
     - riscv::xs_t

   * - ``tvm_i``
     - in
     - Trap virtual memory
     - CSR_REGFILE
     - logic

   * - ``tw_i``
     - in
     - Timeout wait
     - CSR_REGFILE
     - logic

   * - ``tsr_i``
     - in
     - Trap sret
     - CSR_REGFILE
     - logic

   * - ``instruction_o``
     - out
     - Instruction to be added to scoreboard entry
     - ID_STAGE
     - scoreboard_entry_t

   * - ``orig_instr_o``
     - out
     - Instruction
     - ISSUE_STAGE
     - logic[31:0]

   * - ``is_control_flow_instr_o``
     - out
     - Is a control flow instruction
     - ID_STAGE
     - logic
