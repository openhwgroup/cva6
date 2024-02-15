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
     - connexion
     - Type

   * - ``pc_i``
     - in
     - PC from fetch stage
     - FRONTEND
     - logic[riscv::VLEN-1:0]

   * - ``is_compressed_i``
     - in
     - Is a compressed instruction
     - compressed_decoder
     - logic

   * - ``compressed_instr_i``
     - in
     - Compressed form of instruction
     - FRONTEND
     - logic[15:0]

   * - ``is_illegal_i``
     - in
     - Illegal compressed instruction
     - compressed_decoder
     - logic

   * - ``instruction_i``
     - in
     - Instruction from fetch stage
     - FRONTEND
     - logic[31:0]

   * - ``branch_predict_i``
     - in
     - Is a branch predict instruction
     - FRONTEND
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
     - ISSUE_STAGE
     - scoreboard_entry_t

   * - ``orig_instr_o``
     - out
     - Instruction
     - ISSUE_STAGE
     - logic[31:0]

   * - ``is_control_flow_instr_o``
     - out
     - Is a control flow instruction
     - ISSUE_STAGE
     - logic

| As debug is disabled,
|   ``debug_req_i`` input is tied to zero
|   ``debug_mode_i`` input is tied to zero
| As privilege mode is machine mode only,
|   ``priv_lvl_i`` input is tied to Machine mode
| As FPU is not present,
|   ``fs_i`` input is tied to zero
|   ``frm_i`` input is tied to zero
| As vector extension is not present,
|   ``vs_i`` input is tied to zero
