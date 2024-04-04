..
   Copyright 2024 Thales DIS France SAS
   Licensed under the Solderpad Hardware License, Version 2.1 (the "License");
   you may not use this file except in compliance with the License.
   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
   You may obtain a copy of the License at https://solderpad.org/licenses/

   Original Author: Jean-Roch COULON - Thales

.. _CVA6_decoder_ports:

.. list-table:: **decoder module** IO ports
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
     - logic[CVA6Cfg.VLEN-1:0]

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

   * - ``is_macro_instr_i``
     - in
     - Is a macro instruction
     - macro_decoder
     - logic

   * - ``is_last_macro_instr_i``
     - in
     - Is a last macro instruction
     - macro_decoder
     - logic

   * - ``is_double_rd_macro_instr_i``
     - in
     - Is mvsa01/mva01s macro instruction
     - macro_decoder
     - logic

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

Due to cv32a65x configuration, some ports are tied to a static value. These ports do not appear in the above table, they are listed below

| As DebugEn = False,
|   ``debug_req_i`` input is tied to 0
|   ``debug_mode_i`` input is tied to 0
| As PRIV = MachineOnly,
|   ``priv_lvl_i`` input is tied to MachineMode
|   ``tvm_i`` input is tied to 0
|   ``tw_i`` input is tied to 0
|   ``tsr_i`` input is tied to 0
| As RVH = False,
|   ``v_i`` input is tied to 0
|   ``vfs_i`` input is tied to 0
|   ``vtw_i`` input is tied to 0
|   ``hu_i`` input is tied to 0
| As RVF = 0,
|   ``fs_i`` input is tied to 0
|   ``frm_i`` input is tied to 0
| As RVV = False,
|   ``vs_i`` input is tied to 0

