..
   Copyright 2024 Thales DIS France SAS
   Licensed under the Solderpad Hardware License, Version 2.1 (the "License");
   you may not use this file except in compliance with the License.
   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
   You may obtain a copy of the License at https://solderpad.org/licenses/

   Original Author: Jean-Roch COULON - Thales

.. _CVA6_branch_unit_ports:

.. list-table:: **branch_unit module** IO ports
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

   * - ``fu_data_i``
     - in
     - FU data needed to execute instruction
     - ISSUE_STAGE
     - fu_data_t

   * - ``pc_i``
     - in
     - Instruction PC
     - ISSUE_STAGE
     - logic[CVA6Cfg.VLEN-1:0]

   * - ``is_compressed_instr_i``
     - in
     - Instruction is compressed
     - ISSUE_STAGE
     - logic

   * - ``fu_valid_i``
     - in
     - any functional unit is valid, check that there is no accidental mis-predict
     - TO_BE_COMPLETED
     - logic

   * - ``branch_valid_i``
     - in
     - Branch unit instruction is valid
     - ISSUE_STAGE
     - logic

   * - ``branch_comp_res_i``
     - in
     - ALU branch compare result
     - ALU
     - logic

   * - ``branch_result_o``
     - out
     - Brach unit result
     - ISSUE_STAGE
     - logic[CVA6Cfg.VLEN-1:0]

   * - ``branch_predict_i``
     - in
     - Information of branch prediction
     - ISSUE_STAGE
     - branchpredict_sbe_t

   * - ``resolved_branch_o``
     - out
     - Signaling that we resolved the branch
     - ISSUE_STAGE
     - bp_resolve_t

   * - ``resolve_branch_o``
     - out
     - Branch is resolved, new entries can be accepted by scoreboard
     - ID_STAGE
     - logic

   * - ``branch_exception_o``
     - out
     - Branch exception out
     - TO_BE_COMPLETED
     - exception_t

Due to cv32a65x configuration, some ports are tied to a static value. These ports do not appear in the above table, they are listed below

| As RVH = False,
|   ``v_i`` input is tied to 0
| As DebugEn = False,
|   ``debug_mode_i`` input is tied to 0

