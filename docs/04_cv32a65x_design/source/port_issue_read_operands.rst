..
   Copyright 2024 Thales DIS France SAS
   Licensed under the Solderpad Hardware License, Version 2.1 (the "License");
   you may not use this file except in compliance with the License.
   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
   You may obtain a copy of the License at https://solderpad.org/licenses/

   Original Author: Jean-Roch COULON - Thales

.. _CVA6_issue_read_operands_ports:

.. list-table:: issue_read_operands module IO ports
   :header-rows: 1

   * - Signal
     - IO
     - Description
     - connexion
     - Type

   * - ``Clock``
     - in
     - none
     - none
     - logicclk_i,//

   * - ``low``
     - in
     - none
     - none
     - logicrst_ni,//Asynchronousresetactive

   * - ``flush_i``
     - in
     - none
     - none
     - logic

   * - ``stall_i``
     - in
     - none
     - none
     - logic

   * - ``issue_instr_i``
     - in
     - none
     - none
     - scoreboard_entry_t

   * - ``orig_instr_i``
     - in
     - none
     - none
     - logic[31:0]

   * - ``issue_instr_valid_i``
     - in
     - none
     - none
     - logic

   * - ``issue_ack_o``
     - out
     - none
     - none
     - logic

   * - ``rs1_o``
     - out
     - none
     - none
     - logic[REG_ADDR_SIZE-1:0]

   * - ``rs1_i``
     - in
     - none
     - none
     - riscv::xlen_t

   * - ``rs1_valid_i``
     - in
     - none
     - none
     - logic

   * - ``rs2_o``
     - out
     - none
     - none
     - logic[REG_ADDR_SIZE-1:0]

   * - ``rs2_i``
     - in
     - none
     - none
     - riscv::xlen_t

   * - ``rs2_valid_i``
     - in
     - none
     - none
     - logic

   * - ``rs3_o``
     - out
     - none
     - none
     - logic[REG_ADDR_SIZE-1:0]

   * - ``rs3_i``
     - in
     - none
     - none
     - rs3_len_t

   * - ``rs3_valid_i``
     - in
     - none
     - none
     - logic

   * - ``rd_clobber_gpr_i``
     - in
     - none
     - none
     - fu_t[2**REG_ADDR_SIZE-1:0]

   * - ``rd_clobber_fpr_i``
     - in
     - none
     - none
     - fu_t[2**REG_ADDR_SIZE-1:0]

   * - ``fu_data_o``
     - out
     - none
     - none
     - fu_data_t

   * - ``fu_data_o.operanda``
     - out
     - none
     - none
     - riscv::xlen_trs1_forwarding_o,//unregisteredversionof

   * - ``fu_data_o.operandb``
     - out
     - none
     - none
     - riscv::xlen_trs2_forwarding_o,//unregisteredversionof

   * - ``pc_o``
     - out
     - none
     - none
     - logic[riscv::VLEN-1:0]

   * - ``is_compressed_instr_o``
     - out
     - none
     - none
     - logic

   * - ``request``
     - in
     - none
     - none
     - logicflu_ready_i,//Fixedlatencyunitreadytoacceptanew

   * - ``valid``
     - out
     - none
     - none
     - logicalu_valid_o,//Outputis

   * - ``instruction``
     - out
     - none
     - none
     - logicbranch_valid_o,//thisisavalidbranch

   * - ``branch_predict_o``
     - out
     - none
     - none
     - branchpredict_sbe_t

   * - ``ready``
     - in
     - none
     - none
     - logiclsu_ready_i,//FUis

   * - ``valid``
     - out
     - none
     - none
     - logiclsu_valid_o,//Outputis

   * - ``valid``
     - out
     - none
     - none
     - logicmult_valid_o,//Outputis

   * - ``ready``
     - in
     - none
     - none
     - logicfpu_ready_i,//FUis

   * - ``valid``
     - out
     - none
     - none
     - logicfpu_valid_o,//Outputis

   * - ``instr.``
     - out
     - none
     - none
     - logic[1:0]fpu_fmt_o,//FPfmtfieldfrom

   * - ``instr.``
     - out
     - none
     - none
     - logic[2:0]fpu_rm_o,//FPrmfieldfrom

   * - ``valid``
     - out
     - none
     - none
     - logiccsr_valid_o,//Outputis

   * - ``cvxif_valid_o``
     - out
     - none
     - none
     - logic

   * - ``cvxif_ready_i``
     - in
     - none
     - none
     - logic

   * - ``cvxif_off_instr_o``
     - out
     - none
     - none
     - logic[31:0]

   * - ``waddr_i``
     - in
     - none
     - none
     - logic[CVA6Cfg.NrCommitPorts-1:0][4:0]

   * - ``wdata_i``
     - in
     - none
     - none
     - logic[CVA6Cfg.NrCommitPorts-1:0][riscv::XLEN-1:0]

   * - ``we_gpr_i``
     - in
     - none
     - none
     - logic[CVA6Cfg.NrCommitPorts-1:0]

   * - ``we_fpr_i``
     - in
     - none
     - none
     - logic[CVA6Cfg.NrCommitPorts-1:0]

   * - ``entries``
     - out
     - none
     - none
     - logicstall_issue_o//stallsignal,wedonotwanttofetchanymore

