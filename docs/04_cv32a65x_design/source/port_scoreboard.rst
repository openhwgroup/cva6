..
   Copyright 2024 Thales DIS France SAS
   Licensed under the Solderpad Hardware License, Version 2.1 (the "License");
   you may not use this file except in compliance with the License.
   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
   You may obtain a copy of the License at https://solderpad.org/licenses/

   Original Author: Jean-Roch COULON - Thales

.. _CVA6_scoreboard_ports:

.. list-table:: scoreboard module IO ports
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

   * - ``sb_full_o``
     - out
     - none
     - none
     - logic

   * - ``instructions``
     - in
     - none
     - none
     - logicflush_unissued_instr_i,//flushonlyun-issued

   * - ``scoreboard``
     - in
     - none
     - none
     - logicflush_i,//flushwhole

   * - ``branch``
     - in
     - none
     - none
     - logicunresolved_branch_i,//wehaveanunresolved

   * - ``rd_clobber_gpr_o``
     - out
     - none
     - none
     - ariane_pkg::fu_t[2**ariane_pkg::REG_ADDR_SIZE-1:0]

   * - ``rd_clobber_fpr_o``
     - out
     - none
     - none
     - ariane_pkg::fu_t[2**ariane_pkg::REG_ADDR_SIZE-1:0]

   * - ``rs1_i``
     - in
     - none
     - none
     - logic[ariane_pkg::REG_ADDR_SIZE-1:0]

   * - ``rs1_o``
     - out
     - none
     - none
     - riscv::xlen_t

   * - ``rs1_valid_o``
     - out
     - none
     - none
     - logic

   * - ``rs2_i``
     - in
     - none
     - none
     - logic[ariane_pkg::REG_ADDR_SIZE-1:0]

   * - ``rs2_o``
     - out
     - none
     - none
     - riscv::xlen_t

   * - ``rs2_valid_o``
     - out
     - none
     - none
     - logic

   * - ``rs3_i``
     - in
     - none
     - none
     - logic[ariane_pkg::REG_ADDR_SIZE-1:0]

   * - ``rs3_o``
     - out
     - none
     - none
     - rs3_len_t

   * - ``rs3_valid_o``
     - out
     - none
     - none
     - logic

   * - ``commit_instr_o``
     - out
     - none
     - none
     - ariane_pkg::scoreboard_entry_t[CVA6Cfg.NrCommitPorts-1:0]

   * - ``commit_ack_i``
     - in
     - none
     - none
     - logic[CVA6Cfg.NrCommitPorts-1:0]

   * - ``decoded_instr_i``
     - in
     - none
     - none
     - ariane_pkg::scoreboard_entry_t

   * - ``orig_instr_i``
     - in
     - none
     - none
     - logic[31:0]

   * - ``decoded_instr_valid_i``
     - in
     - none
     - none
     - logic

   * - ``decoded_instr_ack_o``
     - out
     - none
     - none
     - logic

   * - ``issue_instr_o``
     - out
     - none
     - none
     - ariane_pkg::scoreboard_entry_t

   * - ``orig_instr_o``
     - out
     - none
     - none
     - logic[31:0]

   * - ``issue_instr_valid_o``
     - out
     - none
     - none
     - logic

   * - ``issue_ack_i``
     - in
     - none
     - none
     - logic

   * - ``resolved_branch_i``
     - in
     - none
     - none
     - ariane_pkg::bp_resolve_t

   * - ``back``
     - in
     - none
     - none
     - logic[CVA6Cfg.NrWbPorts-1:0][ariane_pkg::TRANS_ID_BITS-1:0]trans_id_i,//transactionIDatwhichtowritetheresult

   * - ``in``
     - in
     - none
     - none
     - logic[CVA6Cfg.NrWbPorts-1:0][riscv::XLEN-1:0]wbdata_i,//writedata

   * - ``exception)``
     - in
     - none
     - none
     - ariane_pkg::exception_t[CVA6Cfg.NrWbPorts-1:0]ex_i,//exceptionfromafunctionalunit(e.g.:ld/st

   * - ``valid``
     - in
     - none
     - none
     - logic[CVA6Cfg.NrWbPorts-1:0]wt_valid_i,//datainis

   * - ``writeback``
     - in
     - none
     - none
     - logicx_we_i,//cvxifwefor

   * - ``rvfi_issue_pointer_o``
     - out
     - none
     - none
     - logic[ariane_pkg::TRANS_ID_BITS-1:0]

   * - ``rvfi_commit_pointer_o``
     - out
     - none
     - none
     - logic[CVA6Cfg.NrCommitPorts-1:0][ariane_pkg::TRANS_ID_BITS-1:0]

Due to cv32a65x configuration, some ports are tied to a static value. These ports do not appear in the above table, they are listed below

none
