..
   Copyright 2024 Thales DIS France SAS
   Licensed under the Solderpad Hardware License, Version 2.1 (the "License");
   you may not use this file except in compliance with the License.
   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
   You may obtain a copy of the License at https://solderpad.org/licenses/

   Original Author: Jean-Roch COULON - Thales

.. _CVA6_scoreboard_ports:

.. list-table:: **scoreboard module** IO ports
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

   * - ``sb_full_o``
     - out
     - TO_BE_COMPLETED
     - TO_BE_COMPLETED
     - logic

   * - ``flush_unissued_instr_i``
     - in
     - Flush only un-issued instructions
     - TO_BE_COMPLETED
     - logic

   * - ``flush_i``
     - in
     - Flush whole scoreboard
     - TO_BE_COMPLETED
     - logic

   * - ``rd_clobber_gpr_o``
     - out
     - TO_BE_COMPLETED
     - TO_BE_COMPLETED
     - ariane_pkg::fu_t[2**ariane_pkg::REG_ADDR_SIZE-1:0]

   * - ``rd_clobber_fpr_o``
     - out
     - TO_BE_COMPLETED
     - TO_BE_COMPLETED
     - ariane_pkg::fu_t[2**ariane_pkg::REG_ADDR_SIZE-1:0]

   * - ``rs1_i``
     - in
     - rs1 operand address
     - issue_read_operands
     - logic[ariane_pkg::REG_ADDR_SIZE-1:0]

   * - ``rs1_o``
     - out
     - rs1 operand
     - issue_read_operands
     - logic[CVA6Cfg.XLEN-1:0]

   * - ``rs1_valid_o``
     - out
     - rs1 operand is valid
     - issue_read_operands
     - logic

   * - ``rs2_i``
     - in
     - rs2 operand address
     - issue_read_operands
     - logic[ariane_pkg::REG_ADDR_SIZE-1:0]

   * - ``rs2_o``
     - out
     - rs2 operand
     - issue_read_operands
     - logic[CVA6Cfg.XLEN-1:0]

   * - ``rs2_valid_o``
     - out
     - rs2 operand is valid
     - issue_read_operands
     - logic

   * - ``rs3_i``
     - in
     - rs3 operand address
     - issue_read_operands
     - logic[ariane_pkg::REG_ADDR_SIZE-1:0]

   * - ``rs3_o``
     - out
     - rs3 operand
     - issue_read_operands
     - rs3_len_t

   * - ``rs3_valid_o``
     - out
     - rs3 operand is valid
     - issue_read_operands
     - logic

   * - ``commit_instr_o``
     - out
     - TO_BE_COMPLETED
     - TO_BE_COMPLETED
     - scoreboard_entry_t[CVA6Cfg.NrCommitPorts-1:0]

   * - ``commit_ack_i``
     - in
     - TO_BE_COMPLETED
     - TO_BE_COMPLETED
     - logic[CVA6Cfg.NrCommitPorts-1:0]

   * - ``decoded_instr_i``
     - in
     - TO_BE_COMPLETED
     - TO_BE_COMPLETED
     - scoreboard_entry_t[ariane_pkg::SUPERSCALAR:0]

   * - ``orig_instr_i``
     - in
     - TO_BE_COMPLETED
     - TO_BE_COMPLETED
     - logic[ariane_pkg::SUPERSCALAR:0][31:0]

   * - ``decoded_instr_valid_i``
     - in
     - TO_BE_COMPLETED
     - TO_BE_COMPLETED
     - logic[ariane_pkg::SUPERSCALAR:0]

   * - ``decoded_instr_ack_o``
     - out
     - TO_BE_COMPLETED
     - TO_BE_COMPLETED
     - logic[ariane_pkg::SUPERSCALAR:0]

   * - ``orig_instr_o``
     - out
     - TO_BE_COMPLETED
     - TO_BE_COMPLETED
     - logic[ariane_pkg::SUPERSCALAR:0][31:0]

   * - ``issue_instr_valid_o``
     - out
     - TO_BE_COMPLETED
     - TO_BE_COMPLETED
     - logic[ariane_pkg::SUPERSCALAR:0]

   * - ``issue_ack_i``
     - in
     - TO_BE_COMPLETED
     - TO_BE_COMPLETED
     - logic[ariane_pkg::SUPERSCALAR:0]

   * - ``resolved_branch_i``
     - in
     - TO_BE_COMPLETED
     - TO_BE_COMPLETED
     - bp_resolve_t

   * - ``trans_id_i``
     - in
     - Transaction ID at which to write the result back
     - TO_BE_COMPLETED
     - logic[CVA6Cfg.NrWbPorts-1:0][CVA6Cfg.TRANS_ID_BITS-1:0]

   * - ``wbdata_i``
     - in
     - Results to write back
     - TO_BE_COMPLETED
     - logic[CVA6Cfg.NrWbPorts-1:0][CVA6Cfg.XLEN-1:0]

   * - ``ex_i``
     - in
     - Exception from a functional unit (e.g.: ld/st exception)
     - TO_BE_COMPLETED
     - exception_t[CVA6Cfg.NrWbPorts-1:0]

   * - ``wt_valid_i``
     - in
     - Indicates valid results
     - TO_BE_COMPLETED
     - logic[CVA6Cfg.NrWbPorts-1:0]

   * - ``x_we_i``
     - in
     - Cvxif we for writeback
     - TO_BE_COMPLETED
     - logic

Due to cv32a65x configuration, some ports are tied to a static value. These ports do not appear in the above table, they are listed below

| As EnableAccelerator = 0,
|   ``issue_instr_o`` output is tied to 0
| As IsRVFI = 0,
|   ``rvfi_issue_pointer_o`` output is tied to 0
|   ``rvfi_commit_pointer_o`` output is tied to 0

