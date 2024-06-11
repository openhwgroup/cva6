..
   Copyright 2024 Thales DIS France SAS
   Licensed under the Solderpad Hardware License, Version 2.1 (the "License");
   you may not use this file except in compliance with the License.
   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
   You may obtain a copy of the License at https://solderpad.org/licenses/

   Original Author: Jean-Roch COULON - Thales

.. _CVA6_issue_read_operands_ports:

.. list-table:: **issue_read_operands module** IO ports
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

   * - ``flush_i``
     - in
     - Flush
     - CONTROLLER
     - logic

   * - ``issue_instr_i``
     - in
     - TO_BE_COMPLETED
     - TO_BE_COMPLETED
     - scoreboard_entry_t

   * - ``orig_instr_i``
     - in
     - TO_BE_COMPLETED
     - TO_BE_COMPLETED
     - logic[31:0]

   * - ``issue_instr_valid_i``
     - in
     - TO_BE_COMPLETED
     - TO_BE_COMPLETED
     - logic

   * - ``issue_ack_o``
     - out
     - Issue stage acknowledge
     - TO_BE_COMPLETED
     - logic

   * - ``rs1_o``
     - out
     - rs1 operand address
     - scoreboard
     - logic[REG_ADDR_SIZE-1:0]

   * - ``rs1_i``
     - in
     - rs1 operand
     - scoreboard
     - logic[CVA6Cfg.XLEN-1:0]

   * - ``rs1_valid_i``
     - in
     - rs1 operand is valid
     - scoreboard
     - logic

   * - ``rs2_o``
     - out
     - rs2 operand address
     - scoreboard
     - logic[REG_ADDR_SIZE-1:0]

   * - ``rs2_i``
     - in
     - rs2 operand
     - scoreboard
     - logic[CVA6Cfg.XLEN-1:0]

   * - ``rs2_valid_i``
     - in
     - rs2 operand is valid
     - scoreboard
     - logic

   * - ``rs3_o``
     - out
     - rs3 operand address
     - scoreboard
     - logic[REG_ADDR_SIZE-1:0]

   * - ``rs3_i``
     - in
     - rs3 operand
     - scoreboard
     - rs3_len_t

   * - ``rs3_valid_i``
     - in
     - rs3 operand is valid
     - scoreboard
     - logic

   * - ``rd_clobber_gpr_i``
     - in
     - TO_BE_COMPLETED
     - TO_BE_COMPLETED
     - fu_t[2**REG_ADDR_SIZE-1:0]

   * - ``rd_clobber_fpr_i``
     - in
     - TO_BE_COMPLETED
     - TO_BE_COMPLETED
     - fu_t[2**REG_ADDR_SIZE-1:0]

   * - ``fu_data_o``
     - out
     - TO_BE_COMPLETED
     - TO_BE_COMPLETED
     - fu_data_t

   * - ``rs1_forwarding_o``
     - out
     - Unregistered version of fu_data_o.operanda
     - TO_BE_COMPLETED
     - logic[CVA6Cfg.XLEN-1:0]

   * - ``rs2_forwarding_o``
     - out
     - Unregistered version of fu_data_o.operandb
     - TO_BE_COMPLETED
     - logic[CVA6Cfg.XLEN-1:0]

   * - ``pc_o``
     - out
     - Instruction pc
     - TO_BE_COMPLETED
     - logic[CVA6Cfg.VLEN-1:0]

   * - ``is_compressed_instr_o``
     - out
     - Is compressed instruction
     - TO_BE_COMPLETED
     - logic

   * - ``flu_ready_i``
     - in
     - Fixed Latency Unit ready to accept new request
     - TO_BE_COMPLETED
     - logic

   * - ``alu_valid_o``
     - out
     - ALU output is valid
     - TO_BE_COMPLETED
     - logic

   * - ``branch_valid_o``
     - out
     - Branch instruction is valid
     - TO_BE_COMPLETED
     - logic

   * - ``branch_predict_o``
     - out
     - TO_BE_COMPLETED
     - TO_BE_COMPLETED
     - branchpredict_sbe_t

   * - ``lsu_ready_i``
     - in
     - Load Store Unit is ready
     - TO_BE_COMPLETED
     - logic

   * - ``lsu_valid_o``
     - out
     - Load Store Unit result is valid
     - TO_BE_COMPLETED
     - logic

   * - ``mult_valid_o``
     - out
     - Mult result is valid
     - TO_BE_COMPLETED
     - logic

   * - ``csr_valid_o``
     - out
     - CSR result is valid
     - TO_BE_COMPLETED
     - logic

   * - ``cvxif_valid_o``
     - out
     - CVXIF result is valid
     - TO_BE_COMPLETED
     - logic

   * - ``cvxif_ready_i``
     - in
     - CVXIF is ready
     - TO_BE_COMPLETED
     - logic

   * - ``cvxif_off_instr_o``
     - out
     - CVXIF offloaded instruction
     - TO_BE_COMPLETED
     - logic[31:0]

   * - ``waddr_i``
     - in
     - TO_BE_COMPLETED
     - TO_BE_COMPLETED
     - logic[CVA6Cfg.NrCommitPorts-1:0][4:0]

   * - ``wdata_i``
     - in
     - TO_BE_COMPLETED
     - TO_BE_COMPLETED
     - logic[CVA6Cfg.NrCommitPorts-1:0][CVA6Cfg.XLEN-1:0]

   * - ``we_gpr_i``
     - in
     - TO_BE_COMPLETED
     - TO_BE_COMPLETED
     - logic[CVA6Cfg.NrCommitPorts-1:0]

   * - ``stall_issue_o``
     - out
     - Stall signal, we do not want to fetch any more entries
     - TO_BE_COMPLETED
     - logic

Due to cv32a65x configuration, some ports are tied to a static value. These ports do not appear in the above table, they are listed below

| As EnableAccelerator = 0,
|   ``stall_i`` input is tied to 0
| As RVH = False,
|   ``tinst_o`` output is tied to 0
| As RVF = 0,
|   ``fpu_ready_i`` input is tied to 0
|   ``fpu_valid_o`` output is tied to 0
|   ``fpu_fmt_o`` output is tied to 0
|   ``fpu_rm_o`` output is tied to 0
|   ``we_fpr_i`` input is tied to 0

