..
   Copyright 2024 Thales DIS France SAS
   Licensed under the Solderpad Hardware License, Version 2.1 (the "License");
   you may not use this file except in compliance with the License.
   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
   You may obtain a copy of the License at https://solderpad.org/licenses/

   Original Author: Jean-Roch COULON - Thales

.. _CVA6_issue_stage_ports:

.. list-table:: issue_stage module IO ports
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

   * - ``flush_unissued_instr_i``
     - in
     - TO_BE_COMPLETED
     - CONTROLLER
     - logic

   * - ``flush_i``
     - in
     - TO_BE_COMPLETED
     - CONTROLLER
     - logic

   * - ``decoded_instr_i``
     - in
     - Handshake's data with decode stage
     - ID_STAGE
     - scoreboard_entry_t

   * - ``orig_instr_i``
     - in
     - instruction value
     - ID_STAGE
     - logic[31:0]

   * - ``decoded_instr_valid_i``
     - in
     - Handshake's valid with decode stage
     - ID_STAGE
     - logic

   * - ``is_ctrl_flow_i``
     - in
     - Is instruction a control flow instruction
     - ID_STAGE
     - logic

   * - ``decoded_instr_ack_o``
     - out
     - Handshake's acknowlege with decode stage
     - ID_STAGE
     - logic

   * - ``rs1_forwarding_o``
     - out
     - rs1 forwarding
     - EX_STAGE
     - [riscv::VLEN-1:0]

   * - ``rs2_forwarding_o``
     - out
     - rs2 forwarding
     - EX_STAGE
     - [riscv::VLEN-1:0]

   * - ``fu_data_o``
     - out
     - TO_BE_COMPLETED
     - EX_STAGE
     - fu_data_t

   * - ``pc_o``
     - out
     - TO_BE_COMPLETED
     - EX_STAGE
     - logic[riscv::VLEN-1:0]

   * - ``is_compressed_instr_o``
     - out
     - Is compressed instruction
     - EX_STAGE
     - logic

   * - ``flu_ready_i``
     - in
     - TO_BE_COMPLETED
     - EX_STAGE
     - logic

   * - ``alu_valid_o``
     - out
     - ALU FU is valid
     - EX_STAGE
     - logic

   * - ``resolve_branch_i``
     - in
     - TO_BE_COMPLETED
     - EX_STAGE
     - logic

   * - ``lsu_ready_i``
     - in
     - Load store unit FU is ready
     - EX_STAGE
     - logic

   * - ``lsu_valid_o``
     - out
     - Load store unit FU is valid
     - EX_STAGE
     - logic

   * - ``branch_valid_o``
     - out
     - Branch unit is valid
     - EX_STAGE
     - logic

   * - ``branch_predict_o``
     - out
     - TO_BE_COMPLETED
     - EX_STAGE
     - branchpredict_sbe_t

   * - ``mult_valid_o``
     - out
     - Mult FU is valid
     - EX_STAGE
     - logic

   * - ``fpu_ready_i``
     - in
     - FPU FU is ready
     - EX_STAGE
     - logic

   * - ``csr_valid_o``
     - out
     - CSR is valid
     - EX_STAGE
     - logic

   * - ``x_issue_valid_o``
     - out
     - CVXIF FU is valid
     - EX_STAGE
     - logic

   * - ``x_issue_ready_i``
     - in
     - CVXIF is FU ready
     - EX_STAGE
     - logic

   * - ``x_off_instr_o``
     - out
     - CVXIF offloader instruction value
     - EX_STAGE
     - logic[31:0]

   * - ``trans_id_i``
     - in
     - TO_BE_COMPLETED
     - EX_STAGE
     - logic[CVA6Cfg.NrWbPorts-1:0][TRANS_ID_BITS-1:0]

   * - ``resolved_branch_i``
     - in
     - TO_BE_COMPLETED
     - EX_STAGE
     - bp_resolve_t

   * - ``wbdata_i``
     - in
     - TO_BE_COMPLETED
     - EX_STAGE
     - logic[CVA6Cfg.NrWbPorts-1:0][riscv::XLEN-1:0]

   * - ``ex_ex_i``
     - in
     - exception from execute stage or CVXIF
     - EX_STAGE
     - exception_t[CVA6Cfg.NrWbPorts-1:0]

   * - ``wt_valid_i``
     - in
     - TO_BE_COMPLETED
     - EX_STAGE
     - logic[CVA6Cfg.NrWbPorts-1:0]

   * - ``x_we_i``
     - in
     - TO_BE_COMPLETED
     - EX_STAGE
     - logic

   * - ``waddr_i``
     - in
     - TO_BE_COMPLETED
     - EX_STAGE
     - logic[CVA6Cfg.NrCommitPorts-1:0][4:0]

   * - ``wdata_i``
     - in
     - TO_BE_COMPLETED
     - EX_STAGE
     - logic[CVA6Cfg.NrCommitPorts-1:0][riscv::XLEN-1:0]

   * - ``we_gpr_i``
     - in
     - TO_BE_COMPLETED
     - EX_STAGE
     - logic[CVA6Cfg.NrCommitPorts-1:0]

   * - ``we_fpr_i``
     - in
     - TO_BE_COMPLETED
     - EX_STAGE
     - logic[CVA6Cfg.NrCommitPorts-1:0]

   * - ``commit_instr_o``
     - out
     - TO_BE_COMPLETED
     - COMMIT_STAGE
     - scoreboard_entry_t[CVA6Cfg.NrCommitPorts-1:0]

   * - ``commit_ack_i``
     - in
     - TO_BE_COMPLETED
     - COMMIT_STAGE
     - logic[CVA6Cfg.NrCommitPorts-1:0]

| As performance counters are not supported,
|   ``sb_full_o`` output is tied to zero
|   ``stall_issue_o`` output is tied to zero
| As Accelerate port is not supported,
|   ``stall_i`` input is tied to zero
|   ``issue_instr_o`` output is tied to zero
|   ``issue_instr_hs_o`` output is tied to zero
| As FPU is not present,
|   ``fpu_valid_o`` output is tied to zero
|   ``fpu_fmt_o`` output is tied to zero
|   ``fpu_rm_o`` output is tied to zero
| As RVFI is not implemented,
|   ``rvfi_issue_pointer_o`` output is tied to zero
|   ``rvfi_commit_pointer_o`` output is tied to zero
