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
     - Subsystem Clock
     - logic

   * - ``rst_ni``
     - in
     - Asynchronous reset active low
     - SUBSYSTEM
     - Asynchronous reset active low
     - logic

   * - ``sb_full_o``
     - out
     - PERF_COUNTERS
     - TO_BE_COMPLETED
     - logic

   * - ``flush_unissued_instr_i``
     - in
     - TO_BE_COMPLETED
     - CONTROLLER
     - TO_BE_COMPLETED
     - logic

   * - ``flush_i``
     - in
     - TO_BE_COMPLETED
     - CONTROLLER
     - TO_BE_COMPLETED
     - logic

   * - ``stall_i``
     - in
     - ACC_DISPATCHER
     - zero when accelerate port is disable
     - logic

   * - ``decoded_instr_i``
     - in
     - Handshake's data with decode stage
     - ID_STAGE
     - Handshake's data between decode and issue
     - scoreboard_entry_t

   * - ``orig_instr_i``
     - in
     - instruction value
     - ID_STAGE
     - instruction value
     - logic[31:0]

   * - ``decoded_instr_valid_i``
     - in
     - Handshake's valid with decode stage
     - ID_STAGE
     - Handshake's valid between decode and issue
     - logic

   * - ``is_ctrl_flow_i``
     - in
     - Is instruction a control flow instruction
     - ID_STAGE
     - Report if instruction is a control flow instruction
     - logic

   * - ``decoded_instr_ack_o``
     - out
     - Handshake's acknowlege with decode stage
     - ID_STAGE
     - Handshake's acknowlege between decode and issue
     - logic

   * - ``rs1_forwarding_o``
     - out
     - rs1 forwarding
     - EX_STAGE
     - TO_BE_COMPLETED
     - [riscv::VLEN-1:0]

   * - ``rs2_forwarding_o``
     - out
     - rs2 forwarding
     - EX_STAGE
     - TO_BE_COMPLETED
     - [riscv::VLEN-1:0]

   * - ``fu_data_o``
     - out
     - FU data useful to execute instruction
     - EX_STAGE
     - TO_BE_COMPLETED
     - fu_data_t

   * - ``pc_o``
     - out
     - TO_BE_COMPLETED
     - EX_STAGE
     - TO_BE_COMPLETED
     - logic[riscv::VLEN-1:0]

   * - ``is_compressed_instr_o``
     - out
     - Is compressed instruction
     - EX_STAGE
     - TO_BE_COMPLETED
     - logic

   * - ``flu_ready_i``
     - in
     - TO_BE_COMPLETED
     - EX_STAGE
     - TO_BE_COMPLETED
     - logic

   * - ``alu_valid_o``
     - out
     - ALU FU is valid
     - EX_STAGE
     - TO_BE_COMPLETED
     - logic

   * - ``resolve_branch_i``
     - in
     - TO_BE_COMPLETED
     - EX_STAGE
     - TO_BE_COMPLETED
     - logic

   * - ``lsu_ready_i``
     - in
     - Load store unit FU is ready
     - EX_STAGE
     - TO_BE_COMPLETED
     - logic

   * - ``lsu_valid_o``
     - out
     - Load store unit FU is valid
     - EX_STAGE
     - TO_BE_COMPLETED
     - logic

   * - ``branch_valid_o``
     - out
     - Branch unit is valid
     - EX_STAGE
     - TO_BE_COMPLETED
     - logic

   * - ``branch_predict_o``
     - out
     - Information of branch prediction
     - EX_STAGE
     - TO_BE_COMPLETED
     - branchpredict_sbe_t

   * - ``mult_valid_o``
     - out
     - Mult FU is valid
     - EX_STAGE
     - TO_BE_COMPLETED
     - logic

   * - ``fpu_ready_i``
     - in
     - FPU FU is ready
     - EX_STAGE
     - TO_BE_COMPLETED
     - logic

   * - ``fpu_valid_o``
     - out
     - EX_STAGE
     - TO_BE_COMPLETED
     - logic

   * - ``fpu_fmt_o``
     - out
     - EX_STAGE
     - Report FP fmt field
     - logic[1:0]

   * - ``fpu_rm_o``
     - out
     - EX_STAGE
     - report FP rm field
     - logic[2:0]

   * - ``csr_valid_o``
     - out
     - CSR is valid
     - EX_STAGE
     - TO_BE_COMPLETED
     - logic

   * - ``x_issue_valid_o``
     - out
     - CVXIF FU is valid
     - EX_STAGE
     - TO_BE_COMPLETED
     - logic

   * - ``x_issue_ready_i``
     - in
     - CVXIF is FU ready
     - EX_STAGE
     - TO_BE_COMPLETED
     - logic

   * - ``x_off_instr_o``
     - out
     - CVXIF offloader instruction value
     - EX_STAGE
     - TO_BE_COMPLETED
     - logic[31:0]

   * - ``issue_instr_o``
     - out
     - ACC_DISPATCHER
     - TO_BE_COMPLETED
     - scoreboard_entry_t

   * - ``issue_instr_hs_o``
     - out
     - ACC_DISPATCHER
     - TO_BE_COMPLETED
     - logic

   * - ``trans_id_i``
     - in
     - TO_BE_COMPLETED
     - EX_STAGE
     - TO_BE_COMPLETED
     - logic[CVA6Cfg.NrWbPorts-1:0][TRANS_ID_BITS-1:0]

   * - ``resolved_branch_i``
     - in
     - TO_BE_COMPLETED
     - EX_STAGE
     - TO_BE_COMPLETED
     - bp_resolve_t

   * - ``wbdata_i``
     - in
     - TO_BE_COMPLETED
     - EX_STAGE
     - TO_BE_COMPLETED
     - logic[CVA6Cfg.NrWbPorts-1:0][riscv::XLEN-1:0]

   * - ``ex_ex_i``
     - in
     - exception from execute stage or CVXIF
     - EX_STAGE
     - exception from execute stage or CVXIF offloaded instruction
     - exception_t[CVA6Cfg.NrWbPorts-1:0]

   * - ``wt_valid_i``
     - in
     - TO_BE_COMPLETED
     - EX_STAGE
     - TO_BE_COMPLETED
     - logic[CVA6Cfg.NrWbPorts-1:0]

   * - ``x_we_i``
     - in
     - TO_BE_COMPLETED
     - EX_STAGE
     - TO_BE_COMPLETED
     - logic

   * - ``waddr_i``
     - in
     - TO_BE_COMPLETED
     - EX_STAGE
     - TO_BE_COMPLETED
     - logic[CVA6Cfg.NrCommitPorts-1:0][4:0]

   * - ``wdata_i``
     - in
     - TO_BE_COMPLETED
     - EX_STAGE
     - TO_BE_COMPLETED
     - logic[CVA6Cfg.NrCommitPorts-1:0][riscv::XLEN-1:0]

   * - ``we_gpr_i``
     - in
     - TO_BE_COMPLETED
     - EX_STAGE
     - TO_BE_COMPLETED
     - logic[CVA6Cfg.NrCommitPorts-1:0]

   * - ``we_fpr_i``
     - in
     - TO_BE_COMPLETED
     - EX_STAGE
     - TO_BE_COMPLETED
     - logic[CVA6Cfg.NrCommitPorts-1:0]

   * - ``commit_instr_o``
     - out
     - TO_BE_COMPLETED
     - COMMIT_STAGE
     - TO_BE_COMPLETED
     - scoreboard_entry_t[CVA6Cfg.NrCommitPorts-1:0]

   * - ``commit_ack_i``
     - in
     - TO_BE_COMPLETED
     - COMMIT_STAGE
     - TO_BE_COMPLETED
     - logic[CVA6Cfg.NrCommitPorts-1:0]

   * - ``stall_issue_o``
     - out
     - PERF_COUNTERS
     - Issue stall
     - logic

   * - ``rvfi_issue_pointer_o``
     - out
     - SUBSYSTEM
     - Information dedicated to RVFI
     - logic[TRANS_ID_BITS-1:0]

   * - ``rvfi_commit_pointer_o``
     - out
     - SUBSYSTEM
     - Information dedicated to RVFI
     - logic[CVA6Cfg.NrCommitPorts-1:0][TRANS_ID_BITS-1:0]
