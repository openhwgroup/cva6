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
     - Connection
     - Type
     - Description

   * - ``clk_i``
     - in
     - SUBSYSTEM
     - logic
     - Subsystem Clock

   * - ``rst_ni``
     - in
     - SUBSYSTEM
     - logic
     - Asynchronous reset active low

   * - ``sb_full_o``
     - out
     - PERF_COUNTERS
     - logic
     - TO_BE_COMPLETED

   * - ``flush_unissued_instr_i``
     - in
     - CONTROLLER
     - logic
     - TO_BE_COMPLETED

   * - ``flush_i``
     - in
     - CONTROLLER
     - logic
     - TO_BE_COMPLETED

   * - ``stall_i``
     - in
     - ACC_DISPATCHER
     - logic
     - zero when accelerate port is disable

   * - ``decoded_instr_i``
     - in
     - ID_STAGE
     - scoreboard_entry_t
     - Handshake's data between decode and issue

   * - ``orig_instr_i``
     - in
     - ID_STAGE
     - logic[31:0]
     - instruction value

   * - ``decoded_instr_valid_i``
     - in
     - ID_STAGE
     - logic
     - Handshake's valid between decode and issue

   * - ``is_ctrl_flow_i``
     - in
     - ID_STAGE
     - logic
     - Report if instruction is a control flow instruction

   * - ``decoded_instr_ack_o``
     - out
     - ID_STAGE
     - logic
     - Handshake's acknowlege between decode and issue

   * - ``rs1_forwarding_o``
     - out
     - EX_STAGE
     - [riscv::VLEN-1:0]
     - TO_BE_COMPLETED

   * - ``rs2_forwarding_o``
     - out
     - EX_STAGE
     - [riscv::VLEN-1:0]
     - TO_BE_COMPLETED

   * - ``fu_data_o``
     - out
     - EX_STAGE
     - fu_data_t
     - TO_BE_COMPLETED

   * - ``pc_o``
     - out
     - EX_STAGE
     - logic[riscv::VLEN-1:0]
     - TO_BE_COMPLETED

   * - ``is_compressed_instr_o``
     - out
     - EX_STAGE
     - logic
     - TO_BE_COMPLETED

   * - ``flu_ready_i``
     - in
     - EX_STAGE
     - logic
     - TO_BE_COMPLETED

   * - ``alu_valid_o``
     - out
     - EX_STAGE
     - logic
     - TO_BE_COMPLETED

   * - ``resolve_branch_i``
     - in
     - EX_STAGE
     - logic
     - TO_BE_COMPLETED

   * - ``lsu_ready_i``
     - in
     - EX_STAGE
     - logic
     - TO_BE_COMPLETED

   * - ``lsu_valid_o``
     - out
     - EX_STAGE
     - logic
     - TO_BE_COMPLETED

   * - ``branch_valid_o``
     - out
     - EX_STAGE
     - logic
     - TO_BE_COMPLETED

   * - ``branch_predict_o``
     - out
     - EX_STAGE
     - branchpredict_sbe_t
     - TO_BE_COMPLETED

   * - ``mult_valid_o``
     - out
     - EX_STAGE
     - logic
     - TO_BE_COMPLETED

   * - ``fpu_ready_i``
     - in
     - EX_STAGE
     - logic
     - TO_BE_COMPLETED

   * - ``fpu_valid_o``
     - out
     - EX_STAGE
     - logic
     - TO_BE_COMPLETED

   * - ``fpu_fmt_o``
     - out
     - EX_STAGE
     - logic[1:0]
     - Report FP fmt field

   * - ``fpu_rm_o``
     - out
     - EX_STAGE
     - logic[2:0]
     - report FP rm field

   * - ``csr_valid_o``
     - out
     - EX_STAGE
     - logic
     - TO_BE_COMPLETED

   * - ``x_issue_valid_o``
     - out
     - EX_STAGE
     - logic
     - TO_BE_COMPLETED

   * - ``x_issue_ready_i``
     - in
     - EX_STAGE
     - logic
     - TO_BE_COMPLETED

   * - ``x_off_instr_o``
     - out
     - EX_STAGE
     - logic[31:0]
     - TO_BE_COMPLETED

   * - ``issue_instr_o``
     - out
     - ACC_DISPATCHER
     - scoreboard_entry_t
     - TO_BE_COMPLETED

   * - ``issue_instr_hs_o``
     - out
     - ACC_DISPATCHER
     - logic
     - TO_BE_COMPLETED

   * - ``trans_id_i``
     - in
     - EX_STAGE
     - logic[CVA6Cfg.NrWbPorts-1:0][TRANS_ID_BITS-1:0]
     - TO_BE_COMPLETED

   * - ``resolved_branch_i``
     - in
     - EX_STAGE
     - bp_resolve_t
     - TO_BE_COMPLETED

   * - ``wbdata_i``
     - in
     - EX_STAGE
     - logic[CVA6Cfg.NrWbPorts-1:0][riscv::XLEN-1:0]
     - TO_BE_COMPLETED

   * - ``ex_ex_i``
     - in
     - EX_STAGE
     - exception_t[CVA6Cfg.NrWbPorts-1:0]
     - exception from execute stage or CVXIF offloaded instruction

   * - ``wt_valid_i``
     - in
     - EX_STAGE
     - logic[CVA6Cfg.NrWbPorts-1:0]
     - TO_BE_COMPLETED

   * - ``x_we_i``
     - in
     - EX_STAGE
     - logic
     - TO_BE_COMPLETED

   * - ``waddr_i``
     - in
     - EX_STAGE
     - logic[CVA6Cfg.NrCommitPorts-1:0][4:0]
     - TO_BE_COMPLETED

   * - ``wdata_i``
     - in
     - EX_STAGE
     - logic[CVA6Cfg.NrCommitPorts-1:0][riscv::XLEN-1:0]
     - TO_BE_COMPLETED

   * - ``we_gpr_i``
     - in
     - EX_STAGE
     - logic[CVA6Cfg.NrCommitPorts-1:0]
     - TO_BE_COMPLETED

   * - ``we_fpr_i``
     - in
     - EX_STAGE
     - logic[CVA6Cfg.NrCommitPorts-1:0]
     - TO_BE_COMPLETED

   * - ``commit_instr_o``
     - out
     - COMMIT_STAGE
     - scoreboard_entry_t[CVA6Cfg.NrCommitPorts-1:0]
     - TO_BE_COMPLETED

   * - ``commit_ack_i``
     - in
     - COMMIT_STAGE
     - logic[CVA6Cfg.NrCommitPorts-1:0]
     - TO_BE_COMPLETED

   * - ``stall_issue_o``
     - out
     - PERF_COUNTERS
     - logic
     - Issue stall

   * - ``rvfi_issue_pointer_o``
     - out
     - SUBSYSTEM
     - logic[TRANS_ID_BITS-1:0]
     - Information dedicated to RVFI

   * - ``rvfi_commit_pointer_o``
     - out
     - SUBSYSTEM
     - logic[CVA6Cfg.NrCommitPorts-1:0][TRANS_ID_BITS-1:0]
     - Information dedicated to RVFI
