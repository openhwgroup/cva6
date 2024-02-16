..
   Copyright 2024 Thales DIS France SAS
   Licensed under the Solderpad Hardware License, Version 2.1 (the "License");
   you may not use this file except in compliance with the License.
   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
   You may obtain a copy of the License at https://solderpad.org/licenses/

   Original Author: Jean-Roch COULON - Thales

.. _CVA6_id_stage_ports:

.. list-table:: id_stage module IO ports
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
     - Fetch flush request
     - CONTROLLER
     - logic

   * - ``fetch_entry_i``
     - in
     - Handshake's data between fetch and decode
     - FRONTEND
     - ariane_pkg::fetch_entry_t

   * - ``fetch_entry_valid_i``
     - in
     - Handshake's valid between fetch and decode
     - FRONTEND
     - logic

   * - ``fetch_entry_ready_o``
     - out
     - Handshake's ready between fetch and decode
     - FRONTEND
     - logic

   * - ``issue_entry_o``
     - out
     - Handshake's data between decode and issue
     - ISSUE
     - ariane_pkg::scoreboard_entry_t

   * - ``orig_instr_o``
     - out
     - Instruction value
     - ISSUE
     - logic[31:0]

   * - ``issue_entry_valid_o``
     - out
     - Handshake's valid between decode and issue
     - ISSUE
     - logic

   * - ``is_ctrl_flow_o``
     - out
     - Report if instruction is a control flow instruction
     - ISSUE
     - logic

   * - ``issue_instr_ack_i``
     - in
     - Handshake's acknowlege between decode and issue
     - ISSUE
     - logic

   * - ``irq_i``
     - in
     - Level sensitive (async) interrupts
     - SUBSYSTEM
     - logic[1:0]

   * - ``irq_ctrl_i``
     - in
     - Interrupt control status
     - CSR_REGFILE
     - ariane_pkg::irq_ctrl_t

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

Due to cv32a65x configuration, some ports are tied to a static value. These ports do not appear in the above table, they are listed below

| As DebugEn = 0,
|   ``debug_req_i`` input is tied to 0
|   ``debug_mode_i`` input is tied to 0
| As IsRVFI = 0,
|   ``rvfi_is_compressed_o`` output is tied to 0
| As PRIV = MachineOnly,
|   ``priv_lvl_i`` input is tied to MachineMode
| As RVF = 0,
|   ``fs_i`` input is tied to 0
|   ``frm_i`` input is tied to 0
| As RVV = 0,
|   ``vs_i`` input is tied to 0
