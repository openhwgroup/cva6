..
   Copyright 2024 Thales DIS France SAS
   Licensed under the Solderpad Hardware License, Version 2.1 (the "License");
   you may not use this file except in compliance with the License.
   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
   You may obtain a copy of the License at https://solderpad.org/licenses/

   Original Author: Jean-Roch COULON - Thales

.. _CVA6_id_stage_ports:

.. list-table:: **id_stage module** IO ports
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
     - fetch_entry_t[ariane_pkg::SUPERSCALAR:0]

   * - ``fetch_entry_valid_i``
     - in
     - Handshake's valid between fetch and decode
     - FRONTEND
     - logic[ariane_pkg::SUPERSCALAR:0]

   * - ``fetch_entry_ready_o``
     - out
     - Handshake's ready between fetch and decode
     - FRONTEND
     - logic[ariane_pkg::SUPERSCALAR:0]

   * - ``issue_entry_o``
     - out
     - Handshake's data between decode and issue
     - ISSUE
     - scoreboard_entry_t[ariane_pkg::SUPERSCALAR:0]

   * - ``orig_instr_o``
     - out
     - Instruction value
     - ISSUE
     - logic[ariane_pkg::SUPERSCALAR:0][31:0]

   * - ``issue_entry_valid_o``
     - out
     - Handshake's valid between decode and issue
     - ISSUE
     - logic[ariane_pkg::SUPERSCALAR:0]

   * - ``is_ctrl_flow_o``
     - out
     - Report if instruction is a control flow instruction
     - ISSUE
     - logic[ariane_pkg::SUPERSCALAR:0]

   * - ``issue_instr_ack_i``
     - in
     - Handshake's acknowlege between decode and issue
     - ISSUE
     - logic[ariane_pkg::SUPERSCALAR:0]

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

Due to cv32a65x configuration, some ports are tied to a static value. These ports do not appear in the above table, they are listed below

| As DebugEn = False,
|   ``debug_req_i`` input is tied to 0
|   ``debug_mode_i`` input is tied to 0
| As IsRVFI = 0,
|   ``rvfi_is_compressed_o`` output is tied to 0
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

