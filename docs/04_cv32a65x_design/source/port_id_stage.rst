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
     - Connection
     - Type
     - Description

   * - ``clk_i``
     - in
     - SUBSYSTEM
     - Subsystem Clock
     - logic

   * - ``rst_ni``
     - in
     - SUBSYSTEM
     - Asynchronous reset active low
     - logic

   * - ``flush_i``
     - in
     - CONTROLLER
     - Fetch flush request
     - logic

   * - ``debug_req_i``
     - in
     - SUBSYSTEM
     - Debug (async) request
     - logic

   * - ``fetch_entry_i``
     - in
     - FRONTEND
     - Handshake's data between fetch and decode
     - ariane_pkg::fetch_entry_t

   * - ``fetch_entry_valid_i``
     - in
     - FRONTEND
     - Handshake's valid between fetch and decode
     - logic

   * - ``fetch_entry_ready_o``
     - out
     - FRONTEND
     - Handshake's ready between fetch and decode
     - logic

   * - ``issue_entry_o``
     - out
     - ISSUE
     - Handshake's data between decode and issue
     - ariane_pkg::scoreboard_entry_t

   * - ``orig_instr_o``
     - out
     - ISSUE
     - instruction value
     - logic[31:0]

   * - ``issue_entry_valid_o``
     - out
     - ISSUE
     - Handshake's valid between decode and issue
     - logic

   * - ``is_ctrl_flow_o``
     - out
     - ISSUE
     - Report if instruction is a control flow instruction
     - logic

   * - ``issue_instr_ack_i``
     - in
     - ISSUE
     - Handshake's acknowlege between decode and issue
     - logic

   * - ``rvfi_is_compressed_o``
     - out
     - none
     - none
     - logic

   * - ``priv_lvl_i``
     - in
     - CSR
     - Report current privilege level
     - riscv::priv_lvl_t

   * - ``fs_i``
     - in
     - CSR
     - Report floating point extension status
     - riscv::xs_t

   * - ``frm_i``
     - in
     - CSR
     - Report floating point dynamic rounding mode
     - logic[2:0]

   * - ``vs_i``
     - in
     - CSR
     - Report vector extension status
     - riscv::xs_t

   * - ``irq_i``
     - in
     - SUBSYSTEM
     - Level sensitive (async) interrupts
     - logic[1:0]

   * - ``irq_ctrl_i``
     - in
     - CSR
     - TBD
     - ariane_pkg::irq_ctrl_t

   * - ``debug_mode_i``
     - in
     - CSR
     - Report if current mode is debug
     - logic

   * - ``tvm_i``
     - in
     - CSR
     - TBD
     - logic

   * - ``tw_i``
     - in
     - CSR
     - TBD
     - logic

   * - ``tsr_i``
     - in
     - none
     - none
     - logic
