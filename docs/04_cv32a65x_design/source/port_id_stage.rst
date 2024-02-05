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
     - logic
     - Subsystem Clock

   * - ``rst_ni``
     - in
     - SUBSYSTEM
     - logic
     - Asynchronous reset active low

   * - ``flush_i``
     - in
     - CONTROLLER
     - logic
     - Fetch flush request

   * - ``debug_req_i``
     - in
     - SUBSYSTEM
     - logic
     - Debug (async) request

   * - ``fetch_entry_i``
     - in
     - FRONTEND
     - ariane_pkg::fetch_entry_t
     - Handshake's data between fetch and decode

   * - ``fetch_entry_valid_i``
     - in
     - FRONTEND
     - logic
     - Handshake's valid between fetch and decode

   * - ``fetch_entry_ready_o``
     - out
     - FRONTEND
     - logic
     - Handshake's ready between fetch and decode

   * - ``issue_entry_o``
     - out
     - ISSUE
     - ariane_pkg::scoreboard_entry_t
     - Handshake's data between decode and issue

   * - ``orig_instr_o``
     - out
     - ISSUE
     - logic [31:0]
     - instruction value

   * - ``issue_entry_valid_o``
     - out
     - ISSUE
     - logic
     - Handshake's valid between decode and issue

   * - ``is_ctrl_flow_o``
     - out
     - ISSUE
     - logic
     - Report if instruction is a control flow instruction

   * - ``issue_instr_ack_i``
     - in
     - ISSUE
     - logic
     - Handshake's acknowlege between decode and issue

   * - ``rvfi_is_compressed_o``
     - out
     - none
     - logic
     - none

   * - ``priv_lvl_i``
     - in
     - CSR
     - riscv::priv_lvl_t
     - Report current privilege level

   * - ``fs_i``
     - in
     - CSR
     - riscv::xs_t
     - Report floating point extension status

   * - ``frm_i``
     - in
     - CSR
     - logic [2:0]
     - Report floating point dynamic rounding mode

   * - ``vs_i``
     - in
     - CSR
     - riscv::xs_t
     - Report vector extension status

   * - ``irq_i``
     - in
     - SUBSYSTEM
     - logic [1:0]
     - Level sensitive (async) interrupts

   * - ``irq_ctrl_i``
     - in
     - CSR
     - ariane_pkg::irq_ctrl_t
     - TBD

   * - ``debug_mode_i``
     - in
     - CSR
     - logic
     - Report if current mode is debug

   * - ``tvm_i``
     - in
     - CSR
     - logic
     - TBD

   * - ``tw_i``
     - in
     - CSR
     - logic
     - TBD

   * - ``tsr_i``
     - in
     - none
     - logic
     - none
