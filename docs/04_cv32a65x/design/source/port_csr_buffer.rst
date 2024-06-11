..
   Copyright 2024 Thales DIS France SAS
   Licensed under the Solderpad Hardware License, Version 2.1 (the "License");
   you may not use this file except in compliance with the License.
   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
   You may obtain a copy of the License at https://solderpad.org/licenses/

   Original Author: Jean-Roch COULON - Thales

.. _CVA6_csr_buffer_ports:

.. list-table:: **csr_buffer module** IO ports
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
     - Flush CSR
     - CONTROLLER
     - logic

   * - ``fu_data_i``
     - in
     - FU data needed to execute instruction
     - ISSUE_STAGE
     - fu_data_t

   * - ``csr_ready_o``
     - out
     - CSR FU is ready
     - ISSUE_STAGE
     - logic

   * - ``csr_valid_i``
     - in
     - CSR instruction is valid
     - ISSUE_STAGE
     - logic

   * - ``csr_result_o``
     - out
     - CSR buffer result
     - ISSUE_STAGE
     - logic[CVA6Cfg.XLEN-1:0]

   * - ``csr_commit_i``
     - in
     - commit the pending CSR OP
     - TO_BE_COMPLETED
     - logic

   * - ``csr_addr_o``
     - out
     - CSR address to write
     - COMMIT_STAGE
     - logic[11:0]


