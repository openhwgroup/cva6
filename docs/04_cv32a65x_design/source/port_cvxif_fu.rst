..
   Copyright 2024 Thales DIS France SAS
   Licensed under the Solderpad Hardware License, Version 2.1 (the "License");
   you may not use this file except in compliance with the License.
   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
   You may obtain a copy of the License at https://solderpad.org/licenses/

   Original Author: Jean-Roch COULON - Thales

.. _CVA6_cvxif_fu_ports:

.. list-table:: **cvxif_fu module** IO ports
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

   * - ``fu_data_i``
     - in
     - FU data needed to execute instruction
     - ISSUE_STAGE
     - fu_data_t

   * - ``x_valid_i``
     - in
     - CVXIF instruction is valid
     - ISSUE_STAGE
     - logic

   * - ``x_ready_o``
     - out
     - CVXIF is ready
     - ISSUE_STAGE
     - logic

   * - ``x_off_instr_i``
     - in
     - Offloaded instruction
     - ISSUE_STAGE
     - logic[31:0]

   * - ``x_trans_id_o``
     - out
     - CVXIF transaction ID
     - ISSUE_STAGE
     - logic[CVA6Cfg.TRANS_ID_BITS-1:0]

   * - ``x_exception_o``
     - out
     - CVXIF exception
     - ISSUE_STAGE
     - exception_t

   * - ``x_result_o``
     - out
     - CVXIF FU result
     - ISSUE_STAGE
     - logic[CVA6Cfg.XLEN-1:0]

   * - ``x_valid_o``
     - out
     - CVXIF result valid
     - ISSUE_STAGE
     - logic

   * - ``x_we_o``
     - out
     - CVXIF write enable
     - ISSUE_STAGE
     - logic

   * - ``cvxif_req_o``
     - out
     - CVXIF request
     - SUBSYSTEM
     - cvxif_pkg::cvxif_req_t

   * - ``cvxif_resp_i``
     - in
     - CVXIF response
     - SUBSYSTEM
     - cvxif_pkg::cvxif_resp_t

Due to cv32a65x configuration, some ports are tied to a static value. These ports do not appear in the above table, they are listed below

| As PRIV = MachineOnly,
|   ``priv_lvl_i`` input is tied to MachineMode

