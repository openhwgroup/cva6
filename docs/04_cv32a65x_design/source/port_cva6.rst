..
   Copyright 2024 Thales DIS France SAS
   Licensed under the Solderpad Hardware License, Version 2.1 (the "License");
   you may not use this file except in compliance with the License.
   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
   You may obtain a copy of the License at https://solderpad.org/licenses/

   Original Author: Jean-Roch COULON - Thales

.. _CVA6_cva6_ports:

.. list-table:: cva6 module IO ports
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

   * - ``boot_addr_i``
     - in
     - SUBSYSTEM
     - Reset boot address
     - logic[riscv::VLEN-1:0]

   * - ``hart_id_i``
     - in
     - SUBSYSTEM
     - Hard ID reflected as CSR
     - logic[riscv::XLEN-1:0]

   * - ``irq_i``
     - in
     - SUBSYSTEM
     - Level sensitive (async) interrupts
     - logic[1:0]

   * - ``ipi_i``
     - in
     - SUBSYSTEM
     - Inter-processor (async) interrupt
     - logic

   * - ``time_irq_i``
     - in
     - SUBSYSTEM
     - Timer (async) interrupt
     - logic

   * - ``debug_req_i``
     - in
     - SUBSYSTEM
     - Debug (async) request
     - logic

   * - ``rvfi_probes_o``
     - out
     - SUBSYSTEM
     - Probes to build RVFI, can be left open when not used
     - rvfi_probes_t

   * - ``cvxif_req_o``
     - out
     - SUBSYSTEM
     - CVXIF request
     - cvxif_req_t

   * - ``cvxif_resp_i``
     - in
     - SUBSYSTEM
     - CVXIF response
     - cvxif_resp_t

   * - ``noc_req_o``
     - out
     - SUBSYSTEM
     - noc request, can be AXI or OpenPiton
     - noc_req_t

   * - ``noc_resp_i``
     - in
     - SUBSYSTEM
     - noc response, can be AXI or OpenPiton
     - noc_resp_t
