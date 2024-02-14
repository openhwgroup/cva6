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
     - Description
     - Connection
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

   * - ``boot_addr_i``
     - in
     - Reset boot address
     - SUBSYSTEM
     - logic[riscv::VLEN-1:0]

   * - ``hart_id_i``
     - in
     - Hard ID reflected as CSR
     - SUBSYSTEM
     - logic[riscv::XLEN-1:0]

   * - ``irq_i``
     - in
     - Level sensitive (async) interrupts
     - SUBSYSTEM
     - logic[1:0]

   * - ``ipi_i``
     - in
     - Inter-processor (async) interrupt
     - SUBSYSTEM
     - logic

   * - ``time_irq_i``
     - in
     - Timer (async) interrupt
     - SUBSYSTEM
     - logic

   * - ``debug_req_i``
     - in
     - Debug (async) request
     - SUBSYSTEM
     - logic

   * - ``rvfi_probes_o``
     - out
     - Probes to build RVFI, can be left open when not used
     - SUBSYSTEM
     - rvfi_probes_t

   * - ``cvxif_req_o``
     - out
     - CVXIF request
     - SUBSYSTEM
     - cvxif_req_t

   * - ``cvxif_resp_i``
     - in
     - CVXIF response
     - SUBSYSTEM
     - cvxif_resp_t

   * - ``noc_req_o``
     - out
     - noc request, can be AXI or OpenPiton
     - SUBSYSTEM
     - noc_req_t

   * - ``noc_resp_i``
     - in
     - noc response, can be AXI or OpenPiton
     - SUBSYSTEM
     - noc_resp_t
