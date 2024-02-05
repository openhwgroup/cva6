..
   Copyright 2024 Thales DIS France SAS
   Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
   You may obtain a copy of the License at https://solderpad.org/licenses/

   Original Author: Jean-Roch COULON - Thales

.. _CV32A6_cva6:

.. list-table:: cva6 module IO ports
   :header-rows: 1

   * - Signal
     - IO
     - connection
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

   * - ``boot_addr_i``
     - in
     - SUBSYSTEM
     - logic [riscv::VLEN-1:0]
     - Reset boot address

   * - ``hart_id_i``
     - in
     - SUBSYSTEM
     - logic [riscv::XLEN-1:0]
     - Hard ID reflected as CSR

   * - ``irq_i``
     - in
     - SUBSYSTEM
     - logic [1:0]
     - Level sensitive (async) interrupts

   * - ``ipi_i``
     - in
     - SUBSYSTEM
     - logic
     - Inter-processor (async) interrupt

   * - ``time_irq_i``
     - in
     - SUBSYSTEM
     - logic
     - Timer (async) interrupt

   * - ``debug_req_i``
     - in
     - SUBSYSTEM
     - logic
     - Debug (async) request

   * - ``rvfi_probes_o``
     - out
     - SUBSYSTEM
     - rvfi_probes_t
     - Probes to build RVFI, can be left open when not used

   * - ``cvxif_req_o``
     - out
     - SUBSYSTEM
     - cvxif_req_t
     - CVXIF request

   * - ``cvxif_resp_i``
     - in
     - SUBSYSTEM
     - cvxif_resp_t
     - CVXIF response

   * - ``noc_req_o``
     - out
     - SUBSYSTEM
     - noc_req_t
     - noc request, can be AXI or OpenPiton

   * - ``noc_resp_i``
     - in
     - SUBSYSTEM
     - noc_resp_t
     - noc response, can be AXI or OpenPiton
