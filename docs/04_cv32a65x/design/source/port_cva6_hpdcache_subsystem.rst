..
   Copyright 2024 Thales DIS France SAS
   Licensed under the Solderpad Hardware License, Version 2.1 (the "License");
   you may not use this file except in compliance with the License.
   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
   You may obtain a copy of the License at https://solderpad.org/licenses/

   Original Author: Jean-Roch COULON - Thales

.. _CVA6_cva6_hpdcache_subsystem_ports:

.. list-table:: **cva6_hpdcache_subsystem module** IO ports
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

   * - ``icache_en_i``
     - in
     - Instruction cache enable
     - CSR_REGFILE
     - logic

   * - ``icache_flush_i``
     - in
     - Flush the instruction cache
     - CONTROLLER
     - logic

   * - ``icache_areq_i``
     - in
     - Input address translation request
     - EX_STAGE
     - icache_areq_t

   * - ``icache_areq_o``
     - out
     - Output address translation request
     - EX_STAGE
     - icache_arsp_t

   * - ``icache_dreq_i``
     - in
     - Input data translation request
     - FRONTEND
     - icache_dreq_t

   * - ``icache_dreq_o``
     - out
     - Output data translation request
     - FRONTEND
     - icache_drsp_t

   * - ``dcache_enable_i``
     - in
     - Data cache enable
     - CSR_REGFILE
     - logic

   * - ``dcache_flush_i``
     - in
     - Data cache flush
     - CONTROLLER
     - logic

   * - ``dcache_flush_ack_o``
     - out
     - Flush acknowledge
     - CONTROLLER
     - logic

   * - ``dcache_amo_req_i``
     - in
     - AMO request
     - EX_STAGE
     - ariane_pkg::amo_req_t

   * - ``dcache_amo_resp_o``
     - out
     - AMO response
     - EX_STAGE
     - ariane_pkg::amo_resp_t

   * - ``dcache_req_ports_i``
     - in
     - Data cache input request ports
     - EX_STAGE
     - dcache_req_i_t[NumPorts-1:0]

   * - ``dcache_req_ports_o``
     - out
     - Data cache output request ports
     - EX_STAGE
     - dcache_req_o_t[NumPorts-1:0]

   * - ``wbuffer_empty_o``
     - out
     - Write buffer status to know if empty
     - EX_STAGE
     - logic

   * - ``wbuffer_not_ni_o``
     - out
     - Write buffer status to know if not non idempotent
     - EX_STAGE
     - logic

Due to cv32a65x configuration, some ports are tied to a static value. These ports do not appear in the above table, they are listed below

| As PerfCounterEn = 0,
|   ``icache_miss_o`` output is tied to 0
|   ``dcache_miss_o`` output is tied to 0
| For any HW configuration,
|   ``dcache_cmo_req_i`` input is tied to 0
|   ``dcache_cmo_resp_o`` output is tied to open
|   ``hwpf_base_set_i`` input is tied to 0
|   ``hwpf_base_i`` input is tied to 0
|   ``hwpf_base_o`` output is tied to 0
|   ``hwpf_param_set_i`` input is tied to 0
|   ``hwpf_param_i`` input is tied to 0
|   ``hwpf_param_o`` output is tied to 0
|   ``hwpf_throttle_set_i`` input is tied to 0
|   ``hwpf_throttle_i`` input is tied to 0
|   ``hwpf_throttle_o`` output is tied to 0
|   ``hwpf_status_o`` output is tied to 0

