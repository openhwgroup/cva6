..
   Copyright 2024 Thales DIS France SAS
   Licensed under the Solderpad Hardware License, Version 2.1 (the "License");
   you may not use this file except in compliance with the License.
   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
   You may obtain a copy of the License at https://solderpad.org/licenses/

   Original Author: Jean-Roch COULON - Thales

.. _CVA6_load_unit_ports:

.. list-table:: **load_unit module** IO ports
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
     - TO_BE_COMPLETED
     - TO_BE_COMPLETED
     - logic

   * - ``valid_i``
     - in
     - Load unit input port
     - TO_BE_COMPLETED
     - logic

   * - ``lsu_ctrl_i``
     - in
     - TO_BE_COMPLETED
     - TO_BE_COMPLETED
     - lsu_ctrl_t

   * - ``pop_ld_o``
     - out
     - TO_BE_COMPLETED
     - TO_BE_COMPLETED
     - logic

   * - ``valid_o``
     - out
     - Load unit result is valid
     - TO_BE_COMPLETED
     - logic

   * - ``trans_id_o``
     - out
     - Load transaction ID
     - TO_BE_COMPLETED
     - logic[CVA6Cfg.TRANS_ID_BITS-1:0]

   * - ``result_o``
     - out
     - Load result
     - TO_BE_COMPLETED
     - logic[CVA6Cfg.XLEN-1:0]

   * - ``ex_o``
     - out
     - Load exception
     - TO_BE_COMPLETED
     - exception_t

   * - ``translation_req_o``
     - out
     - Request address translation
     - TO_BE_COMPLETED
     - logic

   * - ``vaddr_o``
     - out
     - Virtual address
     - TO_BE_COMPLETED
     - logic[CVA6Cfg.VLEN-1:0]

   * - ``paddr_i``
     - in
     - Physical address
     - TO_BE_COMPLETED
     - logic[CVA6Cfg.PLEN-1:0]

   * - ``ex_i``
     - in
     - Excepted which appears before load
     - TO_BE_COMPLETED
     - exception_t

   * - ``page_offset_o``
     - out
     - TO_BE_COMPLETED
     - TO_BE_COMPLETED
     - logic[11:0]

   * - ``page_offset_matches_i``
     - in
     - TO_BE_COMPLETED
     - TO_BE_COMPLETED
     - logic

   * - ``store_buffer_empty_i``
     - in
     - Store buffer is empty
     - TO_BE_COMPLETED
     - logic

   * - ``commit_tran_id_i``
     - in
     - TO_BE_COMPLETED
     - TO_BE_COMPLETED
     - logic[CVA6Cfg.TRANS_ID_BITS-1:0]

   * - ``req_port_i``
     - in
     - Data cache request out
     - CACHES
     - dcache_req_o_t

   * - ``req_port_o``
     - out
     - Data cache request in
     - CACHES
     - dcache_req_i_t

   * - ``dcache_wbuffer_not_ni_i``
     - in
     - TO_BE_COMPLETED
     - TO_BE_COMPLETED
     - logic

Due to cv32a65x configuration, some ports are tied to a static value. These ports do not appear in the above table, they are listed below

| As RVH = False,
|   ``tinst_o`` output is tied to 0
|   ``hs_ld_st_inst_o`` output is tied to 0
|   ``hlvx_inst_o`` output is tied to 0
| For any HW configuration,
|   ``dtlb_hit_i`` input is tied to 1
| As MMUPresent = 0,
|   ``dtlb_ppn_i`` input is tied to 0

