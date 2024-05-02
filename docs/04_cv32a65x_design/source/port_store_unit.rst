..
   Copyright 2024 Thales DIS France SAS
   Licensed under the Solderpad Hardware License, Version 2.1 (the "License");
   you may not use this file except in compliance with the License.
   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
   You may obtain a copy of the License at https://solderpad.org/licenses/

   Original Author: Jean-Roch COULON - Thales

.. _CVA6_store_unit_ports:

.. list-table:: **store_unit module** IO ports
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
     - Flush
     - CONTROLLER
     - logic

   * - ``stall_st_pending_i``
     - in
     - TO_BE_COMPLETED
     - TO_BE_COMPLETED
     - logic

   * - ``no_st_pending_o``
     - out
     - TO_BE_COMPLETED
     - TO_BE_COMPLETED
     - logic

   * - ``store_buffer_empty_o``
     - out
     - Store buffer is empty
     - TO_BE_COMPLETED
     - logic

   * - ``valid_i``
     - in
     - Store instruction is valid
     - ISSUE_STAGE
     - logic

   * - ``lsu_ctrl_i``
     - in
     - Data input
     - ISSUE_STAGE
     - lsu_ctrl_t

   * - ``pop_st_o``
     - out
     - TO_BE_COMPLETED
     - TO_BE_COMPLETED
     - logic

   * - ``commit_i``
     - in
     - Instruction commit
     - TO_BE_COMPLETED
     - logic

   * - ``commit_ready_o``
     - out
     - TO_BE_COMPLETED
     - TO_BE_COMPLETED
     - logic

   * - ``valid_o``
     - out
     - Store result is valid
     - ISSUE_STAGE
     - logic

   * - ``trans_id_o``
     - out
     - Transaction ID
     - ISSUE_STAGE
     - logic[CVA6Cfg.TRANS_ID_BITS-1:0]

   * - ``result_o``
     - out
     - Store result
     - ISSUE_STAGE
     - logic[CVA6Cfg.XLEN-1:0]

   * - ``ex_o``
     - out
     - Store exception output
     - TO_BE_COMPLETED
     - exception_t

   * - ``translation_req_o``
     - out
     - Address translation request
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
     - Exception raised before store
     - TO_BE_COMPLETED
     - exception_t

   * - ``page_offset_i``
     - in
     - Address to be checked
     - load_unit
     - logic[11:0]

   * - ``page_offset_matches_o``
     - out
     - Address check result
     - load_unit
     - logic

   * - ``req_port_i``
     - in
     - Data cache request
     - CACHES
     - dcache_req_o_t

   * - ``req_port_o``
     - out
     - Data cache response
     - CACHES
     - dcache_req_i_t

Due to cv32a65x configuration, some ports are tied to a static value. These ports do not appear in the above table, they are listed below

| As RVA = False,
|   ``amo_valid_commit_i`` input is tied to 0
|   ``amo_req_o`` output is tied to 0
|   ``amo_resp_i`` input is tied to 0
| As IsRVFI = 0,
|   ``rvfi_mem_paddr_o`` output is tied to 0
| As RVH = False,
|   ``tinst_o`` output is tied to 0
|   ``hs_ld_st_inst_o`` output is tied to 0
|   ``hlvx_inst_o`` output is tied to 0
| For any HW configuration,
|   ``dtlb_hit_i`` input is tied to 1

