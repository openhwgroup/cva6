..
   Copyright 2024 Thales DIS France SAS
   Licensed under the Solderpad Hardware License, Version 2.1 (the "License");
   you may not use this file except in compliance with the License.
   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
   You may obtain a copy of the License at https://solderpad.org/licenses/

   Original Author: Jean-Roch COULON - Thales

.. _CVA6_csr_regfile_ports:

.. list-table:: **csr_regfile module** IO ports
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

   * - ``time_irq_i``
     - in
     - Timer threw a interrupt
     - SUBSYSTEM
     - logic

   * - ``flush_o``
     - out
     - send a flush request out when a CSR with a side effect changes
     - CONTROLLER
     - logic

   * - ``halt_csr_o``
     - out
     - halt requested
     - CONTROLLER
     - logic

   * - ``commit_instr_i``
     - in
     - Instruction to be committed
     - ID_STAGE
     - scoreboard_entry_t[CVA6Cfg.NrCommitPorts-1:0]

   * - ``commit_ack_i``
     - in
     - Commit acknowledged a instruction -> increase instret CSR
     - COMMIT_STAGE
     - logic[CVA6Cfg.NrCommitPorts-1:0]

   * - ``boot_addr_i``
     - in
     - Address from which to start booting, mtvec is set to the same address
     - SUBSYSTEM
     - logic[CVA6Cfg.VLEN-1:0]

   * - ``hart_id_i``
     - in
     - Hart id in a multicore environment (reflected in a CSR)
     - SUBSYSTEM
     - logic[CVA6Cfg.XLEN-1:0]

   * - ``ex_i``
     - in
     - We've got an exception from the commit stage, take it
     - COMMIT_STAGE
     - exception_t

   * - ``csr_op_i``
     - in
     - Operation to perform on the CSR file
     - COMMIT_STAGE
     - fu_op

   * - ``csr_addr_i``
     - in
     - Address of the register to read/write
     - EX_STAGE
     - logic[11:0]

   * - ``csr_wdata_i``
     - in
     - Write data in
     - COMMIT_STAGE
     - logic[CVA6Cfg.XLEN-1:0]

   * - ``csr_rdata_o``
     - out
     - Read data out
     - COMMIT_STAGE
     - logic[CVA6Cfg.XLEN-1:0]

   * - ``pc_i``
     - in
     - PC of instruction accessing the CSR
     - COMMIT_STAGE
     - logic[CVA6Cfg.VLEN-1:0]

   * - ``csr_exception_o``
     - out
     - attempts to access a CSR without appropriate privilege
     - COMMIT_STAGE
     - exception_t

   * - ``epc_o``
     - out
     - Output the exception PC to PC Gen, the correct CSR (mepc, sepc) is set accordingly
     - FRONTEND
     - logic[CVA6Cfg.VLEN-1:0]

   * - ``eret_o``
     - out
     - Return from exception, set the PC of epc_o
     - FRONTEND
     - logic

   * - ``trap_vector_base_o``
     - out
     - Output base of exception vector, correct CSR is output (mtvec, stvec)
     - FRONTEND
     - logic[CVA6Cfg.VLEN-1:0]

   * - ``irq_ctrl_o``
     - out
     - interrupt management to id stage
     - ID_STAGE
     - irq_ctrl_t

   * - ``irq_i``
     - in
     - external interrupt in
     - SUBSYSTEM
     - logic[1:0]

   * - ``ipi_i``
     - in
     - inter processor interrupt -> connected to machine mode sw
     - SUBSYSTEM
     - logic

   * - ``icache_en_o``
     - out
     - L1 ICache Enable
     - CACHE
     - logic

   * - ``dcache_en_o``
     - out
     - L1 DCache Enable
     - CACHE
     - logic

   * - ``rvfi_csr_o``
     - out
     - none
     - none
     - rvfi_probes_csr_t

Due to cv32a65x configuration, some ports are tied to a static value. These ports do not appear in the above table, they are listed below

| As RVF = 0,
|   ``dirty_fp_state_i`` input is tied to 0
|   ``csr_write_fflags_i`` input is tied to 0
|   ``fs_o`` output is tied to 0
|   ``fflags_o`` output is tied to 0
|   ``frm_o`` output is tied to 0
|   ``fprec_o`` output is tied to 0
| As EnableAccelerator = 0,
|   ``dirty_v_state_i`` input is tied to 0
|   ``acc_fflags_ex_i`` input is tied to 0
|   ``acc_fflags_ex_valid_i`` input is tied to 0
|   ``acc_cons_en_o`` output is tied to 0
|   ``pmpcfg_o`` output is tied to 0
|   ``pmpaddr_o`` output is tied to 0
| As PRIV = MachineOnly,
|   ``priv_lvl_o`` output is tied to MachineMode
|   ``ld_st_priv_lvl_o`` output is tied to MAchineMode
|   ``tvm_o`` output is tied to 0
|   ``tw_o`` output is tied to 0
|   ``tsr_o`` output is tied to 0
| As RVH = False,
|   ``v_o`` output is tied to 0
|   ``vfs_o`` output is tied to 0
|   ``en_g_translation_o`` output is tied to 0
|   ``en_ld_st_g_translation_o`` output is tied to 0
|   ``ld_st_v_o`` output is tied to 0
|   ``csr_hs_ld_st_inst_i`` input is tied to 0
|   ``vs_sum_o`` output is tied to 0
|   ``vmxr_o`` output is tied to 0
|   ``vsatp_ppn_o`` output is tied to 0
|   ``vs_asid_o`` output is tied to 0
|   ``hgatp_ppn_o`` output is tied to 0
|   ``vmid_o`` output is tied to 0
|   ``vtw_o`` output is tied to 0
|   ``hu_o`` output is tied to 0
| As RVV = False,
|   ``vs_o`` output is tied to 0
| As RVS = False,
|   ``en_translation_o`` output is tied to 0
|   ``en_ld_st_translation_o`` output is tied to 0
|   ``sum_o`` output is tied to 0
|   ``mxr_o`` output is tied to 0
|   ``satp_ppn_o`` output is tied to 0
|   ``asid_o`` output is tied to 0
| As DebugEn = False,
|   ``debug_req_i`` input is tied to 0
|   ``set_debug_pc_o`` output is tied to 0
|   ``debug_mode_o`` output is tied to 0
|   ``single_step_o`` output is tied to 0
| As PerfCounterEn = 0,
|   ``perf_addr_o`` output is tied to 0
|   ``perf_data_o`` output is tied to 0
|   ``perf_data_i`` input is tied to 0
|   ``perf_we_o`` output is tied to 0
|   ``mcountinhibit_o`` output is tied to 0

