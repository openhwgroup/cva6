..
   Copyright 2024 Thales DIS France SAS
   Licensed under the Solderpad Hardware License, Version 2.1 (the "License");
   you may not use this file except in compliance with the License.
   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
   You may obtain a copy of the License at https://solderpad.org/licenses/

   Original Author: Jean-Roch COULON - Thales

.. _CVA6_csr_regfile_ports:

.. list-table:: csr_regfile module IO ports
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
     - logic[riscv::VLEN-1:0]

   * - ``hart_id_i``
     - in
     - Hart id in a multicore environment (reflected in a CSR)
     - SUBSYSTEM
     - logic[riscv::XLEN-1:0]

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
     - logic[riscv::XLEN-1:0]

   * - ``csr_rdata_o``
     - out
     - Read data out
     - COMMIT_STAGE
     - logic[riscv::XLEN-1:0]

   * - ``dirty_fp_state_i``
     - in
     - Mark the FP sate as dirty
     - COMMIT_STAGE
     - logic

   * - ``csr_write_fflags_i``
     - in
     - Write fflags register e.g.: we are retiring a floating point instruction
     - COMMIT_STAGE
     - logic

   * - ``pc_i``
     - in
     - PC of instruction accessing the CSR
     - COMMIT_STAGE
     - logic[riscv::VLEN-1:0]

   * - ``csr_exception_o``
     - out
     - attempts to access a CSR without appropriate privilege
     - COMMIT_STAGE
     - exception_t

   * - ``epc_o``
     - out
     - Output the exception PC to PC Gen, the correct CSR (mepc, sepc) is set accordingly
     - FRONTEND
     - logic[riscv::VLEN-1:0]

   * - ``eret_o``
     - out
     - Return from exception, set the PC of epc_o
     - FRONTEND
     - logic

   * - ``trap_vector_base_o``
     - out
     - Output base of exception vector, correct CSR is output (mtvec, stvec)
     - FRONTEND
     - logic[riscv::VLEN-1:0]

   * - ``priv_lvl_o``
     - out
     - Current privilege level the CPU is in
     - EX_STAGE
     - riscv::priv_lvl_t

   * - ``fs_o``
     - out
     - Floating point extension status
     - ID_STAGE
     - riscv::xs_t

   * - ``fflags_o``
     - out
     - Floating-Point Accured Exceptions
     - COMMIT_STAGE
     - logic[4:0]

   * - ``frm_o``
     - out
     - Floating-Point Dynamic Rounding Mode
     - EX_STAGE
     - logic[2:0]

   * - ``fprec_o``
     - out
     - Floating-Point Precision Control
     - EX_STAGE
     - logic[6:0]

   * - ``vs_o``
     - out
     - Vector extension status
     - ID_STAGE
     - riscv::xs_t

   * - ``irq_ctrl_o``
     - out
     - interrupt management to id stage
     - ID_STAGE
     - irq_ctrl_t

   * - ``en_translation_o``
     - out
     - enable VA translation
     - EX_STAGE
     - logic

   * - ``en_ld_st_translation_o``
     - out
     - enable VA translation for load and stores
     - EX_STAGE
     - logic

   * - ``ld_st_priv_lvl_o``
     - out
     - Privilege level at which load and stores should happen
     - EX_STAGE
     - riscv::priv_lvl_t

   * - ``sum_o``
     - out
     - TO_BE_COMPLETED
     - EX_STAGE
     - logic

   * - ``mxr_o``
     - out
     - TO_BE_COMPLETED
     - EX_STAGE
     - logic

   * - ``satp_ppn_o``
     - out
     - TO_BE_COMPLETED
     - EX_STAGE
     - logic[riscv::PPNW-1:0]

   * - ``asid_o``
     - out
     - TO_BE_COMPLETED
     - EX_STAGE
     - logic[AsidWidth-1:0]

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

   * - ``set_debug_pc_o``
     - out
     - TO_BE_COMPLETED
     - FRONTEND
     - logic

   * - ``tvm_o``
     - out
     - trap virtual memory
     - ID_STAGE
     - logic

   * - ``tw_o``
     - out
     - timeout wait
     - ID_STAGE
     - logic

   * - ``tsr_o``
     - out
     - trap sret
     - ID_STAGE
     - logic

   * - ``debug_mode_o``
     - out
     - we are in debug mode -> that will change some decoding
     - EX_STAGE
     - logic

   * - ``single_step_o``
     - out
     - we are in single-step mode
     - COMMIT_STAGE
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

Due to cv32a65x configuration, some ports are tied to a static value. These ports do not appear in the above table, they are listed below

| As EnableAccelerator = 0,
|   ``dirty_v_state_i`` input is tied to 0
|   ``acc_fflags_ex_i`` input is tied to 0
|   ``acc_fflags_ex_valid_i`` input is tied to 0
|   ``acc_cons_en_o`` output is tied to 0
|   ``pmpcfg_o`` output is tied to 0
|   ``pmpaddr_o`` output is tied to 0
| As DebugEn = 0,
|   ``debug_req_i`` input is tied to 0
| As PerfCounterEn = 0,
|   ``perf_addr_o`` output is tied to 0
|   ``perf_data_o`` output is tied to 0
|   ``perf_data_i`` input is tied to 0
|   ``perf_we_o`` output is tied to 0
|   ``mcountinhibit_o`` output is tied to 0
none
