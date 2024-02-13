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

   * - ``time_irq_i``
     - in
     - SUBSYSTEM
     - Timer threw a interrupt
     - logic

   * - ``flush_o``
     - out
     - CONTROLLER
     - send a flush request out when a CSR with a side effect changes
     - logic

   * - ``halt_csr_o``
     - out
     - CONTROLLER
     - halt requested
     - logic

   * - ``commit_instr_i``
     - in
     - ID_STAGE
     - Instruction to be committed
     - scoreboard_entry_t[CVA6Cfg.NrCommitPorts-1:0]

   * - ``commit_ack_i``
     - in
     - COMMIT_STAGE
     - Commit acknowledged a instruction -> increase instret CSR
     - logic[CVA6Cfg.NrCommitPorts-1:0]

   * - ``boot_addr_i``
     - in
     - SUBSYSTEM
     - Address from which to start booting, mtvec is set to the same address
     - logic[riscv::VLEN-1:0]

   * - ``hart_id_i``
     - in
     - SUBSYSTEM
     - Hart id in a multicore environment (reflected in a CSR)
     - logic[riscv::XLEN-1:0]

   * - ``ex_i``
     - in
     - COMMIT_STAGE
     - We've got an exception from the commit stage, take it
     - exception_t

   * - ``csr_op_i``
     - in
     - COMMIT_STAGE
     - Operation to perform on the CSR file
     - fu_op

   * - ``csr_addr_i``
     - in
     - EX_STAGE
     - Address of the register to read/write
     - logic[11:0]

   * - ``csr_wdata_i``
     - in
     - COMMIT_STAGE
     - Write data in
     - logic[riscv::XLEN-1:0]

   * - ``csr_rdata_o``
     - out
     - COMMIT_STAGE
     - Read data out
     - logic[riscv::XLEN-1:0]

   * - ``dirty_fp_state_i``
     - in
     - COMMIT_STAGE
     - Mark the FP sate as dirty
     - logic

   * - ``csr_write_fflags_i``
     - in
     - COMMIT_STAGE
     - Write fflags register e.g.: we are retiring a floating point instruction
     - logic

   * - ``dirty_v_state_i``
     - in
     - ACC_DISPATCHER
     - Mark the V state as dirty
     - logic

   * - ``pc_i``
     - in
     - COMMIT_STAGE
     - PC of instruction accessing the CSR
     - logic[riscv::VLEN-1:0]

   * - ``csr_exception_o``
     - out
     - COMMIT_STAGE
     - attempts to access a CSR without appropriate privilege
     - exception_t

   * - ``epc_o``
     - out
     - FRONTEND
     - Output the exception PC to PC Gen, the correct CSR (mepc, sepc) is set accordingly
     - logic[riscv::VLEN-1:0]

   * - ``eret_o``
     - out
     - FRONTEND
     - Return from exception, set the PC of epc_o
     - logic

   * - ``trap_vector_base_o``
     - out
     - FRONTEND
     - Output base of exception vector, correct CSR is output (mtvec, stvec)
     - logic[riscv::VLEN-1:0]

   * - ``priv_lvl_o``
     - out
     - EX_STAGE
     - Current privilege level the CPU is in
     - riscv::priv_lvl_t

   * - ``acc_fflags_ex_i``
     - in
     - ACC_DISPATCHER
     - Imprecise FP exception from the accelerator (fcsr.fflags format)
     - logic[4:0]

   * - ``acc_fflags_ex_valid_i``
     - in
     - ACC_DISPATCHER
     - An FP exception from the accelerator occurred
     - logic

   * - ``fs_o``
     - out
     - ID_STAGE
     - Floating point extension status
     - riscv::xs_t

   * - ``fflags_o``
     - out
     - COMMIT_STAGE
     - Floating-Point Accured Exceptions
     - logic[4:0]

   * - ``frm_o``
     - out
     - EX_STAGE
     - Floating-Point Dynamic Rounding Mode
     - logic[2:0]

   * - ``fprec_o``
     - out
     - EX_STAGE
     - Floating-Point Precision Control
     - logic[6:0]

   * - ``vs_o``
     - out
     - ID_STAGE
     - Vector extension status
     - riscv::xs_t

   * - ``irq_ctrl_o``
     - out
     - ID_STAGE
     - interrupt management to id stage
     - irq_ctrl_t

   * - ``en_translation_o``
     - out
     - EX_STAGE
     - enable VA translation
     - logic

   * - ``en_ld_st_translation_o``
     - out
     - EX_STAGE
     - enable VA translation for load and stores
     - logic

   * - ``ld_st_priv_lvl_o``
     - out
     - EX_STAGE
     - Privilege level at which load and stores should happen
     - riscv::priv_lvl_t

   * - ``sum_o``
     - out
     - EX_STAGE
     - TO_BE_COMPLETED
     - logic

   * - ``mxr_o``
     - out
     - EX_STAGE
     - TO_BE_COMPLETED
     - logic

   * - ``satp_ppn_o``
     - out
     - EX_STAGE
     - TO_BE_COMPLETED
     - logic[riscv::PPNW-1:0]

   * - ``asid_o``
     - out
     - EX_STAGE
     - TO_BE_COMPLETED
     - logic[AsidWidth-1:0]

   * - ``irq_i``
     - in
     - SUBSYSTEM
     - external interrupt in
     - logic[1:0]

   * - ``ipi_i``
     - in
     - SUBSYSTEM
     - inter processor interrupt -> connected to machine mode sw
     - logic

   * - ``debug_req_i``
     - in
     - ID_STAGE
     - debug request in
     - logic

   * - ``set_debug_pc_o``
     - out
     - FRONTEND
     - TO_BE_COMPLETED
     - logic

   * - ``tvm_o``
     - out
     - ID_STAGE
     - trap virtual memory
     - logic

   * - ``tw_o``
     - out
     - ID_STAGE
     - timeout wait
     - logic

   * - ``tsr_o``
     - out
     - ID_STAGE
     - trap sret
     - logic

   * - ``debug_mode_o``
     - out
     - EX_STAGE
     - we are in debug mode -> that will change some decoding
     - logic

   * - ``single_step_o``
     - out
     - COMMIT_STAGE
     - we are in single-step mode
     - logic

   * - ``icache_en_o``
     - out
     - CACHE
     - L1 ICache Enable
     - logic

   * - ``dcache_en_o``
     - out
     - CACHE
     - L1 DCache Enable
     - logic

   * - ``acc_cons_en_o``
     - out
     - ACC_DISPATCHER
     - Accelerator memory consistent mode
     - logic

   * - ``perf_addr_o``
     - out
     - PERF_COUNTERS
     - read/write address to performance counter module
     - logic[11:0]

   * - ``perf_data_o``
     - out
     - PERF_COUNTERS
     - write data to performance counter module
     - logic[riscv::XLEN-1:0]

   * - ``perf_data_i``
     - in
     - PERF_COUNTERS
     - read data from performance counter module
     - logic[riscv::XLEN-1:0]

   * - ``perf_we_o``
     - out
     - PERF_COUNTERS
     - TO_BE_COMPLETED
     - logic

   * - ``pmpcfg_o``
     - out
     - ACC_DISPATCHER
     - PMP configuration containing pmpcfg for max 16 PMPs
     - riscv::pmpcfg_t[15:0]

   * - ``pmpaddr_o``
     - out
     - ACC_DISPATCHER
     - PMP addresses
     - logic[15:0][riscv::PLEN-3:0]

   * - ``mcountinhibit_o``
     - out
     - PERF_COUNTERS
     - TO_BE_COMPLETED
     - logic[31:0]
