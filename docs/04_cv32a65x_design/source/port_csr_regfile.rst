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
     - logic
     - Subsystem Clock

   * - ``rst_ni``
     - in
     - SUBSYSTEM
     - logic
     - Asynchronous reset active low

   * - ``time_irq_i``
     - in
     - SUBSYSTEM
     - logic
     - Timer threw a interrupt

   * - ``flush_o``
     - out
     - CONTROLLER
     - logic
     - send a flush request out when a CSR with a side effect changes

   * - ``halt_csr_o``
     - out
     - CONTROLLER
     - logic
     - halt requested

   * - ``commit_instr_i``
     - in
     - ID_STAGE
     - scoreboard_entry_t[CVA6Cfg.NrCommitPorts-1:0]
     - Instruction to be committed

   * - ``commit_ack_i``
     - in
     - COMMIT_STAGE
     - logic[CVA6Cfg.NrCommitPorts-1:0]
     - Commit acknowledged a instruction -> increase instret CSR

   * - ``boot_addr_i``
     - in
     - SUBSYSTEM
     - logic[riscv::VLEN-1:0]
     - Address from which to start booting, mtvec is set to the same address

   * - ``hart_id_i``
     - in
     - SUBSYSTEM
     - logic[riscv::XLEN-1:0]
     - Hart id in a multicore environment (reflected in a CSR)

   * - ``ex_i``
     - in
     - COMMIT_STAGE
     - exception_t
     - We've got an exception from the commit stage, take it

   * - ``csr_op_i``
     - in
     - COMMIT_STAGE
     - fu_op
     - Operation to perform on the CSR file

   * - ``csr_addr_i``
     - in
     - EX_STAGE
     - logic[11:0]
     - Address of the register to read/write

   * - ``csr_wdata_i``
     - in
     - COMMIT_STAGE
     - logic[riscv::XLEN-1:0]
     - Write data in

   * - ``csr_rdata_o``
     - out
     - COMMIT_STAGE
     - logic[riscv::XLEN-1:0]
     - Read data out

   * - ``dirty_fp_state_i``
     - in
     - COMMIT_STAGE
     - logic
     - Mark the FP sate as dirty

   * - ``csr_write_fflags_i``
     - in
     - COMMIT_STAGE
     - logic
     - Write fflags register e.g.: we are retiring a floating point instruction

   * - ``dirty_v_state_i``
     - in
     - ACC_DISPATCHER
     - logic
     - Mark the V state as dirty

   * - ``pc_i``
     - in
     - COMMIT_STAGE
     - logic[riscv::VLEN-1:0]
     - PC of instruction accessing the CSR

   * - ``csr_exception_o``
     - out
     - COMMIT_STAGE
     - exception_t
     - attempts to access a CSR without appropriate privilege

   * - ``epc_o``
     - out
     - FRONTEND
     - logic[riscv::VLEN-1:0]
     - Output the exception PC to PC Gen, the correct CSR (mepc, sepc) is set accordingly

   * - ``eret_o``
     - out
     - FRONTEND
     - logic
     - Return from exception, set the PC of epc_o

   * - ``trap_vector_base_o``
     - out
     - FRONTEND
     - logic[riscv::VLEN-1:0]
     - Output base of exception vector, correct CSR is output (mtvec, stvec)

   * - ``priv_lvl_o``
     - out
     - EX_STAGE
     - riscv::priv_lvl_t
     - Current privilege level the CPU is in

   * - ``acc_fflags_ex_i``
     - in
     - ACC_DISPATCHER
     - logic[4:0]
     - Imprecise FP exception from the accelerator (fcsr.fflags format)

   * - ``acc_fflags_ex_valid_i``
     - in
     - ACC_DISPATCHER
     - logic
     - An FP exception from the accelerator occurred

   * - ``fs_o``
     - out
     - ID_STAGE
     - riscv::xs_t
     - Floating point extension status

   * - ``fflags_o``
     - out
     - COMMIT_STAGE
     - logic[4:0]
     - Floating-Point Accured Exceptions

   * - ``frm_o``
     - out
     - EX_STAGE
     - logic[2:0]
     - Floating-Point Dynamic Rounding Mode

   * - ``fprec_o``
     - out
     - EX_STAGE
     - logic[6:0]
     - Floating-Point Precision Control

   * - ``vs_o``
     - out
     - ID_STAGE
     - riscv::xs_t
     - Vector extension status

   * - ``irq_ctrl_o``
     - out
     - ID_STAGE
     - irq_ctrl_t
     - interrupt management to id stage

   * - ``en_translation_o``
     - out
     - EX_STAGE
     - logic
     - enable VA translation

   * - ``en_ld_st_translation_o``
     - out
     - EX_STAGE
     - logic
     - enable VA translation for load and stores

   * - ``ld_st_priv_lvl_o``
     - out
     - EX_STAGE
     - riscv::priv_lvl_t
     - Privilege level at which load and stores should happen

   * - ``sum_o``
     - out
     - EX_STAGE
     - logic
     - TO_BE_COMPLETED

   * - ``mxr_o``
     - out
     - EX_STAGE
     - logic
     - TO_BE_COMPLETED

   * - ``satp_ppn_o``
     - out
     - EX_STAGE
     - logic[riscv::PPNW-1:0]
     - TO_BE_COMPLETED

   * - ``asid_o``
     - out
     - EX_STAGE
     - logic[AsidWidth-1:0]
     - TO_BE_COMPLETED

   * - ``irq_i``
     - in
     - SUBSYSTEM
     - logic[1:0]
     - external interrupt in

   * - ``ipi_i``
     - in
     - SUBSYSTEM
     - logic
     - inter processor interrupt -> connected to machine mode sw

   * - ``debug_req_i``
     - in
     - ID_STAGE
     - logic
     - debug request in

   * - ``set_debug_pc_o``
     - out
     - FRONTEND
     - logic
     - TO_BE_COMPLETED

   * - ``tvm_o``
     - out
     - ID_STAGE
     - logic
     - trap virtual memory

   * - ``tw_o``
     - out
     - ID_STAGE
     - logic
     - timeout wait

   * - ``tsr_o``
     - out
     - ID_STAGE
     - logic
     - trap sret

   * - ``debug_mode_o``
     - out
     - EX_STAGE
     - logic
     - we are in debug mode -> that will change some decoding

   * - ``single_step_o``
     - out
     - COMMIT_STAGE
     - logic
     - we are in single-step mode

   * - ``icache_en_o``
     - out
     - CACHE
     - logic
     - L1 ICache Enable

   * - ``dcache_en_o``
     - out
     - CACHE
     - logic
     - L1 DCache Enable

   * - ``acc_cons_en_o``
     - out
     - ACC_DISPATCHER
     - logic
     - Accelerator memory consistent mode

   * - ``perf_addr_o``
     - out
     - PERF_COUNTERS
     - logic[11:0]
     - read/write address to performance counter module

   * - ``perf_data_o``
     - out
     - PERF_COUNTERS
     - logic[riscv::XLEN-1:0]
     - write data to performance counter module

   * - ``perf_data_i``
     - in
     - PERF_COUNTERS
     - logic[riscv::XLEN-1:0]
     - read data from performance counter module

   * - ``perf_we_o``
     - out
     - PERF_COUNTERS
     - logic
     - TO_BE_COMPLETED

   * - ``pmpcfg_o``
     - out
     - ACC_DISPATCHER
     - riscv::pmpcfg_t[15:0]
     - PMP configuration containing pmpcfg for max 16 PMPs

   * - ``pmpaddr_o``
     - out
     - ACC_DISPATCHER
     - logic[15:0][riscv::PLEN-3:0]
     - PMP addresses

   * - ``mcountinhibit_o``
     - out
     - PERF_COUNTERS
     - logic[31:0]
     - TO_BE_COMPLETED
