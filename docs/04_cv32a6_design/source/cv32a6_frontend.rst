..
   Copyright 2021 Thales DIS design services SAS
   Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
   You may obtain a copy of the License at https://solderpad.org/licenses/

   Original Author: Jean-Roch COULON - Thales

.. _CV32A6_FRONTEND:

FRONTEND Module
===============

Description
-----------

The FRONTEND module implements two first stages of the cva6 pipeline, PC gen and Fetch stages.

PC gen stage is responsible for generating the next program counter hosting a Branch Target Buffer (BTB) a Branch History Table (BHT) and a Return Address Stack (RAS) to speculate on the branch target address.

Fetch stage requests data to the CACHE module, realigns the data to store them in instruction queue and transmits the instructions to the DECODE module. FRONTEND can fetch up to 2 instructions per cycles when C extension instructions is used, but as instruction queue limits the data rate, up to one instruction per cycle can be sent to DECODE.

The module is connected to:

* CACHES module provides fethed instructions to FRONTEND.
* DECODE module receives instructions from FRONTEND.
* CONTROLLER module can flush FRONTEND PC gen stage
* EXECUTE, CONTROLLER, CSR and COMMIT modules triggers PC jumping due to a branch mispredict, an exception, a return from exception, a debug entry or pipeline flush. They provides related PC next value.
* CSR module states about debug mode.


.. list-table:: FRONTEND interface signals
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

   * - ``debug_mode_i``
     - in
     - CSR
     - logic
     - Debug mode state

   * - ``flush_i``
     - in
     - CONTROLLER
     - logic
     - Fetch flush request

   * - ``flush_bp_i``
     - in
     - tied at zero
     - logic
     - flush branch prediction

   * - ``boot_addr_i``
     - in
     - SUBSYSTEM
     - logic[VLEN-1:0]
     - Next PC when reset

   * - ``resolved_branch_i``
     - in
     - EXECUTE
     - bp_resolve_t
     - mispredict event and next PC

   * - ``eret_i``
     - in
     - CSR
     - logic
     - Return from exception event

   * - ``epc_i``
     - in
     - CSR
     - logic[VLEN-1:0]
     - Next PC when returning from exception

   * - ``ex_valid_i``
     - in
     - COMMIT
     - logic
     - Exception event

   * - ``trap_vector_base_i``
     - in
     - CSR
     - logic[VLEN-1:0]
     - Next PC when jumping into exception

   * - ``set_pc_commit_i``
     - in
     - CONTROLLER
     - logic
     - Set the PC coming from COMMIT as next PC


   * - ``pc_commit_i``
     - in
     - COMMIT
     - logic[VLEN-1:0]
     - Next PC when flushing pipeline

   * - ``set_debug_pc_i``
     - in
     - CSR
     - logic
     - Debug event

   * - ``icache_dreq_o``
     - out
     - CACHES
     - icache_dreq_i_t
     - Handshake between CACHE and FRONTEND (fetch)

   * - ``icache_dreq_i``
     - in
     - CACHES
     - icache_dreq_o_t
     - Handshake between CACHE and FRONTEND (fetch)

   * - ``fetch_entry_o``
     - out
     - DECODE
     - fetch_entry_t
     - Handshake's data between FRONTEND (fetch) and DECODE

   * - ``fetch_entry_valid_o``
     - out
     - DECODE
     - logic
     - Handshake's valid between FRONTEND (fetch) and DECODE

   * - ``fetch_entry_ready_i``
     - in
     - DECODE
     - logic
     - Handshake's ready between FRONTEND (fetch) and DECODE


Functionality
-------------

PC Generation stage
~~~~~~~~~~~~~~~~~~~

PC gen generates the next program counter. The next PC can originate from the following sources (listed in order of precedence):

* **Reset state:** At reset, the PC is assigned to the boot address.

* **Branch Predict:** Fetched instruction is predecoded thanks to instr_scan submodule. When instruction is a control flow, three cases need to be considered:

  + 1) If instruction is a JALR and BTB (Branch Target Buffer) returns a valid address, next PC is predicted by BTB. Else JALR is not considered as a control flow instruction, which will generate a mispredict.

  + 2) If instruction is a branch and BTH (Branch History table) returns a valid address, next PC is predicted by BHT. Else branch is not considered as an control flow instruction, which will generate a mispredict when branch is taken.

  + 3) If instruction is a RET and RAS (Return Address Stack) returns a valid address and RET has already been consummed by instruction queue. Else RET is considered as a control flow instruction but next PC is not predicted. A mispredict wil be generated.

  Then the PC gen informs the Fetch stage that it performed a prediction on the PC. *In CV32A6 v0.1.0, Branch Prediction is simplified: no information is stored in BTB, BHT and RAS. JALR, branch and RET instructions are not considered as control flow instruction and will generates mispredict.*

* **Default:** PC + 4 is fetched. PC Gen always fetches on a word boundary (32-bit). Compressed instructions are handled by fetch stage.

* **Mispredict:** When a branch prediction is mispredicted, the EXECUTE feedbacks a misprediction. This can either be a 'real' mis-prediction or a branch which was not recognized as one. In any case we need to correct our action and start fetching from the correct address.

* **Replay instruction fetch:** When the instruction queue is full, the instr_queue submodule asks the fetch replay and provides the address to be replayed.

* **Return from environment call:** When CSR asks a return from an environment call, the PC is assigned to the successive PC to the one stored in the CSR [m-s]epc register.

* **Exception/Interrupt:** If an exception (or interrupt, which is in the context of RISC-V subsystems quite similar) is triggered by the COMMIT, the next PC Gen is assigned to the CSR trap vector base address. The trap vector base address can be different depending on whether the exception traps to S-Mode or M-Mode (user mode exceptions are currently not supported). It is the purpose of the CSR Unit to figure out where to trap to and present the correct address to PC Gen.

* **Pipeline Flush:** When a CSR with side-effects gets written the whole pipeline is flushed by CONTROLLER and FRONTEND starts fetching from the next instruction again in order to take the up-dated information into account (for example virtual memory base pointer changes). The PC related to the flush action is provided by the COMMIT. Moreover flush is also transmitted to the CACHES through the next fetch CACHES access and instruction queue is reset.

* **Debug:** Debug has the highest order of precedence as it can interrupt any control flow requests. It also the only source of control flow change which can actually happen simultaneously to any other of the forced control flow changes. The debug jump is requested by CSR. The address to be jumped into is HW coded. This debug feature is not supported by CV32A6 v0.1.0.

All program counters are logical addressed. If the logical to physical mapping changes a fence.vm instruction should used to flush the pipeline *and TLBs (MMU is not enabled in CV32A6 v0.1.0)*.



Fetch Stage
~~~~~~~~~~~

Fetch stage controls by handshake protocol the CACHE module. Fetched data are 32-bit block with word aligned address. A granted fetch is realigned into instr_realign submodule to produce instructions. Then instructions are pushed into an internal instruction FIFO called instruction queue (instr_queue submodule). This submodule stores the instructions and related information which allow to identify the outstanding transactions. In the case CONTROLLER decides to flush the instruction queue, the outstanding transactions are discarded.

*The Fetch stage asks the MMU (MMU is not enabled in CV32A6 v0.1.0) to translate the requested address.*

Memory *and MMU (MMU is not enabled in CV32A6 v0.1.0)* can feedback potential exceptions generated by the memory fetch request. They can be bus errors, invalid accesses or instruction page faults.



Architecture and Submodules
---------------------------

.. figure:: ../images/frontend_modules.png
   :name: FRONTEND submodules
   :align: center
   :alt:

   FRONTEND submodules


Instr_realign submodule
~~~~~~~~~~~~~~~~~~~~~~~

.. list-table:: instr_realign interface signals
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
     - Subystem Clock

   * - ``rst_ni``
     - in
     - SUBSYSTEM
     - logic
     - Asynchronous reset active low

   * - ``flush_i``
     - in
     - FRONTEND
     - logic
     - Instr_align Flush

   * - ``valid_i``
     - in
     - CACHES (reg)
     - logic
     - 32-bit block is valid

   * - ``address_i``
     - in
     - CACHES (reg)
     - logic[VLEN-1:0]
     - 32-bit block address

   * - ``data_i``
     - in
     - CACHES (reg)
     - logic[31:0]
     - 32-bit block

   * - ``valid_o``
     - out
     - FRONTEND
     - logic[1:0]
     - instruction is valid

   * - ``addr_o``
     - out
     - FRONTEND
     - logic[1:0][VLEN-1:0]
     - Instruction address

   * - ``instr_o``
     - out
     - instr_scan, instr_queue
     - logic[1:0][31:0]
     - Instruction

   * - ``serving_unaligned_o``
     - out
     - FRONTEND
     - logic
     - Instruction is unaligned


The 32-bit aligned block coming from the CACHE module enters the instr_realign submodule. This submodule extracts the instructions from the 32-bit blocks, up to two instructions because it is possible to fetch two instructions when C extension is used. If the instructions are not compressed, it is possible that the instruction is not aligned on the block size but rather interleaved with two cache blocks. In that case, two cache accesses are needed. The instr_realign submodule provides at maximum one instruction per cycle. Not complete instruction is stored in instr_realign submodule before being provided in the next cycles.

In case of mispredict, flush, replay or branch predict, the instr_realign is re-initialized, the internal register storing the instruction alignment state is reset.


Instr_queue submodule
~~~~~~~~~~~~~~~~~~~~~

.. list-table:: instr_realign interface signals
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
     - Subystem Clock

   * - ``rst_ni``
     - in
     - SUBSYSTEM
     - logic
     - Asynchronous reset active low

   * - ``flush_i``
     -  in
     -  CONTROLLER
     -  logic
     -  Fetch flush request

   * - ``valid_i``
     -  in
     -  instr_realign
     -  logic[1:0]
     -  Instruction is valid

   * - ``instr_i``
     -  in
     -  instr_realign
     -  logic[1:0][31:0]
     -  Instruction

   * - ``addr_i``
     -  in
     -  instr_realign
     - logic[1:0][VLEN-1:0]
     -  Instruction address

   * - ``predict_address_i``
     -  in
     -  FRONTEND
     -  logic[VLEN-1:0]
     -  Instruction predict address

   * - ``cf_type_i``
     -  in
     -  FRONTEND
     -  logic[1:0]
     -  Instruction control flow type

   * - ``ready_o``
     -  out
     -  CACHES
     -  logic
     -  Handshake's ready between CACHE and FRONTEND (fetch stage)

   * - ``consumed_o``
     -  out
     -  FRONTEND
     -  logic[1:0]
     -  Indicates instructions consummed, that is to say popped by DECODE

   * - ``exception_i``
     -  in
     -  CACHES (reg)
     -  logic
     -  Exception

   * - ``exception_addr_i``
     -  in
     -  CACHES (reg)
     -  logic[VLEN-1:0]
     -  Exception address

   * - ``replay_o``
     -  out
     -  FRONTEND
     -  logic
     -  Replay instruction because one of the FIFO was already full

   * - ``replay_addr_o``
     -  out
     -  FRONTEND
     -  logic[VLEN-1:0]
     -  Address at which to replay the fetch

   * - ``fetch_entry_o``
     -  out
     -  DECODE
     -  fetch_entry_t
     -  Handshake's data between FRONTEND (fetch stage) and DECODE

   * - ``fetch_entry_valid_o``
     -  out
     -  DECODE
     -  logic
     -  Handshake's valid between FRONTEND (fetch stage) and DECODE

   * - ``fetch_entry_ready_i``
     -  in
     -  DECODE
     -  logic
     -  Handshake's ready between FRONTEND (fetch stage) and DECODE


The instr_queue receives 32bit block from CACHES to create a valid stream of instructions to be decoded (by DECODE), to be issued (by ISSUE) and executed (by EXECUTE). FRONTEND pushes in FIFO to store the instructions and related information needed in case of mispredict or exception: instructions, instruction control flow type, exception, exception address and predicted address. DECODE pops them when decode stage is ready and indicates to the FRONTEND the instruction has been consummed.

The instruction queue contains max 4 instructions.

In instruction queue, exception can only correspond to page-fault exception.

If the instruction queue is full, a replay request is sent to inform the fetch mechanism to replay the fetch.

The instruction queue can be flushed by CONTROLLER.



Instr_scan submodule
~~~~~~~~~~~~~~~~~~~~

.. list-table:: instr_scan interface signals
   :header-rows: 1

   * - Signal
     -  IO
     -  Connection
     -  Type
     -  Description

   * - ``instr_i``
     -  in
     -  instr_realign
     -  logic[31:0]
     -  Instruction to be predecoded

   * - ``rvi_return_o``
     -  out
     -  FRONTEND
     -  logic
     -  Return instruction

   * - ``rvi_call_o``
     -  out
     -  FRONTEND
     -  logic
     -  JAL instruction

   * - ``rvi_branch_o``
     -  out
     -  FRONTEND
     -  logic
     -  Branch instruction

   * - ``rvi_jalr_o``
     -  out
     -  FRONTEND
     -  logic
     -  JALR instruction

   * - ``rvi_jump_o``
     -  out
     -  FRONTEND
     -  logic
     -  unconditional jump instruction

   * - ``rvi_imm_o``
     -  out
     -  FRONTEND
     -  logic[VLEN-1:0]
     -  Instruction immediat

   * - ``rvc_branch_o``
     -  out
     -  FRONTEND
     -  logic
     -  Branch compressed instruction

   * - ``rvc_jump_o``
     -  out
     -  FRONTEND
     -  logic
     -  unconditional jump compressed instruction

   * - ``rvc_jr_o``
     -  out
     -  FRONTEND
     -  logic
     -  JR compressed instruction

   * - ``rvc_return_o``
     -  out
     -  FRONTEND
     -  logic
     -  Return compressed instruction

   * - ``rvc_jalr_o``
     -  out
     -  FRONTEND
     -  logic
     -  JALR compressed instruction

   * - ``rvc_call_o``
     -  out
     -  FRONTEND
     -  logic
     -  JAL compressed instruction

   * - ``rvc_imm_o``
     -  out
     -  FRONTEND
     -  logic[VLEN-1:0]
     -  Instruction compressed immediat


The instr_scan submodule pre-decodes the fetched instructions, instructions could be compressed or not. The outputs are used by the branch prediction feature. The instr_scan submodule tells if the instruction is compressed and provides the intruction type: branch, jump, return, jalr, imm, call or others.


BHT (Branch History Table) submodule
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. list-table:: BHT interface signals
   :header-rows: 1

   * - Signal
     -  IO
     -  Connection
     -  Type
     -  Description

   * - ``clk_i``
     -  in
     -  SUBSYSTEM
     -  logic
     -  Subystem clock

   * - ``rst_ni``
     -  in
     -  SUBSYSTEM
     -  logic
     -  Asynchronous reset active low

   * - ``flush_i``
     -  in
     -  tied at zero
     -  logic
     -  Flush request

   * - ``debug_mode_i``
     -  in
     -  CSR
     -  logic
     -  Debug mode state

   * - ``vpc_i``
     -  in
     -  CACHES (reg)
     -  logic[VLEN-1:0]
     -  Virtual PC

   * - ``bht_update_i``
     -  in
     -  EXECUTE
     -  bht_update_t
     -  Update bht with resolved address

   * - ``bht_prediction_o``
     -  out
     -  FRONTEND
     -  bht_prediction_t
     -  Prediction from bht


When a branch instruction is resolved by the EXECUTE, the relative information is stored in the Branch History Table.

The information is stored in a 1024 entry table.

The Branch History table is a two-bit saturation counter that takes the virtual address of the current fetched instruction by the CACHE. It states whether the current branch request should be taken or not. The two bit counter is updated by the successive execution of the current instructions as shown in the following figure.

.. figure:: ../images/bht.png
   :name: BHT saturation
   :align: center
   :alt:

   BHT saturation

The BHT is not updated if processor is in debug mode.

When a branch instruction is pre-decoded by instr_scan submodule, the BHT informs whether the PC address is in the BHT. In this case, the BHT predicts whether the branch is taken and provides the corresponding target address.

The BHT is never flushed.


BTB (Branch Target Buffer) submodule
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. list-table:: BTB interface signals
   :header-rows: 1

   * - Signal
     -  IO
     -  Connection
     -  Type
     -  Description

   * - ``clk_i``
     -  in
     -  SUBSYSTEM
     -  logic
     -  Subystem clock

   * - ``rst_ni``
     -  in
     -  SUBSYSTEM
     -  logic
     -  Asynchronous reset active low

   * - ``flush_i``
     -  in
     -  tied at zero
     -  logic
     -  Flush request state

   * - ``debug_mode_i``
     -  in
     -  CSR
     -  logic
     -  Debug mode

   * - ``vpc_i``
     -  in
     -  CACHES (reg)
     -  logic
     -  Virtual PC

   * - ``btb_update_i``
     -  in
     -  EXECUTE
     -  btb_update_t
     -  Update BTB with resolved address

   * - ``btb_prediction_o``
     -  out
     -  FRONTEND
     -  btb_prediction_t
     -  BTB Prediction


When a unconditional jumps to a register (JALR instruction) is mispredicted by the EXECUTE, the relative information is stored into the BTB, that is to say the JALR PC and the target address.

The information is stored in a 8 entry table.

The BTB is not updated if processor is in debug mode.

When a branch instruction is pre-decoded by instr_scan submodule, the BTB informs whether the input PC address is in BTB. In this case, the BTB provides the corresponding target address.

The BTB is never flushed.



RAS (Return Address Stack) submodule
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. list-table:: RAS interface signals
   :header-rows: 1

   * - Signal
     -  IO
     -  Connection
     -  Type
     -  Description

   * - ``clk_i``
     -  in
     -  SUBSYSTEM
     -  logic
     -  Subystem clock

   * - ``rst_ni``
     -  in
     -  SUBSYSTEM
     -  logic
     -  Asynchronous reset active low

   * - ``flush_i``
     -  in
     -  tied at zero
     -  logic
     -  Flush request

   * - ``push_i``
     -  in
     -  FRONTEND
     -  logic
     -  Push address in RAS

   * - ``pop_i``
     -  in
     -  FRONTEND
     -  logic
     -  Pop address from RAS

   * - ``data_i``
     -  in
     -  FRONTEND
     -  logic[VLEN-1:0]
     -  Data to be pushed

   * - ``data_o``
     -  out
     -  FRONTEND
     -  ras_t
     -  Popped data


When an unconditional jumps to a known target address (JAL instruction) is consummed by the instr_queue, the next pc after the JAL instruction and the return address are stored into a FIFO.

The RAS FIFO depth is 2.

When a branch instruction is pre-decoded by instr_scan submodule, the RAS informs whether the input PC address is in RAS. In this case, the RAS provides the corresponding target address.

The RAS is never flushed.

