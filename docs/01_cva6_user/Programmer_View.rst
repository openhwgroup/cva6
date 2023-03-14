..
   Copyright (c) 2023 OpenHW Group
   Copyright (c) 2023 Thales DIS design services SAS

   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1

.. Level 1
   =======

   Level 2
   -------

   Level 3
   ~~~~~~~

   Level 4
   ^^^^^^^

.. _cva6_programmers_view:

Programmer’s View
=================
In each section, we must make clear when a feature is variable upon parameters

RISC-V Extensions
-----------------
Need for step1 verification.
As CVA6 implements specified RISC-V extensions, this will be a short section, where we mention which extensions are always present or optional.

RISC-V Privileges
-----------------
Need for step1 verification.
We identify the supported RISC-V privileges

RISC-V Virtual Memory
---------------------
Need for step1 verification (MMU by 10xEngineers).
We identify the supported RISC-V virtual memories

CV32A6 supports the RISC-V Sv32 virtual memory when the ``MMUEn`` parameter is set to 1 (and ``Xlen`` is set to 32).

CV64A6 supports the RISC-V Sv39 virtual memory when the ``MMUEn`` parameter is set to 1 (and ``Xlen`` is set to 64).

The virtual memory is implemented by a memory management unit (MMU) that accelerates the translation from virtual memory addresses (as handled by the core) and physical memory addresses. The MMU integrable transaction lookaside buffers (TLB) and a hardware page table walker (PTW). The number of instruction and data TLB entries are configured with ``InstrTlbEntries`` and ``DataTlbEntries``.

Note that the CV32A6 memory will evolve to feature micro-TLB and shared TLB.

Memory Alignment
----------------
CVA6 does not support non-aligned memory accesses.

