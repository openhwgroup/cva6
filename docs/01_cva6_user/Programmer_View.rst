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
CV32A6 supports the RISC-V **Sv32** virtual memory when the ``MMUEn`` parameter is set to 1 (and ``Xlen`` is set to 32).

CV64A6 supports the RISC-V **Sv39** virtual memory when the ``MMUEn`` parameter is set to 1 (and ``Xlen`` is set to 64).

By default, CV32A6 and CV64A6 are in RISC-V **Bare** mode. **Sv32** or **Sv39** are enabled by writing 1 to ``stap[0]`` register bit.

When the ``MMUEn`` parameter is set to 0, CV32A6 and CV64A6 are always in RISC-V **Bare** mode; ``stap[0]`` remains at 0 and writes to this register are ignored.

Notes for the integrator:

* The virtual memory is implemented by a memory management unit (MMU) that accelerates the translation from virtual memory addresses (as handled by the core) to physical memory addresses. The MMU integrates translation lookaside buffers (TLB) and a hardware page table walker (PTW). The number of instruction and data TLB entries are configured with ``InstrTlbEntries`` and ``DataTlbEntries``.

* The CV32A6 MMU will evolve with a microarchitectural optimization featuring two levels of TLB: level 1 TBL (sized by ``InstrTlbEntries`` and ``DataTlbEntries``) and a shared level 2 TLB. This optimization remains to be implemented in CV64A6. The optimization has no consequences on the programmer's view.

* The addition of the hypervisor support will come with **Sv39x4** virtual memory that is not yet documented here.

Memory Alignment
----------------
CVA6 does not support non-aligned memory accesses.

