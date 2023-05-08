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

.. _cva6_csr_performance_counters:

CSR performance counters control
================================
CVA6 implements performance counters according to the RISC-V Privileged Specification, version 1.11 (see Hardware Performance Monitor, Section 3.1.10). The performance counters are placed inside the Control and Status Registers(CSRs) and can be accessed with the                               instructions.

CVA6 implements the standard clock cycle counter ``mcycle`` ,the retired instruction counter ``minstret`` as well as the six generic event counters ``mhpm_counter_3`` to ``mhpm_counter_8`` including their upper 32 bits counterparts ``mhpm_counter_3h`` to  ``mhpm_counter_8h``. The corresponding event selectors ``mhpm_event_3`` to ``mhpm_event_8`` are implemented for the selection of the source of events. 

The mcountinhibit CSR is used to individually inhibit the incrementing of the counters. The read-only shadows of the counters are also implemented as ``cycle``, ``instret`` and ``hpmcountern``. The ``mcycle`` and ``minstret`` counters are always available but the ``mhpmcounter`` are optional and can be configured through the parameter ``PERF_COUNTER_EN``. The supervisor and user access of performance counters are allowed through enabling of ``mcounteren`` and ``scounteren`` CSRs respectively.

Event Selector
-------------------------------
The five least significant bit of the event selector CSRs ``mhpm_event_3`` to ``mhpm_event_8`` controls which of the events are counted by the six generic event counters ``mhpm_counter_3`` to ``mhpm_counter_8`` respectively. Each of the six generic performance counters is able to monitor events from one of these sources:

+----------+-----------------------------+---------------------------------------------------------------+
| Event ID |         Event Name          |                          Description                          |
+==========+=============================+===============================================================+
|    1     |      L1 I-Cache Misses      |                Number Of Misses In L1 I-Cache                 |
+----------+-----------------------------+---------------------------------------------------------------+
|    2     |      L1 D-Cache Misses      |                Number Of Misses In L1 D-Cache                 |
+----------+-----------------------------+---------------------------------------------------------------+
|    3     |         ITLB Misses         |                   Number Of Misses In ITLB                    |
+----------+-----------------------------+---------------------------------------------------------------+
|    4     |         DTLB Misses         |                   Number Of Misses In DTLB                    |
+----------+-----------------------------+---------------------------------------------------------------+
|    5     |        Load Accesses        |                  Number Of Data Memory Loads                  |
+----------+-----------------------------+---------------------------------------------------------------+
|    6     |       Store Accesses        |                 Number Of Data Memory Stores                  |
+----------+-----------------------------+---------------------------------------------------------------+
|    7     |         Exceptions          |                 Valid Exceptions encountered                  |
+----------+-----------------------------+---------------------------------------------------------------+
|    8     |  Exception Handler Returns  |                   Return from an exception                    |
+----------+-----------------------------+---------------------------------------------------------------+
|    9     |     Branch Instructions     |           Number of Branch instructions encountered           |
+----------+-----------------------------+---------------------------------------------------------------+
|    10    |     Branch Mispredicts      |                Number of branch mispredictions                |
+----------+-----------------------------+---------------------------------------------------------------+
|    11    |      Branch Exceptions      |               Number of valid Branch exceptions               |
+----------+-----------------------------+---------------------------------------------------------------+
|    12    |            Call             |                  Number of Call instructions                  |
+----------+-----------------------------+---------------------------------------------------------------+
|    13    |           Return            |                 Number of Return Instructions                 |
+----------+-----------------------------+---------------------------------------------------------------+
|    14    |          MSB Full           |                      Scoreboard is full                       |
+----------+-----------------------------+---------------------------------------------------------------+
|    15    |   Instruction Fetch Empty   |             Number of invalid instructions in IF              |
+----------+-----------------------------+---------------------------------------------------------------+
|    16    |     L1 I-Cache Accesses     |            Number of accesses to Instruction Cache            |
+----------+-----------------------------+---------------------------------------------------------------+
|    17    |     L1 D-Cache Accesses     |               Number of accesses to Data Cache                |
+----------+-----------------------------+---------------------------------------------------------------+
|    18    |   L1 Cache Line Eviction    |              Number of  Data Cache line eviction              |
+----------+-----------------------------+---------------------------------------------------------------+
|    19    |         ITLB Flush          |                    Number of ITLB Flushes                     |
+----------+-----------------------------+---------------------------------------------------------------+
|    20    |    Integer Instructions     |                Number of Integer instructions                 |
+----------+-----------------------------+---------------------------------------------------------------+
|    21    | Floating Point Instructions |             Number of Floating point instructions             |
+----------+-----------------------------+---------------------------------------------------------------+
|    22    |       Pipeline Stall        | Number of cycles the pipeline is stalled during read operands |
+----------+-----------------------------+---------------------------------------------------------------+
|  23-31   |          Reserved           |                           Reserved                            |
+----------+-----------------------------+---------------------------------------------------------------+



