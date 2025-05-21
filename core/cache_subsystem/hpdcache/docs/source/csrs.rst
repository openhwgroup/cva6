..
   Copyright 2024 CEA*
   *Commissariat a l'Energie Atomique et aux Energies Alternatives (CEA)

   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1

   Licensed under the Solderpad Hardware License v 2.1 (the “License”); you
   may not use this file except in compliance with the License, or, at your
   option, the Apache License version 2.0. You may obtain a copy of the
   License at

   https://solderpad.org/licenses/SHL-2.1/

   Unless required by applicable law or agreed to in writing, any work
   distributed under the License is distributed on an “AS IS” BASIS, WITHOUT
   WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
   License for the specific language governing permissions and limitations
   under the License.

   Authors       : Cesar Fuguet
   Description   : HPDcache Control-Status Registers (CSRs)

.. _sec_csr:

Control-Status Registers (CSRs)
===============================

Dedicated CSR address space
---------------------------

The HPDcache defines a dedicated memory address space for configuring and
checking the internal status. This memory space is shared among all the
requesters connected to the same HPDcache. However, this space is private to
those requesters in a system-wide point of view. This is, this dedicated CSR
address space is not visible to other requesters integrated in the system.

The dedicated CSR address space is aligned to 4 Kibytes and has this same size.
Current version of the HPDcache uses a very small subset of this address space,
but the aligning to 4 Kibytes, allows easier mapping in the virtual address
space by the OS. The smallest virtual/physical page size defined in the
[RISCVP2019]_ is 4 Kibytes. :numref:`Figure %s <fig_csr_addr_space>` displays
the layout of the dedicated CSR address space of the HPDcache.

The :math:`\mathsf{CFIG\_BASE}` address is specified through an input port of
the HPDcache. The name of this input pin is ``cfig_base_i``. It is a multi-bit
signal. The number of bits is :math:`\mathsf{CONF\_HPDCACHE\_PA\_WIDTH}`. As
mentioned above, as this segment must be aligned to 4 KiB, the 12 least
significant bits must be all 0.

.. _fig_csr_addr_space:

.. figure:: images/hpdcache_csr_addr_space.*
   :alt: HPDcache CSR Dedicated Address Space
   :align: center
   :figwidth: 100%
   :width: 100%

   HPDcache CSR Dedicated Address Space


Configuration registers
-----------------------

:numref:`Table %s <tab_csr_cfg>` lists the configuration registers implemented
in the HPDcache.

These are mapped on the :math:`\mathsf{CFIG}` memory address segment
(:numref:`Figure %s <fig_csr_addr_space>`).


.. _tab_csr_cfg:

.. list-table:: Configuration Registers in the HPDcache
   :widths: 5 60 35
   :header-rows: 2

   * - **CFIG Segment**
     -
     -
   * - **Register**
     - **Description**
     - **Base address**
   * - ``cfig_version``
     - 64-bits register with cache version
     - ``cfig_base_i`` + 0x00
   * - ``cfig_info``
     - 64-bits register with cache information (part I)
     - ``cfig_base_i`` + 0x08
   * - ``cfig_info2``
     - 64-bits register with cache information (part II)
     - ``cfig_base_i`` + 0x10
   * - ``cfig_cachectrl``
     - 64-bits register to configure the cache controller
     - ``cfig_base_i`` + 0x18
   * - ``cfig_wbuf``
     - 64-bits register to configure the write buffer
     - ``cfig_base_i`` + 0x20


cfig_version
''''''''''''

.. list-table:: Configuration - Version Register
   :widths: 10 15 35 5 30
   :header-rows: 1

   * - Bits
     - Field
     - Description
     - Mode
     - Reset Value
   * - [15:0]
     - MinorID
     - Minor Version ID of the HPDcache
     - RO
     - :math:`\small\mathsf{0x0001}`
   * - [31:16]
     - MajorID
     - Major Version ID of the HPDcache
     - RO
     - :math:`\small\mathsf{0x0001}`
   * - [47:32]
     - IpID
     - IP ID of the HPDcache
     - RO
     - :math:`\small\mathsf{0x0001}`
   * - [63:48]
     - VendorID
     - Vendor ID
     - RO
     - :math:`\small\mathsf{0x0001}`


cfig_info
'''''''''

.. list-table:: Configuration - Info Register
   :widths: 10 15 35 5 30
   :header-rows: 1

   * - Bits
     - Field
     - Description
     - Mode
     - Reset Value
   * - [15:0]
     - Sets
     - Number of sets in the cache (one-based)
     - RO
     - :math:`\scriptsize\mathsf{CONF\_HPDCACHE\_SETS - 1}`
   * - [23:16]
     - Ways
     - Number of ways in the cache (one-based)
     - RO
     - :math:`\scriptsize\mathsf{CONF\_HPDCACHE\_WAYS - 1}`
   * - [27:24]
     - ClBytes
     - Number of bytes per cacheline (power of 2)
     - RO
     - :math:`\scriptsize\mathsf{log_2(CONF\_HPDCACHE\_CL\_WIDTH/8)}`
   * - [39:32]
     - MSHRSets
     - Number of sets in the MSHR (one-based)
     - RO
     - :math:`\scriptsize\mathsf{CONF\_HPDCACHE\_MSHR\_SETS - 1}`
   * - [47:40]
     - MSHRWays
     - Number of ways in the MSHR (one-based)
     - RO
     - :math:`\scriptsize\mathsf{CONF\_HPDCACHE\_MSHR\_WAYS - 1}`

cfig_info2
''''''''''

.. list-table:: Configuration - Info 2 Register
   :widths: 10 15 35 5 30
   :header-rows: 1

   * - Bits
     - Field
     - Description
     - Mode
     - Reset Value
   * - [7:0]
     - RTAB
     - Number of entries in the RTAB (one-based)
     - RO
     - :math:`\scriptsize\mathsf{CONF\_HPDCACHE\_RTAB\_ENTRIES - 1}`
   * - [23:16]
     - WBufDir
     - Number of entries in the directory of the Write Buffer (one-based)
     - RO
     - :math:`\scriptsize\mathsf{CONF\_HPDCACHE\_WBUF\_DIR\_ENTRIES - 1}`
   * - [31:24]
     - WBufData
     - Number of entries in the data buffer of the Write Buffer (one-based)
     - RO
     - :math:`\scriptsize\mathsf{CONF\_HPDCACHE\_WBUF\_DATA\_ENTRIES - 1}`
   * - [35:32]
     - WBufBytes
     - Number of bytes per Write-Buffer Data Entry (power of 2)
     - RO
     - :math:`\scriptsize\mathsf{log_2(CONF\_HPDCACHE\_WBUF\_WIDTH/8)}`


.. _sec_cfig_cachectrl:

cfig_cachectrl
''''''''''''''

.. list-table:: Configuration - Cache Controller Register
   :widths: 10 15 35 5 30
   :header-rows: 1

   * - Bits
     - Field
     - Description
     - Mode
     - Reset Value
   * - [0:0]
     - E
     - Cache Enable - When set to 0, all memory accesses are considered
       uncacheable
     - RW
     - :math:`\small\mathsf{0}`
   * - [8:8]
     - P
     - Performance Counters Enable - When set to 1, performance counter count
       events
     - RW
     - :math:`\small\mathsf{1}`
   * - [56:56]
     - R
     - Single-Entry RTAB (fallback mode) - When set to 1, the cache controller
       only uses one entry of the Replay Table.
     - RW
     - :math:`\small\mathsf{0}`


cfig_wbuf
'''''''''

.. list-table:: Configuration - Write Buffer Register
   :widths: 10 15 35 5 30
   :header-rows: 1

   * - Bits
     - Field
     - Description
     - Mode
     - Reset Value
   * - [0:0]
     - R
     - Reset time-counter on write - When set to 1, write accesses restart the
       time-counter to 0 of the used write-buffer entry
     - RW
     - :math:`\small\mathsf{1}`
   * - [1:1]
     - S
     - Sequential Write after Write - When set to 1, the write buffer stalls
       write accesses that collide with an in-flight write transaction (SENT).
     - RW
     - :math:`\small\mathsf{0}`
   * - [2:2]
     - I
     - Inhibit Write Coalescing - When set to 1, entries in the write-buffer go
       from the FREE state to the PEND state directly (bypassing the OPEN
       state). Moreover, no coalescing is accepted while the entry is in the
       PEND state.
     - RW
     - :math:`\small\mathsf{0}`
   * - [15:8]
     - T
     - Time-counter Threshold - This field defines the time-counter threshold on
       which open write-buffer entries (OPEN) go to the pending state (PEND)
     - RW
     - :math:`\small\mathsf{3}`

.. _sec_perf_counters:

Performance counters
--------------------

The HPDcache provides a set of performance counters. These counters provide
information that can be used by software developers, at OS level or
user application level, to, for example, debug performance issues.

These counters are implemented in the HPDcache only if
:math:`\scriptsize\mathsf{CONF\_HPDCACHE\_SUPPORT\_PERF}` is set to 1. If this
configuration parameter is set to 0, any read or write to performance counters
is ignored and a response with an error is sent to the corresponding requester
when ``core_req_i.need_rsp`` is set to 1.

Performance counters are incremented automatically by the hardware when the
corresponding event is triggered and the ``cfig_cachectrl.P``
(see :ref:`sec_cfig_cachectrl`) bit is set to 1.

:numref:`Table %s <tab_perf_counters>` lists the performance counters provided
by the HPDcache. These are mapped on the :math:`\mathsf{PERF}` memory address
segment (:numref:`Figure %s <fig_csr_addr_space>`).

.. _tab_perf_counters:

.. list-table:: Performance Counters in the HPDcache
   :widths: 20 50 30
   :header-rows: 1

   * - **Counter**
     - **Description**
     - **Base Address**
   * - ``perf_write_cnt``
     - 64-bit counter for processed write requests
     - ``cfg_base_i`` + 0x400
   * - ``perf_read_cnt``
     - 64-bit counter for processed read requests
     - ``cfg_base_i`` + 0x408
   * - ``perf_prefetch_cnt``
     - 64-bit counter for processed prefetch requests
     - ``cfg_base_i`` + 0x410
   * - ``perf_uncached_cnt``
     - 64-bit counter for processed uncached requests
     - ``cfg_base_i`` + 0x418
   * - ``perf_cmo_cnt``
     - 64-bit counter for processed CMO requests
     - ``cfg_base_i`` + 0x420
   * - ``perf_accepted_cnt``
     - 64-bit counter for processed requests
     - ``cfg_base_i`` + 0x428
   * - ``perf_write_miss_cnt``
     - 64-bit counter for write cache misses
     - ``cfg_base_i`` + 0x430
   * - ``perf_read_miss_cnt``
     - 64-bit counter for read cache misses
     - ``cfg_base_i`` + 0x438
   * - ``perf_onhold_cnt``
     - 64-bit counter for requests put on-hold
     - ``cfg_base_i`` + 0x440
   * - ``perf_onhold_mshr_cnt``
     - 64-bit counter for requests put on-hold because of MSHR conflicts
     - ``cfg_base_i`` + 0x448
   * - ``perf_onhold_wbuf_cnt``
     - 64-bit counter for requests put on-hold because of WBUF conflicts
     - ``cfg_base_i`` + 0x450
   * - ``perf_onhold_rollback_cnt``
     - 64-bit counter for requests put on-hold (again) after a rollback
     - ``cfg_base_i`` + 0x458
   * - ``perf_stall_cnt``
     - 64-bit counter for stall cycles (cache does not accept a request)
     - ``cfg_base_i`` + 0x460
