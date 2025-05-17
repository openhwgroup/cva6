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
   Description   : HPDcache Overview

Overview
========

This HPDcache is the responsible for serving data accesses issued by a RISC-V core, tightly-coupled accelerators and hardware memory prefetchers.
All these "clients" are called requesters.

The HPDcache implements a hardware pipeline capable of serving one request per cycle.
An arbiter in the requesters’ interface of the HPDcache guarantees the correct behavior when there are multiple requesters.
This is illustrated in :numref:`Figure %s <fig_request_arbiter>`.

.. _fig_request_arbiter:

.. figure:: images/hpdcache_highlevel_integration.*
   :alt: High-Level View of the HPDcache Sub-System
   :align: center
   :width: 90%

   High-Level View of the HPDcache Sub-System

List of features
----------------

- Support for multiple outstanding requests per requester.

- Support for multiple outstanding read misses and writes to memory.

- Processes one request per cycle.

- Any given requester can access 1 to 32 bytes of a cacheline per cycle.

- Reduced energy consumption by limiting the number of RAMs consulted per
  request.

- Fixed priority arbiter between requesters: the requester port with the lowest
  index has the highest priority.

- Non-allocate, write-through policy or allocate, write-back policy. Either one
  or both are supported simultaneously at cacheline granularity.

- Hardware write-buffer to mask the latency of write acknowledgements from
  the memory system.

- Compliance with RVWMO.

- For address-overlapping transactions, the cache guarantees that these are
  committed in the order in which they are consumed from the requesters.

- For non-address-overlapping transactions, the cache may execute them in an
  out-of-order fashion to improve performance.

- Support for CMOs: cache invalidation operations, and memory fences for
  multi-core synchronisation.  Cache invalidation operations support the ones
  defined in the RISC-V CMO Standard.

- Memory-mapped CSRs for runtime configuration of the cache, status and
  performance monitoring.

- Ready-Valid, 5 channels (3 request/2 response), interface to the memory. This
  interface, cache memory interface (CMI), can be easily adapted to mainstream
  NoC interfaces like AMBA AXI [AXI2020]_.

- An adapter for interfacing with AXI5 is provided.

- External (optional), configurable, hardware, memory-prefetcher that supports
  up to 4 simultaneous prefetching streams.

