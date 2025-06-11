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
   Description   : HPDcache Cache Management Operations (CMOs)

.. _sec_cmo:

Cache Management Operations (CMOs)
==================================

The HPDcache is able of performing the following Cache Management Operations
(CMOs):

- Memory write fence

- Invalidate a cacheline given its address

- Invalidate all cachelines

- Prefetch the cacheline indicated given its physical address

Any of the clients of the HPDCACHE can trigger one of this operation anytime by
using specific opcodes in their request (see
:numref:`Table %s <tab_cmo_optypes>`).

.. _tab_cmo_optypes:

.. list-table:: CMO Operation Types
   :widths: 25 15 60
   :align: center
   :header-rows: 1

   * - **Mnemonic**
     - **Encoding**
     - **Description**
   * - :math:`\small\mathsf{HPDCACHE\_CMO\_FENCE}`
     - :math:`\small\mathsf{0b000}`
     - Memory Write Fence
   * - :math:`\small\mathsf{HPDCACHE\_CMO\_INVAL\_NLINE}`
     - :math:`\small\mathsf{0b010}`
     - Invalidate a Cacheline given its Address
   * - :math:`\small\mathsf{HPDCACHE\_CMO\_INVAL\_ALL}`
     - :math:`\small\mathsf{0b100}`
     - Invalidate All Cachelines
   * - :math:`\small\mathsf{HPDCACHE\_CMO\_PREFETCH}`
     - :math:`\small\mathsf{0b101}`
     - Prefetch a Cacheline given its Address


The ``core_req_i.op`` must be set to ``HPDCACHE_REQ_CMO``
(see :numref:`Table %s <tab_req_op_types>`). The CMO subtype
(:numref:`Table %s <tab_cmo_optypes>`) is transferred into the
``core_req_i.size`` signal of the request.

If :math:`\scriptsize\mathsf{CONF\_HPDCACHE\_SUPPORT\_CMO}` is set to 0, the
HPDcache does not support CMOs from requesters.
See :ref:`sec_cmo_handler` for more details.

The following sections describe in detail each of the CMO operations,
and how the requests shall be encoded to trigger each of them.


Memory Write Fence
------------------

To make sure that the HPDcache accepts new requests only when all previous
writes are sent and acknowledged from the memory, a requester can issue a fence
operation. This is useful to ensure memory consistency in multi-core systems. It
may also be necessary to ensure such consistency between the core and other
peripherals with DMA capability.

The default consistency model of RISC-V is a Weak Memory Ordering (WMO) model
(RVWMO). In this model, the system is able to reorder memory transactions with
respect to the program order. There are however some constraints detailed in
[RISCVUP2019]_ and briefly described in :ref:`sec_mcrs`.

To issue a memory fence, the requester shall build the request as follows:

.. list-table:: CMO Memory Write Fence Request Formatting
   :widths: 30 50
   :align: center
   :header-rows: 1

   * - **Signal**
     - **Value**
   * - ``core_req_o.addr_offset``
     - *Don't Care*
   * - ``core_req_o.op``
     - :math:`\small\mathsf{HPDCACHE\_REQ\_CMO}`
   * - ``core_req_o.wdata``
     - *Don't Care*
   * - ``core_req_o.be``
     - *Don't Care*
   * - ``core_req_o.size``
     - :math:`\small\mathsf{HPDCACHE\_CMO\_FENCE}`
   * - ``core_req_o.sid``
     - Corresponding source ID of the requester
   * - ``core_req_o.tid``
     - Transaction ID of the request
   * - ``core_req_o.need_rsp``
     - Indicates if the requester needs an acknowledgement when the operation is
       completed.
   * - ``core_req_o.phys_indexed``
     - *Don't Care*
   * - ``core_req_o.addr_tag``
     - *Don't Care*
   * - ``core_req_o.pma.uncacheable``
     - *Don't Care*
   * - ``core_req_o.pma.io``
     - *Don't Care*
   * - ``core_req_tag_i``
     - *Don't Care*
   * - ``core_req_pma_i.uncacheable``
     - *Don't Care*
   * - ``core_req_pma_i.io``
     - *Don't Care*


As for any regular request, the request shall follow the **VALID**/**READY**
handshake protocol described in :ref:`sec_ready_valid_handshake`.

This memory fence operation has the following effects:

- All open entries in the write buffer (write requests waiting to be sent to the
  memory) are immediately closed;

- No new requests from any requester are acknowledged until all pending write
  requests in the cache have been acknowledged on the NoC interface.

When the memory fence transaction is completed, and the ``core_req_o.need_rsp``
signal was set to 1, an acknowledgement is sent to the corresponding requester.


Invalidate a Cacheline Given its Address
----------------------------------------

The program may need to invalidate cachelines to ensure cache coherency by
software. This may be needed in both multi-core systems or systems with
DMA-capable peripherals.

To invalidate a cacheline given its address, the requester shall build the
request as follows:

.. list-table:: CMO Cacheline Invalidation given its Address Request Formatting
   :widths: 30 50
   :align: center
   :header-rows: 1

   * - **Signal**
     - **Value**
   * - ``core_req_o.addr_offset``
     - Least significant bits of the address
   * - ``core_req_o.op``
     - :math:`\small\mathsf{HPDCACHE\_REQ\_CMO}`
   * - ``core_req_o.wdata``
     - *Don't Care*
   * - ``core_req_o.be``
     - *Don't Care*
   * - ``core_req_o.size``
     - :math:`\small\mathsf{HPDCACHE\_CMO\_INVAL\_NLINE}`
   * - ``core_req_o.sid``
     - Corresponding source ID of the requester
   * - ``core_req_o.tid``
     - Transaction ID of the request
   * - ``core_req_o.need_rsp``
     - Indicates if the requester needs an acknowledgement when the operation is
       completed.
   * - ``core_req_o.phys_indexed``
     - 1 if physical indexing, 0 if virtual indexing
   * - ``core_req_o.addr_tag``
     - Most significant bits of the address if ``core_req_o.phys_indexed = 1``,
       *Don't Care* otherwise
   * - ``core_req_o.pma.uncacheable``
     - *Don't Care*
   * - ``core_req_o.pma.io``
     - *Don't Care*
   * - ``core_req_tag_i``
     - Most significant bits of the address if ``core_req_o.phys_indexed = 0``,
       *Don't Care* otherwise
   * - ``core_req_pma_i.uncacheable``
     - *Don't Care*
   * - ``core_req_pma_i.io``
     - *Don't Care*


As for any regular request, the request shall follow the **VALID**/**READY**
handshake protocol (see :ref:`sec_ready_valid_handshake`).
This CMO request supports both virtual or physical indexed requests (see
:ref:`sec_vipt`).

Regarding the latency of this operation, only one cycle is needed to invalidate
the corresponding cacheline. However, if there is a pending read miss on the
target address, the HPDcache waits for the response of the read miss then
invalidates the corresponding cacheline.

If the target address is not cached, the operation does nothing.

When the invalidation transaction is completed, and the ``core_req_o.need_rsp``
signal was set to 1, an acknowledgement is sent to the corresponding requester.


Invalidate All Cachelines
-------------------------

With this operation, all the cachelines in the HPDcache are invalidated.

The requester shall build the request as follows to perform a complete
invalidation of the HPDcache:

.. list-table:: CMO All Cachelines Invalidation
   :widths: 30 50
   :align: center
   :header-rows: 1

   * - **Signal**
     - **Value**
   * - ``core_req_o.addr_offset``
     - *Don't Care*
   * - ``core_req_o.op``
     - :math:`\small\mathsf{HPDCACHE\_REQ\_CMO}`
   * - ``core_req_o.wdata``
     - *Don't Care*
   * - ``core_req_o.be``
     - *Don't Care*
   * - ``core_req_o.size``
     - :math:`\small\mathsf{HPDCACHE\_CMO\_INVAL\_ALL}`
   * - ``core_req_o.sid``
     - Corresponding source ID of the requester
   * - ``core_req_o.tid``
     - Transaction ID of the request
   * - ``core_req_o.need_rsp``
     - Indicates if the requester needs an acknowledgement when the operation is
       completed.
   * - ``core_req_o.phys_indexed``
     - *Don't Care*
   * - ``core_req_o.addr_tag``
     - *Don't Care*
   * - ``core_req_o.pma.uncacheable``
     - *Don't Care*
   * - ``core_req_o.pma.io``
     - *Don't Care*
   * - ``core_req_tag_i``
     - *Don't Care*
   * - ``core_req_pma_i.uncacheable``
     - *Don't Care*
   * - ``core_req_pma_i.io``
     - *Don't Care*


As for any regular request, the request shall follow the **VALID**/**READY**
handshake protocol (see :ref:`sec_ready_valid_handshake`).

This operation works as a memory read fence. This is, before handling the
operation, the HPDcache waits for all pending read misses to complete.

Regarding the latency of this operation, it has two aggregated components:

- The time to serve all pending reads.

- One cycle per set implemented in the HPDcache (all ways of a given set are
  invalidated simultaneously).

When the invalidation transaction is completed, and the ``core_req_o.need_rsp``
signal was set to 1, an acknowledgement is sent to the corresponding requester.


Prefetch a Cacheline given its Address
--------------------------------------

With this operation, the cacheline corresponding to the indicated address is
prefetched into the HPDcache.

The requester shall build the request as follows to perform a prefetch:

.. list-table:: CMO All Cachelines Invalidation
   :widths: 30 50
   :align: center
   :header-rows: 1

   * - **Signal**
     - **Value**
   * - ``core_req_o.addr_offset``
     - Least significant bits of the address
   * - ``core_req_o.op``
     - :math:`\small\mathsf{HPDCACHE\_REQ\_CMO}`
   * - ``core_req_o.wdata``
     - *Don't Care*
   * - ``core_req_o.be``
     - *Don't Care*
   * - ``core_req_o.size``
     - :math:`\small\mathsf{HPDCACHE\_CMO\_PREFETCH}`
   * - ``core_req_o.sid``
     - Corresponding source ID of the requester
   * - ``core_req_o.tid``
     - Transaction ID of the request
   * - ``core_req_o.need_rsp``
     - Indicates if the requester needs an acknowledgement when the operation is
       completed.
   * - ``core_req_o.phys_indexed``
     - 1 if physical indexing, 0 if virtual indexing
   * - ``core_req_o.addr_tag``
     - Most significant bits of the address if ``core_req_o.phys_indexed = 1``,
       *Don't Care* otherwise
   * - ``core_req_o.pma.uncacheable``
     - *Don't Care*
   * - ``core_req_o.pma.io``
     - *Don't Care*
   * - ``core_req_tag_i``
     - Most significant bits of the address if ``core_req_o.phys_indexed = 0``,
       *Don't Care* otherwise
   * - ``core_req_pma_i.uncacheable``
     - *Don't Care*
   * - ``core_req_pma_i.io``
     - *Don't Care*


As for any regular request, the request shall follow the **VALID**/**READY**
handshake protocol (see :ref:`sec_ready_valid_handshake`). This CMO request
supports both virtual or physical indexed requests (see :ref:`sec_vipt`).

If the requested cacheline is already in the cache this request has no effect.
If the requested cacheline is not present in the cache, the cacheline is fetched
from the memory and replicated into the cache.

When the prefetch transaction is completed, and the ``core_req_o.need_rsp``
signal was set to 1, an acknowledgement is sent to the corresponding requester.
