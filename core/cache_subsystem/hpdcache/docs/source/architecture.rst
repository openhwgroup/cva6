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
   Description   : HPDcache Architecture

Architecture
============

:numref:`Figure %s <fig_architecture_hpdcache_core>` depicts a global view of
the HPDcache (core partition that does not include the request arbitration). On
the upper part of the cache there is the interface from/to requesters. On the
bottom part there is the interface from/to the memory.

.. _fig_architecture_hpdcache_core:

.. figure:: images/hpdcache_core.*
   :alt: HPDcache core
   :align: center
   :width: 100%

   HPDcache core

Cache Controller
----------------

The cache controller is responsible for decoding and issuing the requests to the
appropriate handler. The cache controller implements a 3-stage pipeline. This
pipeline is capable of accepting one request per cycle. However, there are some
scenarios where the pipeline may either stall or put a request on hold in a side
buffer called Replay Table (RTAB).

The first stage (stage 0) of the pipeline arbitrates between requests from the
miss handler (refill), RTAB, and requesters; the second stage (stage 1) responds
to loads (in case of hit) and to stores; the third stage (stage 2) is only used
by loads in case of miss. In this last stage, the cache triggers a read miss
transaction to the memory and allocates a new entry in the Miss Status Holding
Register (MSHR) to track the progress of the miss transaction.

A request on stage 0 can either be consumed on that cycle (forwarded to the
stage 1) or stalled. A request on stage 1 or stage 2 always progresses. In stage
1 the request is either acknowledged (load hit or write acknowledgement),
forwarded to stage 2 (load miss), or put into the RTAB. In stage 2, the request
quits the pipeline and it is written in the MSHR.

The arbiter in stage 0 uses a fixed-priority policy: refills have the higher
priority, followed by the RTAB, and finally core request (lower priority).

Pipeline Stalls in Stage 0
''''''''''''''''''''''''''

Stalls in stage 0 are necessary in some specific scenarios, that are listed
below. When there is a stall in stage 0, a new request from a requester cannot
be accepted, this is, the corresponding :math:`\mathsf{ready}` signal is kept
low (set to 0). Requests in the other stages (1 and 2) are processed normally
(even in case of a stall in stage 0).

.. list-table:: Events that Stall the Pipeline
   :widths: 5 50 40
   :header-rows: 1
   :align: center

   * - Event
     - Description
     - Stall Latency (Clock Cycles)
   * - **1**
     - The RTAB is full
     - It depends on when an entry of the RTAB is freed
   * - **2**
     - A CMO invalidation or fence operation is being processed by the
       corresponding handler
     - It depends on the latency of the operation
   * - **3**
     - An uncacheable or atomic operation is being processed by the
       corresponding handler
     - It depends on the latency of the operation
   * - **4**
     - There is a load miss in stage 1
     - One cycle
   * - **5**
     - There is a store in stage 1 and the request in stage 0 is a load
       (structural hazard on access to the internal cache data memory)
     - One cycle

.. _sec_onhold:

On-Hold Requests
''''''''''''''''

In some scenarios, a request that has been accepted in the pipeline can be
later put on-hold by the cache controller. The cache controller puts a request
on-hold by removing it from the cache pipeline and writing it into the Replay
Table (RTAB). When a request is put on-hold, it is re-executed when all the
blocking conditions have been removed. The blocking conditions putting a
request on-hold are the following:

.. _tab_onhold:

.. list-table:: Conditions Putting a Request On-hold
   :widths: 3 37 60
   :header-rows: 1

   * - #
     - Condition
     - Description
   * - **1**
     - **Cacheable LOAD or PREFETCH, and there is a hit on a pending miss (hit
       on the MSHR)**
     - When there is a read miss on a given cacheline for which there is a
       pending read miss, then the more recent one needs to wait for the
       previous one to be served. This allows the latest one to read the data
       from the cache after the refill operation completes. More importantly,
       this frees the pipeline to accept the corresponding refill and prevent a
       deadlock.
   * - **2**
     - **Cacheable LOAD or PREFETCH, there is a miss on the cache, and there is
       a hit (cacheline granularity) on an opened, pending or sent entry of the
       WBUF**
     - When there is a read miss on an address, the cache controller needs to
       read from the memory the missing cacheline. As the NoC implements
       different physical channels for read and write requests, there is a race
       condition between the read miss and a pending write operation.  If the
       read miss arrives first to the memory, it would read the old data (which
       violates :ref:`sec_mcrs`). This blocking condition causes that the LOAD
       or PREFETCH will have a delay penalty of up to two transaction delays:
       one for the write to complete, then one for the read.
   * - **3**
     - **Cacheable STORE, there is a miss on the cache, and there is a hit on a
       pending miss (hit on the MSHR)**
     - When writing, as the NoC implements different physical channels for read
       and write requests, there is a race condition between the STORE and the
       pending read miss. If the STORE arrives first to the memory, the earlier
       read miss would read the new data (which violates :ref:`sec_mcrs`).
   * - **4**
     - **Cacheable LOAD/PREFETCH/STORE, and there is a hit on an entry of the
       RTAB**
     - Accesses to the same cacheline SHALL be processed in order (to respect
       :ref:`sec_mcrs`). In case of a hit with a valid entry in the RTAB, the
       new request shall wait for previous requests on the same cacheline to
       finish.
   * - **5**
     - **Cacheable LOAD or PREFETCH, there is a miss on the cache, and the MSHR
       has no available slots**
     - When there is a read miss on an address, the cache controller needs to
       allocate a new entry in the MSHR. If there is no available entry, the
       read request needs to wait for an entry in the MSHR to be freed. This
       frees the pipeline to accept the corresponding refill and prevent a
       deadlock.
   * - **6**
     - **Cacheable LOAD or PREFETCH, there is a miss on the cache, and the miss
       handler FSM cannot send the read miss request**
     - When there is a read miss on an address, the cache controller needs to
       read from memory the missing cacheline. The read miss request is sent by
       the miss handler FSM, but if there is congestion in the NoC, this read
       request cannot be issued. This frees the pipeline to prevent a potential
       deadlock.

The cache controller checks all these conditions in the second stage (stage 1)
of the pipeline. If one of the conditions is met, the cache controller puts the
request into the RTAB and holds it there until its blocking condition is
resolved. At that moment, the cache can replay the request from the RTAB.

The RTAB can store multiple on-hold requests. The idea is to improve the
throughput of the cache by reducing the number of cases where there is a head
of line blocking at the client interface. As mentioned in
:numref:`Table %s <tab_onhold>`, this also prevents deadlocks. To always allow
the cache controller to retire a request from the pipeline, the cache controller
does not accept new requests if the RTAB is full.

Requests from the RTAB may be executed in an order that is different from
the order in which they were accepted (if they target different cachelines).
The requests, that target the same cacheline, are replayed by the RTAB in the
order they were accepted.

Requests within the RTAB that have their dependencies resolved may be replayed.
These have higher priority than the new requests from requesters.


.. _sec_mcrs:

Memory Consistency Rules (MCRs)
'''''''''''''''''''''''''''''''

The cache controller processes requests following a set of Memory Consistency
Rules (MCRs). These rules allow the requesters to have a predictable behavior.

The set MCRs respected by the cache controller are those defined by the RISC-V
Weak Memory Ordering (RVWMO) memory consistency model. [RISCVUP2019]_ specifies
this model. The following statement summarizes these rules: **if one memory
access (read or write), A, precedes another memory access (read or write), B,
and they access overlapping addresses, then they MUST be executed in program
order (A then B)**. It can be deduced from this statement, that non-overlapping
accesses can be executed in any order.

The cache controller also needs to respect the progress axiom: **no memory
operation may be preceded by an infinite number of memory operations**. That
is, all memory operations need to be processed at some point in time. They
cannot wait indefinitely.

Hybrid Write-Policy
'''''''''''''''''''

The HPDcache can handle writes in both write-back and write-through policies.
The HPDcache handles the write policy at cacheline granularity. This means that
at any given time, the HPDcache has two logical subsets of cachelines: one
subset containing cachelines in write-back policy, and another subset
containing cachelines in write-through policy. Any of these two subsets may be
empty, meaning that all cachelines may be either write-back or write-through.

If only one write-policy is required, the system designer can:

  - Disable the write-back policy setting to 0 the ``CONF_HPDCACHE_WB_ENABLE``
    parameter.

  - Disable the write-through policy setting to 0 the ``CONF_HPDCACHE_WT_ENABLE``
    parameter.

When both write-policies are enabled, the request interface may set dynamically
the write-policy (write-back or write-through) for the target cacheline. In the
request interface, there are specific flags (hints) to indicate the desired
policy for a given request.

The HPDcache keeps the policy for subsequent accesses until a request/response
force it to a specific policy. It accepts policy changes for any cacheline.
This is, a request/response may ask for write-back policy (respectively
write-through) for a given cacheline, and another request/response may ask for
write-through policy (respectively write-back) for that same cacheline later.


Cache Directory and Data
------------------------

State Bits in the Cache Directory
'''''''''''''''''''''''''''''''''

Each cacheline in the HPDcache has the following state bits:

  - **valid**: when this bit is set, it means that the cacheline is valid.
    Otherwise, the slot is available.
  - **wback**: when this bit is set, it means that the cacheline is in
    write-back mode. It is only valid when the valid bit is set.
  - **dirty**: when this bit is set, it means that the cacheline is in
    write-back mode and it is dirty (it has locally modified data which has not
    been transmitted to the next memory level). It is only valid when the valid
    bit is set.
  - **fetch**: when this bit is set, it means that the cacheline has been
    pre-selected to be replaced by a new one. While this bit is set, the refill
    response for the miss has not yet arrived.

Replacement Policy
''''''''''''''''''

The HPDcache supports the following two replacement policies: Pseudo Random or
Pseudo Least Recently Used (PLRU) replacement policy. The user selects the
actual policy at synthesis-time through the
:math:`\scriptsize\mathsf{CONF\_HPDCACHE\_VICTIM\_SEL}`
configuration parameter (:numref:`Table %s <tab_synthesis_parameters>`).

The cache uses the selected policy to select the victim way where a new
cacheline is written. In case of a read miss, CMO prefetch miss or a write miss
with the write-back policy the cache controller applies the replacement policy
to select the way of the corresponding set where the miss handler will write
the new cacheline.

The cache selects the victim way at the moment of a cache miss. At that moment,
it also asks for the missing cacheline to the memory. While waiting for the
refill response, the victim cacheline is still accessible but in **fetch** mode
(fetch bit set). This means that it has been pre-selected for replacement, and
cannot be a candidate for victim selection for a future miss (until the refill
response does not arrive).


Pseudo Least Recently Used (PLRU)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This replacement policy requires one state bit per cacheline in the cache. This
bit is named Least Recently Used (LRU) state. All LRU bits are set to 0 on
reset. They are then updated at each read, CMO prefetch, store and atomic
operation from the requesters.

The following code snippet shows the declaration of the array containing the
LRU bits. As explained before, there are as many bits as cachelines in the
cache. Therefore the LRU bits are organized as a 2D (two-dimensions) array of
:math:`\mathsf{CONF\_HPDCACHE\_SETS}` and
:math:`\mathsf{CONF\_HPDCACHE\_WAYS}` bits.

.. code:: c

   //  2D array containing LRU state bits
   bool lru[CONF_HPDCACHE_SETS][CONF_HPDCACHE_WAYS];


The following code snippet illustrates the algorithm (``update_plru`` function)
that the cache controller uses to update PLRU bits. This function is used by
read, CMO prefetch, write and atomic requests from requesters. The cache
controller first checks for a hit in any way of the set designated by the
request address. If there is a hit, the cache controller applies the
``update_plru`` algorithm on the corresponding set and way. In the case of a
miss, the cache controller first selects a victim way, then during the refill,
the miss handler applies the ``update_plru`` algorithm.

.. code:: c

   void update_plru(int set, int way)
   {
      //  set the LRU bit of the target set and way
      lru[set][way] = true;

      //  check if all LRU bits of the target "set" contain 1
      for (int w = 0; w < HPDCACHE_WAYS; w++) {
         //  If there is at least one 0, the update is done
         if (!lru[set][w]) return;
      }

      //  If all LRU bits are set to 1, reset to 0 the LRU bits of all the ways
      //  except the one being accessed
      for (int w = 0; w < HPDCACHE_WAYS; w++) {
         if (w != way) lru[set][w] = false;
      }
   }


The following code snippet illustrates the algorithm (``select_victim_way``
function) that the cache controller uses to select a victim way on a cache
miss. In summary, the victim way is either the first way (starting from way
0) where the valid bit is 0, or the first way where the LRU bit is unset.
In the case where the way with the LRU bit unset is being fetched (fetch bit
set), the controller selects one of the ways which is not being fetched, giving
the highest priority to clean ways (no local modification in case of write-back
policy). If all ways are pre-selected (being fetched by a previous miss), the
cache controller cannot select a victim, and puts the new miss request into the
replay table.

.. code:: c

   int select_victim_way(int set)
   {
      //  Return the first way (of the target set) whose valid bit is unset
      for (int w = 0; w < HPDCACHE_WAYS; w++) {
         if (!valid[set][w]) {
            return w;
         }
      }

      //  If all ways are valid, return the first way (of the target set) whose
      //  PLRU bit is unset and which is not pre-selected as victim
      for (int w = 0; w < HPDCACHE_WAYS; w++) {
         if (!fetch[set][w] && !lru[set][w]) {
            return w;
         }
      }

      //  If the PLRU designated way cannot be selected (already pre-selected
      //  as victim), return the first clean way (no locally modified in case
      //  of write-back policy)
      for (int w = 0; w < HPDCACHE_WAYS; w++) {
         if (!fetch[set][w] && !dirty[set][w]) {
            return w;
         }
      }

      //  If there is no clean way selectable, return the first dirty way
      for (int w = 0; w < HPDCACHE_WAYS; w++) {
         if (!fetch[set][w]) {
            return w;
         }
      }

      // If there is no selectable way (all ways are being already pre-selected
      // and are waiting for a refill) returns -1. In this case the cache
      // controller puts the miss request on hold in the replay table.
      return -1;
   }


Pseudo Random
~~~~~~~~~~~~~

This replacement policy requires only one 8-bit Linear Feedback Shift Register
(LFSR).

Each time there is a miss (read, CMO prefetch, write in write-back mode), the
cache controller selects either a free way (valid bit is set to 0), or a way
designated by the value in the LFSR. If the random way is in **fetch** mode,
then the cache controller selects the first way which is not in **fetch** mode,
giving the highest priority to clean ways. If all ways are in **fetch** mode,
then the request is put on-hold in the replay table. Each time the cache
controller uses the pseudo random value, it performs a shift of the LFSR.

This pseudo random policy has a lower area footprint than the PLRU policy
because it only uses a 8-bit LFSR (independently of the number of cachelines in
the cache). The PLRU policy requires one bit per cacheline in the cache.
However, some applications may exhibit lower performance with the pseudo random
replacement policy as locality is not considered while selecting the victim.


RAM Organization
''''''''''''''''

The HPDcache cache uses SRAM macros for the directory and data parts of the
cache. These RAM macros are synchronous, read/write, single-port RAMs.

The organization of the RAMs, for the directory and the data, targets the
following:

#. **High memory bandwidth to/from the requesters**

   The organization allows to read 1, 2, 4, 8, 16, 32 or 64 bytes per cycle. The
   maximum number of bytes per cycle is a configuration parameter of the cache.
   Read latency is one cycle.

#. **Low energy-consumption**

   To limit the energy-consumption, the RAMs are organized in a way that the
   cache enables only a limited number of RAM macros. This number depends on the
   number of requested bytes, and it also depends on the target technology.
   Depending on the target technology, the RAM macros have different trade-offs
   between width, depth and timing (performance).

#. **Small RAM footprint**

   To limit the footprint of RAMs, the selected organization looks to implement
   a small number of RAMs macros. The macros are selected in a way that they are
   as deep and as wide as possible. The selected ratios (depth and width) depend
   on the target technology node.

.. _sec_cache_ram_organization:

RAM Organization Parameters
'''''''''''''''''''''''''''

The HPDcache provides a set of parameters to tune the organization of the SRAM
macros. These parameters allow to adapt the HPDcache to the Performance, Power
and Area (PPA) requirements of the system.

The cache directory and data are both implemented using SRAM macros.

Cache Directory Parameters
~~~~~~~~~~~~~~~~~~~~~~~~~~

The cache directory contains the metadata that allows to identify the cachelines
which are present in the cache.

Each entry contains the following information:

.. list-table::
   :widths: 5 15 80
   :header-rows: 1

   * - Field
     - Description
     - Width (in bits)
   * - V
     - Valid
     - :math:`\mathsf{1}`
   * - W
     - Write-back (wback)
     - :math:`\mathsf{1}`
   * - D
     - Dirty
     - :math:`\mathsf{1}`
   * - F
     - Fetch
     - :math:`\mathsf{1}`
   * - T
     - Cache Tag
     - :math:`\mathsf{HPDCACHE\_NLINE\_WIDTH - HPDCACHE\_SET\_WIDTH}`

The depth of the macros is:

   :math:`\mathsf{CONF\_HPDCACHE\_SETS}`.

The width (in bits) of the macros is:

   :math:`\mathsf{4 + T}` bits.

Finally, the total number of SRAM macros for the cache directory is:

   :math:`\text{SRAM macros} = \mathsf{CONF\_HPDCACHE\_WAYS}`


.. admonition:: Possible Improvement
   :class: note

   Allow to split sets in different RAMs as for the cache data
   (:math:`\mathsf{CONF\_HPDCACHE\_DATA\_SETS\_PER\_RAM}`).

.. admonition:: Possible Improvement
   :class: note

   Allow to put ways side-by-side as for the cache data
   (:math:`\mathsf{CONF\_HPDCACHE\_DATA\_WAYS\_PER\_RAM\_WORD}`).

Cache Data Parameters
~~~~~~~~~~~~~~~~~~~~~

The depth of the macros is:

   :math:`\mathsf{\lceil\frac{CONF\_HPDCACHE\_CL\_WORDS}{CONF\_HPDCACHE\_ACCESS\_WORDS}\rceil{}\times{}CONF\_HPDCACHE\_DATA\_SETS\_PER\_RAM}`

Multiple ways, for the same set, can be put side-by-side in the same SRAM word:

   :math:`\mathsf{CONF\_HPDCACHE\_DATA\_WAYS\_PER\_RAM\_WORD}`

The width (in bits) of the macros is:

.. math::

   \mathsf{CONF\_HPDCACHE\_DATA\_WAYS\_PER\_RAM\_WORD}\\
   \mathsf{\times{}CONF\_HPDCACHE\_WORD\_WIDTH}

Finally, the total number of SRAM macros is:

.. math::

   \mathsf{W}         &= \mathsf{CONF\_HPDCACHE\_DATA\_WAYS}\\
   \mathsf{WR}        &= \mathsf{CONF\_HPDCACHE\_DATA\_WAYS\_PER\_RAM\_WORD}\\
   \mathsf{S}         &= \mathsf{CONF\_HPDCACHE\_DATA\_SETS}\\
   \mathsf{SR}        &= \mathsf{CONF\_HPDCACHE\_DATA\_SETS\_PER\_RAM}\\
   \mathsf{A}         &= \mathsf{CONF\_HPDCACHE\_ACCESS\_WORDS}\\
   \text{SRAM macros} &= \mathsf{A{}\times{}\lceil\frac{W}{WR}\rceil{}\times{}\lceil\frac{S}{SR}\rceil}

The :math:`\mathsf{CONF\_HPDCACHE\_ACCESS\_WORDS}` defines the maximum number of
words that can be read or written in the same clock cycle. This parameter
affects both the refill latency and the maximum throughput (bytes/cycle) between
the HPDcache and the requesters.

Here the refill latency is defined as the number of clock cycles that the miss
handler takes to write into the cache the cacheline data once the response of a
read miss request arrives. It does not consider the latency to receive the data
from the memory because this latency is variable and depends on the system. The
following formula determines the refill latency (in clock cycles) in the
HPDcache:

   :math:`\mathsf{max(2, \frac{CONF\_HPDCACHE\_CL\_WORDS}{CONF\_HPDCACHE\_ACCESS\_WORDS})}`

The following formula determines the maximum throughput (bytes/cycle) between
the HPDcache and the requesters:

   :math:`\mathsf{\frac{CONF\_HPDCACHE\_ACCESS\_WORDS{}\times{}CONF\_HPDCACHE\_WORD\_WIDTH}{8}}`

.. admonition:: Caution
   :class: caution

   The choice of the :math:`\mathsf{CONF\_HPDCACHE\_ACCESS\_WORDS}` parameter is
   important. It has an impact on performance because it determines the refill
   latency and the request throughput. It also has an impact on the area because
   the depth of SRAM macros depends on this parameter. Finally, it has an impact
   on the timing (thus performance) because the number of inputs of the data
   word selection multiplexor (and therefore the number of logic levels) also
   depends on this parameter.

   As a rule of thumb, timing and area improves with smaller values of this
   parameter. Latency and throughput improves with bigger values of this
   parameter. The designer needs to choose the good tradeoff depending on the
   target system.


Example cache data/directory RAM organization
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

:numref:`Figure %s <fig_data_ram_organization_example>` illustrates a possible
organization of the RAMs. The illustrated organization allows to implement 32
KB of data cache (128 sets, 4 ways and 64-byte cachelines). The corresponding
parameters of this organization are the following:

.. list-table::
   :widths: 40 60
   :header-rows: 1

   * - **Parameter**
     - **Value**
   * - :math:`\mathsf{CONF\_HPDCACHE\_SETS}`
     - 128
   * - :math:`\mathsf{CONF\_HPDCACHE\_WAYS}`
     - 4
   * - :math:`\mathsf{CONF\_HPDCACHE\_WORD\_WIDTH}`
     - 64
   * - :math:`\mathsf{CONF\_HPDCACHE\_CL\_WORDS}`
     - 8
   * - :math:`\mathsf{CONF\_HPDCACHE\_ACCESS\_WORDS}`
     - 4
   * - :math:`\mathsf{CONF\_HPDCACHE\_DATA\_SETS\_PER\_RAM}`
     - 128
   * - :math:`\mathsf{CONF\_HPDCACHE\_DATA\_WAYS\_PER\_RAM\_WORD}`
     - 2


.. _fig_data_ram_organization_example:

.. figure:: images/hpdcache_data_ram_organization.*
   :alt: HPDcache RAM Organization Example
   :align: center

   HPDcache RAM Organization Example

This example organization has the following characteristics:

.. list-table::
   :widths: 25 75
   :header-rows: 0

   * - **Refilling Latency**
     - Two clock cycles. The cache needs to write two different entries on a
       given memory cut
   * - **Maximum Request Throughput (bytes/cycle)**
     - 32 bytes/cycle. Requesters can read 1, 2, 4, 8, 16 or 32 bytes of a given
       cacheline per cycle.
   * - **Energy Consumption**
     - It is proportional to the number of requested bytes. Accesses requesting
       1 to 8 bytes need to read two memory cuts (one containing ways 0 and 1,
       and the other containing ways 2 and 3); accesses requesting 8 to 16 bytes
       need to read 4 memory cuts; accesses requesting 24 to 32 bytes need to
       access all the cuts at the same time (8 cuts).


Miss Handler
------------

This block is in charge of processing read miss requests to the memory. It has
three parts:

#. One in charge of forwarding read miss requests to the memory

#. One in charge of tracking the status of in-flight read misses

#. One in charge of selecting a victim cacheline and updating the cache with
   the response data from the memory

Multiple-entry MSHR
'''''''''''''''''''

The miss handler contains an essential component of the HPDcache: the
set-associative multi-entry MSHR. This components is the one responsible of
tracking the status of in-flight read miss requests to the memory. Each entry
of contains the status for each in-flight read miss request. Therefore, the
number of entries in the MSHR defines the maximum number of in-flight read miss
requests.

The number of entries in the MSHR depends on two configuration values:
:math:`\mathsf{CONF\_HPDCACHE\_MSHR\_WAYS}`
and
:math:`\mathsf{CONF\_HPDCACHE\_MSHR\_SETS}`.
The number of entries is computed as follows:

.. math:: \mathsf{CONF\_HPDCACHE\_MSHR\_SETS~\times~CONF\_HPDCACHE\_MSHR\_WAYS}

The MSHR accepts the following configurations:

.. list-table:: MSHR Configurations
   :widths: 20 20 60
   :header-rows: 1

   * - MSHR Ways
     - MSHR Sets
     - Configuration
   * - :math:`\mathsf{= 1}`
     - :math:`\mathsf{= 1}`
     - Single-Entry
   * - :math:`\mathsf{> 1}`
     - :math:`\mathsf{= 1}`
     - Fully-Associative Array
   * - :math:`\mathsf{= 1}`
     - :math:`\mathsf{> 1}`
     - Direct Access Array
   * - :math:`\mathsf{> 1}`
     - :math:`\mathsf{> 1}`
     - Set-Associative Access Array


A high number of entries in the MSHR allows to overlap multiple accesses to the
memory and hide its latency. Of course, the more entries there are, the more
silicon area the MSHR takes. Therefore, the system architect must choose the
MSHR parameters depending on a combination of memory latency, memory
throughput, area and performance. The system architecture must also consider
the capability of requesters to issue multiple read transactions.

An entry in the MSHR contains the following information:

.. list-table::
   :widths: 5 15 80
   :header-rows: 1

   * - Field
     - Description
     - Width (in bits)
   * - T
     - MSHR Tag
     - :math:`\mathsf{HPDCACHE\_NLINE\_WIDTH - log_2(CONF\_HPDCACHE\_MSHR\_SETS)}`
   * - R
     - Request ID
     - :math:`\mathsf{CONF\_HPDCACHE\_REQ\_TRANS\_ID\_WIDTH}`
   * - S
     - Source ID
     - :math:`\mathsf{CONF\_HPDCACHE\_REQ\_SRC\_ID\_WIDTH}`
   * - W
     - Word Index
     - :math:`\mathsf{log_2(CONF\_HPDCACHE\_CL\_WORDS})`
   * - N
     - Need Response
     - 1

MSHR Implementation
'''''''''''''''''''

In order to limit the area cost, the MSHR can be implemented using SRAM
macros. SRAM macros have higher bit density than flip-flops.

The depth of the macros is:

   :math:`\mathsf{CONF\_HPDCACHE\_MSHR\_SETS\_PER\_RAM}`

Multiple ways, for the same set, can be put side-by-side in the same SRAM word:

   :math:`\mathsf{CONF\_HPDCACHE\_MSHR\_WAYS\_PER\_RAM\_WORD}`

The width (in bits) of the macros is:

   :math:`\mathsf{CONF\_HPDCACHE\_MSHR\_WAYS\_PER\_RAM\_WORD{}\times{}(T + R + S + W + 1)}`

Finally, the total number of SRAM macros is:

.. math::

   \mathsf{W}         &= \mathsf{CONF\_HPDCACHE\_MSHR\_WAYS}\\
   \mathsf{WR}        &= \mathsf{CONF\_HPDCACHE\_MSHR\_WAYS\_PER\_RAM\_WORD}\\
   \mathsf{S}         &= \mathsf{CONF\_HPDCACHE\_MSHR\_SETS}\\
   \mathsf{SR}        &= \mathsf{CONF\_HPDCACHE\_MSHR\_SETS\_PER\_RAM}\\
   \text{SRAM macros} &= \mathsf{\lceil\frac{W}{WR}\rceil{}\times{}\lceil\frac{S}{SR}\rceil}

SRAM macros shall be selected depending on the required number of entries, and
the target technology node.

When the number of entries is low
(e.g. :math:`\mathsf{MSHR\_SETS \times MSHR\_WAYS \le 16}`),
it is generally better to implement the MSHR using flip-flops. In such
configurations, the designer may use a fully-associative configuration to
remove associativity conflicts.


MSHR Associativity Conflicts
''''''''''''''''''''''''''''
The MSHR implements a set-associative organization. In such organization, the
target "set" is designated by some bits of the cacheline address.

If there are multiple in-flight read miss requests addressing different
cachelines with the same "set", this is named an associativity conflict. When
this happens, the cache will place each read miss request in a different "way"
of the MSHR. However, if there is no available way, the request is put on hold
(case 5 in :numref:`Table %s <tab_onhold>`).


.. _sec_uncacheable_handler:

Uncacheable Handler
-------------------

This block is responsible for processing uncacheable load and store requests
(see :ref:`sec_req_cacheability`), as well as atomic requests (regardless of
whether they are cacheable or not). For more information about atomic requests
see :ref:`sec_amo`.

If :math:`\scriptsize\mathsf{CONF\_HPDCACHE\_SUPPORT\_AMO}` is set to 0, the
HPDcache does not support AMOs from requesters. In this case, the AMO has no
effect and the Uncacheable Handler responds with an error to the corresponding
requester (when ``core_req_i.need_rsp`` is set to 1). If ``core_req_i.need_rsp``
is set to 0, the Uncacheable Handler ignores the AMO.

All requests handled by this block produce a request to the memory. These
requests to the memory are issued through the CMI interfaces. Uncacheable read
requests are forwarded to the memory through the CMI read. Uncacheable write
requests or atomic requests are forwarded through the CMI write.


.. _sec_cmo_handler:

Cache Management Operation (CMO) Handler
----------------------------------------

This block is responsible for handling CMOs. CMOs are special requests from
requesters that address the cache itself, and not the memory or a peripheral.
CMOs allow to invalidate or prefetch designated cachelines, or produce explicit
memory read and write fences.

The complete list of supported CMOs is detailed in :ref:`sec_cmo`.

If :math:`\scriptsize\mathsf{CONF\_HPDCACHE\_SUPPORT\_CMO}` is set to 0, the
HPDcache does not support CMOs from requesters. In this case, the CMO has no
effect and the CMO Handler responds with an error to the corresponding requester
(when ``core_req_i.need_rsp`` is set to 1). If ``core_req_i.need_rsp`` is set to
0, the CMO Handler ignores the CMO.


.. _sec_rtab:

Replay Table (RTAB)
-------------------

The RTAB is implemented as an array of linked lists. It is a fully-associative
multi-entry buffer where each valid entry belongs to a linked list. It is
implemented in flip-flops. Each linked lists contain requests that target the
same cacheline. There can be multiple linked lists but each shall target a
different cacheline. The head of each linked list contains the oldest request
while the tail contains the newest request. The requests are processed from the
head to the tail to respect the rules explained in section :ref:`sec_mcrs`.

Regarding the pop operation (extracting a ready request from the replay table),
it is possible that once the request is replayed, some of the resources it needs
are again busy. Therefore, the request needs to be put on-hold again. In this
case, the request needs to keep its position as head of the linked list. This is
to preserve the program order. This is the reason why the pop operation is
implemented as a two-step operation: pop then commit, or pop then rollback. The
commit operation allows to actually retire the request, while the rollback
allows to undo the pop.

An entry of the RTAB has the following structure (LL means Linked List):

.. list-table::
   :widths: 10 40 50
   :header-rows: 1

   * - **Field**
     - **Description**
     - **Width (in bits)**
   * - Request
     - Contains the on-hold request from the core (including data)
     - :math:`\mathsf{\approx{}200}`
   * - LL tail
     - Indicates if the entry is the tail of a linked list
     - :math:`\mathsf{1}`
   * - LL head
     - Indicates if the entry is the head of a linked list
     - :math:`\mathsf{1}`
   * - LL next
     - Designates the next (older) request in the linked list
     - :math:`\mathsf{log_2(CONF\_HPDCACHE\_RTAB\_ENTRIES)}`
   * - Deps
     - Indicates the kind of dependency that keeps the request on-hold.
     - :math:`\mathsf{5}`
   * - Valid
     - Indicates if the entry is valid (if unset the entry is free).
     - :math:`\mathsf{1}`


The following table briefly describes the possible dependencies between
memory requests. For each kind of dependency, there is a corresponding
bit in the "deps bits" field of RTAB entries.

.. list-table::
   :widths: 25 75
   :header-rows: 1

   * - **Dependency**
     - **Description**
   * - MSHR Hit
     - Read miss and there is an outstanding miss request on the target address
   * - MSHR Full
     - Read miss and the MSHR has no available way for the requested address
   * - MSHR Not Ready
     - Read miss and the MSHR is busy and cannot send the miss request
   * - WBUF Hit
     - Read miss and there is a match with an open, pending, or sent entry in
       the write buffer
   * - WBUF Not Ready
     - Write miss and there is a match with a sent entry in the write buffer or
       the write-buffer is full


RTAB operations
'''''''''''''''

The RTAB implements the following operations:

+--------------------------+----------------------------------+
| **Operation**            | **Description**                  |
+==========================+==================================+
| ``rtab_alloc``           | Allocate a new linked list       |
+--------------------------+----------------------------------+
| ``rtab_alloc_and_link``  | Allocate a new entry and link it |
|                          | to an existing linked list       |
+--------------------------+----------------------------------+
| ``rtab_pop_try``         | Get a ready request from one of  |
|                          | the linked list (wihout actually |
|                          | removing it from the list)       |
+--------------------------+----------------------------------+
| ``rtab_pop_commit``      | Actually remove a popped request |
|                          | from the list                    |
+--------------------------+----------------------------------+
| ``rtab_pop_rollback``    | Rollback a previously popped     |
|                          | request (with a possible update  |
|                          | of its dependencies)             |
+--------------------------+----------------------------------+
| ``rtab_find_ready``      | Find a ready request among the   |
|                          | heads of valid linked lists      |
+--------------------------+----------------------------------+
| ``rtab_update_deps``     | Update the dependency bits of    |
|                          | valid requests                   |
+--------------------------+----------------------------------+
| ``rtab_find_empty``      | Find an empty request            |
+--------------------------+----------------------------------+
| ``rtab_is_full``         | Is the RTAB full ?               |
+--------------------------+----------------------------------+
| ``rtab_is_empty``        | Is the RTAB empty ?              |
+--------------------------+----------------------------------+
| ``rtab_match_tail``      | Find a 'tail' entry matching a   |
|                          | given nline                      |
+--------------------------+----------------------------------+
| ``rtab_match``           | Find an entry matching a given   |
|                          | nline                            |
+--------------------------+----------------------------------+

The C-like functions below briefly describe the algorithms implemented in the
RTL code of the RTAB.

The following function is called by the cache controller when it detects that
one or more of the conditions in :ref:`tab_onhold` is met, and the request shall
be put on hold.

.. code:: c

   int rtab_alloc(req_t r, deps_t d)
   {
     int index = rtab_find_empty();
     rtab[index] = {
       valid     : 1,
       deps      : d,
       ll_head   : 1,
       ll_tail   : 1,
       ll_next   : 0,
       request   : r
     };
     return index;
   }

The following function is called by the cache controller when it detects that
the request in the pipeline targets the same cacheline that one or more on-hold
requests. In this case, the request is linked in the tail of the corresponding list in the RTAB.

.. code:: c

   int rtab_alloc_and_link(req_t r)
   {
     int index = rtab_find_empty();
     int match = rtab_match_tail(get_nline(r));

     //  replace the tail of the linked list
     rtab[match].ll_tail = 0;

     //  make the next pointer of the old tail to point to the new entry
     rtab[match].ll_next = index;

     //  add the new request as the tail of the linked list
     rtab[index] = {
       valid     : 1,
       deps      : 0,
       ll_head   : 0,
       ll_tail   : 1,
       ll_next   : 0,
       request   : r
     };

     return index;
   }

The following function is called by the cache controller to select a ready
request (dependencies have been resolved) from the RTAB.

.. code:: c

   req_t rtab_pop_try()
   {
     //  These are global states (preserved between function calls)
     static int pop_state = HEAD;
     static int last = 0;
     static int next = 0;

     int index;

     //  Brief description of the following code:
     //    The rtab_pop_try function tries to retire all the requests of a given
     //    linked list. Then it passes to another one.
     switch (pop_state) {
       case HEAD:
         //  Find a list whose head request is ready
         //  (using a round-robin policy)
         index = rtab_find_ready(last);
         if (index == -1) return -1;

         //  Update the pointer to the last linked list served
         last = index;

         //  If the list have more than one request, the next time this function
         //  is called, serve the next request of the list
         if (!rtab[index].ll_tail) {
            next = rtab[index].ll_next;
            pop_state = NEXT;
         }

         //  Temporarily unset the head bit. This is to prevent the
         //  request to be rescheduled.
         rtab[index].ll_head = 0;
         break;

       case NEXT:
         index = next;

         //  If the list have more than one request, the next time this function
         //  is called, serve the next request of the list
         if (!rtab[next].ll_tail) {
            next = rtab[index].ll_next;
            pop_state = NEXT;
         }
         //  It it is the last element of the list, return to the HEAD state
         else {
            pop_state = HEAD;
         }

         //  Temporarily unset the head bit. This is to prevent the
         //  request to be rescheduled.
         rtab[index].ll_head = 0;
     }

     //  Pop the selected request
     return rtab[index].req;
   }

The following function is called by the cache controller when the replayed
request is retired (processed).

.. code:: c

   void rtab_pop_commit(int index)
   {
     rtab[index].valid = 0;
   }

The following function is called by the cache controller when the replayed
request cannot be retired because, again, one or more of the conditions in
:ref:`tab_onhold` is met. In this case, the request is restored into the RTAB
with updated dependency bits. The restored request keeps the same position it
its corresponding linked list to respect the program execution order.

.. code:: c

   void rtab_pop_rollback(int index, bitvector deps)
   {
     rtab[index].ll_head = 1;
     rtab[index].deps    = deps;
   }


The following function is used to find a linked list whose head request can be
replayed (dependencies have been resolved).

.. code:: c

   int rtab_find_ready(int last)
   {
     // choose a ready entry using a round-robin policy
     int i = (last + 1) % RTAB_NENTRIES;
     for (;;) {
       //  ready entry found
       if (rtab[i].valid && rtab[i].ll_head && (rtab[i].deps == 0))
         return i;

       //  there is no ready entry
       if (i == last)
         return -1;

       i = (i + 1) % RTAB_NENTRIES;
     }
   }


The following function is called by the miss hander and the write buffer on the
completion of any pending transaction. It allows to update the dependency bits
of any matching request (with the same cacheline address) in the RTAB.

.. code:: c

   void rtab_update_deps(nline_t nline, bitvector deps)
   {
     int index = rtab_match(nline);
     if (index != -1) {
       rtab[index].deps = deps;
     }
   }


The following utility functions are used by functions above.

.. code:: c

   int rtab_find_empty()
   {
     for (int i = 0; i < RTAB_NENTRIES; i++)
       if (!rtab[i].valid)
         return i;

     return -1;
   }

.. code:: c

   bool rtab_is_full()
   {
     return (rtab_find_empty() == -1);
   }


.. code:: c

   int rtab_is_empty()
   {
     for (int i = 0; i < RTAB_NENTRIES; i++)
       if (rtab[i].valid)
         return 0;

     return 1;
   }


.. code:: c

   int rtab_match_tail(nline_t nline)
   {
     for (int i = 0; i < RTAB_NENTRIES; i++)
       if (rtab[i].valid && get_nline(rtab[i].req) == nline && rtab[i].ll_tail)
         return i;

     return -1;
   }


.. code:: c

   int rtab_match(nline_t nline)
   {
     for (int i = 0; i < RTAB_NENTRIES; i++)
       if (rtab[i].valid && get_nline(rtab[i].req) == nline)
         return i;

     return -1;
   }



Policy for taking new requests in the data cache
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The cache has three possible sources of requests:

- The core (new request from requesters)

- The RTAB (on-hold requests)

- The miss handler (refill requests)

The cache controller implements a fixed priority policy between these sources.
It accepts requests in the following order of priority:

#. Refill request (highest priority)

#. On-hold request

#. New request (lowest priority)


Write-buffer
------------

This cache implements a write-through policy. In this policy, the write accesses
from requesters are systematically transferred to the memory, regardless of
whether the write access hits or misses in the HPDcache.

To decouple write acknowledgements from the memory to the HPDcache, and the
write acknowledgements from the HPDcache to the requester, the HPDcache
implements a write-buffer. The goal is to increase the performance: the
requester does not wait the acknowledgement from the memory, which may suffer
from a very high latency. In addition, the write-buffer implements coalescing of
write data to improve the bandwidth utilization of data channels in the NoC.

The write-buffer implements two different parts: directory and data. The
directory enables tracking of active writes. The data buffers are used to
coalesce writes from the requesters.

Write-Buffer Organization
'''''''''''''''''''''''''

The write-buffer implements two flip-flop arrays: one for the directory and
another for the data.


Write-Buffer Directory
~~~~~~~~~~~~~~~~~~~~~~

The write-buffer directory allows to track pending write transactions.

A given entry in the directory of the write-buffer may be in four
different states:

.. list-table::
   :widths: 15 85
   :header-rows: 1

   * - **State**
     - **Description**
   * - **FREE**
     - The entry is available
   * - **OPEN**
     - The entry is valid and contains pending write data. The entry accepts
       new writes (coalescing)
   * - **PEND**
     - The entry is waiting to be sent to the memory. In this state, the entry
       continues to accept new writes (coalescing).
   * - **SENT**
     - The entry was forwarded to the memory, and is waiting for the
       acknowledgement


Each entry contains the following additional information:

.. list-table::
   :widths: 5 15 80
   :header-rows: 1

   * - Field
     - Description
     - Width (in bits)
   * - S
     - State
     - 2
   * - T
     - Write-Buffer Tag
     - :math:`\mathsf{HPDCACHE\_PA\_WIDTH - HPDCACHE\_WBUF\_OFFSET\_WIDTH}`
   * - C
     - Live counter
     - :math:`\mathsf{HPDCACHE\_WBUF\_TIMECNT\_WIDTH}`
   * - P
     - Pointer to the associated data buffer
     - :math:`\mathsf{log_2(HPDCACHE\_WBUF\_DATA\_ENTRIES)}`


The number of entries in the directory array is:

   :math:`\mathsf{CONF\_HPDCACHE\_WBUF\_DIR\_ENTRIES}`

The width (in bits) of data entries is:

Write-Buffer Data
~~~~~~~~~~~~~~~~~~~~~~

The number of entries (depth) of the data array is:

   :math:`\mathsf{CONF\_HPDCACHE\_WBUF\_DATA\_ENTRIES}`

The width (in bits) of data entries is:

   :math:`\mathsf{CONF\_HPDCACHE\_WBUF\_WORDS{}\times{}HPDCACHE\_WORD\_WIDTH}`

Data buffers may be as wide or wider than the data interface of requesters:

   :math:`\mathsf{CONF\_HPDCACHE\_WBUF\_WORDS \ge CONF\_HPDCACHE\_REQ\_WORDS}`

Designer may choose data buffers to be wider than requesters' data interface to
improve the NoC bandwidth utilization. There is however a constraint: data
buffers' width cannot be wider than the NoC interface. Therefore:

.. math::

      \mathsf{CONF\_HPDCACHE\_WBUF\_WORDS{}\times{}HPDCACHE\_WORD\_WIDTH} \le\\
      \mathsf{CONF\_HPDCACHE\_MEM\_DATA\_WIDTH}



Memory Write Consistency Model
''''''''''''''''''''''''''''''

The HPDcache complies with the RVWMO memory consistency model. Regarding writes,
in this consistency model, there are two important properties:

#. The order in which write accesses on different addresses are forwarded to
   memory MAY differ from the order they arrived from the requester (program
   order);

#. Writes onto the same address, MUST be visible in order. If there is a data
   written by a write A on address @x followed by an another write B on the same
   address, the data of A cannot be visible after the processing of B.

The second property allows write coalescing if the hardware ensures that the
last write persists.

The write-buffer exploits the first property. Multiple “in-flight” writes are
supported due to the multiple directory and data entries. These write
transactions can be forwarded to the memory in an order different from the
program order.

To comply with the second property, the write-buffer does not accept a write
access when there is an address conflict with a **SENT** entry. In that case,
the write access is put on-hold as described in :ref:`sec_onhold`.

The system may choose to relax the constraint of putting a write on-hold in case
of an address conflict with a **SENT** entry. This can be relaxed when the NoC
guaranties in-order delivery. The runtime configuration bit
``cfig_wbuf.S`` (see :ref:`sec_csr`) shall be set to 0 to relax this
dependency.


Functional Description
''''''''''''''''''''''

When an entry of the write-buffer directory is in the **OPEN** or **PEND**
states, there is an allocated data buffer, and it contains data that has not yet
been sent to the memory. When an entry of the write-buffer directory is in the
**SENT** state, the corresponding data was transferred to the memory, and the
corresponding data buffer was freed (and can be reused for another write). A
given entry in the write-buffer directory goes from **FREE** to **OPEN** state
when a new write is accepted, and cannot be coalesced with another **OPEN** or
**PEND** entry (i.e. not in the same address range).

A directory entry passes from **OPEN** to **PEND** after a given number of clock
cycles. This number of clock cycles depends on different runtime configuration
values. Each directory entry contains a life-time counter. This counter starts
at 0 when a new write is accepted (**FREE** :math:`\rightarrow` **OPEN**), and
incremented each cycle while in **OPEN**. When the counter reaches
``cfig_wbuf.T`` (see :ref:`sec_csr`), the write-buffer directory
entry goes to **PEND**. Another runtime configurable bit,
``cfig_wbuf.R`` (see :ref:`sec_csr`), defines the behavior of an entry when a
new write is coalesced into an **OPEN** entry. If this last configuration bit is
set, the life-time counter is reset to 0 when a new write is coalesced.
Otherwise, the counter continues to increment normally.

The life-time of a given write-buffer directory entry is longer than the
life-time of a data entry. A given directory entry is freed
(**SENT** :math:`\rightarrow` **FREE**) when the write acknowledgement is
received from the memory. The number of cycles to get an acknowledgement from
the memory may be significant and it is system-dependent. Thus, to improve
utilization of data buffers, the number of entries in the directory is
generally greater than the number of data buffers.  There is a trade-off
between area and performance when choosing the depth of the data buffer. The
area cost of data buffers is the most critical cost in the write-buffer.  The
synthesis-time parameters
:math:`\mathsf{CONF\_HPDCACHE\_WBUF\_DIR\_ENTRIES}` and
:math:`\mathsf{CONF\_HPDCACHE\_WBUF\_DATA\_ENTRIES}` define the number of
entries in the write-buffer directory and write-buffer data, respectively.

When the ``cfig_wbuf.I`` (see :ref:`sec_csr`) is set, the write buffer does not
perform any write coalescing. This means that the entry passes from **FREE** to
**PEND** (bypassing the **OPEN** state).  While an entry is in the **PEND**
state, and ``cfig_wbuf.I`` is set, that entry does not accept any new writes. It
only waits for the data to be sent. The ``cfig_wbuf.T`` is ignored by the write
buffer when ``cfig_wbuf.I`` is set.

Memory Fences
'''''''''''''

In multi-core systems, or more generally, in systems with multiple DMA-capable
devices, when synchronization is needed, it is necessary to implement memory
fences from the software. In the case of RISC-V, there is specific instructions
for this (i.e. fence).

Fence instructions shall be forwarded to the cache to ensure ordering of writes.
The fence will force the write-buffer to send all pending writes before
accepting new ones. This cache implements two ways of signalling a fence:
sending a specific CMO instruction from the core (described later on
:ref:`sec_cmo`), or by asserting ``wbuf_flush_i`` pin (during one cycle).
