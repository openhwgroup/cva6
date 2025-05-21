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
   Description   : HPDcache Interface

Parameters, Interfaces and Communication Protocols
==================================================

Synthesis-time (Static) Configuration Parameters
------------------------------------------------

The HPDcache has several static configuration parameters. These parameters must
be defined at compilation/synthesis.

:numref:`tab_synthesis_parameters` summarizes the list of parameters
that can be set when integrating the HPDcache.

.. _tab_synthesis_parameters:

.. list-table:: Static Synthesis-Time Parameters
   :widths: 45 55
   :header-rows: 1

   * - Parameter
     - Description
   * - :math:`\scriptsize\mathsf{NREQUESTERS}`
     - Number of requesters to the HPDcache
   * - :math:`\scriptsize\mathsf{CONF\_HPDCACHE\_PA\_WIDTH}`
     - Physical address width (in bits)
   * - :math:`\scriptsize\mathsf{CONF\_HPDCACHE\_WORD\_WIDTH}`
     - Width (in bits) of a data word
   * - :math:`\scriptsize\mathsf{CONF\_HPDCACHE\_SETS}`
     - Number of sets
   * - :math:`\scriptsize\mathsf{CONF\_HPDCACHE\_WAYS}`
     - Number of ways (associativity)
   * - :math:`\scriptsize\mathsf{CONF\_HPDCACHE\_CL\_WORDS}`
     - Number of words in a cacheline
   * - :math:`\scriptsize\mathsf{CONF\_HPDCACHE\_REQ\_WORDS}`
     - Number of words in the data channels from/to requesters
   * - :math:`\scriptsize\mathsf{CONF\_HPDCACHE\_REQ\_TRANS\_ID\_WIDTH}`
     - Width (in bits) of the transaction ID from requesters
   * - :math:`\scriptsize\mathsf{CONF\_HPDCACHE\_REQ\_SRC\_ID\_WIDTH}`
     - Width (in bits) of the source ID from requesters
   * - :math:`\scriptsize\mathsf{CONF\_HPDCACHE\_VICTIM\_SEL}`
     - It allows to choose the replacement selection policy
   * - :math:`\scriptsize\mathsf{CONF\_HPDCACHE\_MSHR\_SETS}`
     - Number of sets in the MSHR
   * - :math:`\scriptsize\mathsf{CONF\_HPDCACHE\_MSHR\_WAYS}`
     - Number of ways (associativity) in the MSHR
   * - :math:`\scriptsize\mathsf{CONF\_HPDCACHE\_WBUF\_DIR\_ENTRIES}`
     - Number of entries in the directory of the write buffer
   * - :math:`\scriptsize\mathsf{CONF\_HPDCACHE\_WBUF\_DATA\_ENTRIES}`
     - Number of entries in the data part of the write buffer
   * - :math:`\scriptsize\mathsf{CONF\_HPDCACHE\_WBUF\_WORDS}`
     - Number of data words per entry in the write buffer
   * - :math:`\scriptsize\mathsf{CONF\_HPDCACHE\_WBUF\_TIMECNT\_WIDTH}`
     - Width (in bits) of the time counter in write buffer entries
   * - :math:`\scriptsize\mathsf{CONF\_HPDCACHE\_RTAB\_ENTRIES}`
     - Number of entries in the replay table
   * - :math:`\scriptsize\mathsf{CONF\_HPDCACHE\_FLUSH\_ENTRIES}`
     - Number of entries in the flush directory
   * - :math:`\scriptsize\mathsf{CONF\_HPDCACHE\_FLUSH\_FIFO\_DEPTH}`
     - Number of entries in the flush FIFO
   * - :math:`\scriptsize\mathsf{CONF\_HPDCACHE\_REFILL\_FIFO\_DEPTH}`
     - Number of entries in the refill FIFO
   * - :math:`\scriptsize\mathsf{CONF\_HPDCACHE\_REFILL\_CORE\_RSP\_FEEDTHROUGH}`
     - Use feedthrough FIFO for responses from the refill handler to the core
   * - :math:`\scriptsize\mathsf{CONF\_HPDCACHE\_MEM\_DATA\_WIDTH}`
     - Width (in bits) of the data channels from/to the memory interface
   * - :math:`\scriptsize\mathsf{CONF\_HPDCACHE\_MEM\_ID\_WIDTH}`
     - Width (in bits) of the transaction ID from the memory interface
   * - :math:`\scriptsize\mathsf{CONF\_HPDCACHE\_WT\_ENABLE}`
     - Enable the write-through policy in the cache
   * - :math:`\scriptsize\mathsf{CONF\_HPDCACHE\_WB\_ENABLE}`
     - Enable the write-back policy in the cache
   * - :math:`\scriptsize\mathsf{CONF\_HPDCACHE\_SUPPORT\_AMO}`
     - When set to 1, the HPDCache supports Atomic Memory Operations (AMOs)
   * - :math:`\scriptsize\mathsf{CONF\_HPDCACHE\_SUPPORT\_CMO}`
     - When set to 1, the HPDCache supports Cache Management Operations (CMOs)
   * - :math:`\scriptsize\mathsf{CONF\_HPDCACHE\_SUPPORT\_PERF}`
     - When set to 1, the HPDcache integrates performance counters

Some parameters are not directly related with functionality. Instead, they
allow adapting the HPDcache to physical constraints in the target technology
node. Typically, these control the geometry of SRAM macros. Depending on the
technology, some dimensions are more efficient than others (in terms of
performance, power and area). These also need to be provided by the user at
synthesis-time. :numref:`tab_synthesis_physical_parameters` lists the static
synthesis-time physical parameters of the HPDcache. The
:math:`\scriptsize\mathsf{CONF\_HPDCACHE\_ACCESS\_WORDS}` has an impact on the refill
latency (see section :ref:`sec_cache_ram_organization`).

.. _tab_synthesis_physical_parameters:

.. list-table:: Static Synthesis-Time Physical Parameters
   :widths: 50 50
   :header-rows: 1

   * - Parameter
     - Description
   * - :math:`\scriptsize\mathsf{CONF\_HPDCACHE\_ACCESS\_WORDS}`
     - Number of words that can be accessed simultaneously from the CACHE data
       array
   * - :math:`\scriptsize\mathsf{CONF\_HPDCACHE\_DATA\_WAYS\_PER\_RAM\_WORD}`
     - Number of ways in the same CACHE data SRAM word
   * - :math:`\scriptsize\mathsf{CONF\_HPDCACHE\_DATA\_SETS\_PER\_RAM}`
     - Number of sets per RAM macro in the DATA array of the cache
   * - :math:`\scriptsize\mathsf{CONF\_HPDCACHE\_DATA\_RAM\_BYTE\_ENABLE}`
     - Use RAM macros with byte-enable instead of bit-mask for the CACHE data
       array
   * - :math:`\scriptsize\mathsf{CONF\_HPDCACHE\_MSHR\_USE\_REG\_BANK}`
     - Use FFs instead of SRAM for the MSHR
   * - :math:`\scriptsize\mathsf{CONF\_HPDCACHE\_MSHR\_WAYS\_PER\_RAM\_WORD}`
     - Number of ways in the same MSHR SRAM word
   * - :math:`\scriptsize\mathsf{CONF\_HPDCACHE\_MSHR\_SETS\_PER\_RAM}`
     - Number of sets per RAM macro in the MSHR array of the cache
   * - :math:`\scriptsize\mathsf{CONF\_HPDCACHE\_MSHR\_RAM\_BYTE\_ENABLE}`
     - Use RAM macros with byte-enable instead of bit-mask for the MSHR

Several internal configuration values are computed from the above ones.
:numref:`tab_internal_parameters` has a non-complete list of these
internal configuration values that may be mentioned in the remainder of this
document.

.. _tab_internal_parameters:

.. list-table:: Internal Parameters
   :widths: 35 25 40
   :header-rows: 1

   * - Parameter
     - Description
     - Value
   * - :math:`\scriptsize\mathsf{HPDCACHE\_CL\_WIDTH}`
     - Width (in bits) of a cacheline
     - | :math:`\scriptsize\mathsf{CONF\_HPDCACHE\_CL\_WORDS \times}`
       |     :math:`\scriptsize\mathsf{CONF\_HPDCACHE\_WORD\_WIDTH}`
   * - :math:`\scriptsize\mathsf{HPDCACHE\_REQ\_DATA\_WIDTH}`
     - Width (in bits) of request data interfaces
     - | :math:`\scriptsize\mathsf{CONF\_HPDCACHE\_REQ\_WORDS \times}`
       |     :math:`\scriptsize\mathsf{CONF\_HPDCACHE\_WORD\_WIDTH}`
   * - :math:`\scriptsize\mathsf{HPDCACHE\_NLINE\_WIDTH}`
     - Width (in bits) of the cacheline index part of the address
     - | :math:`\scriptsize\mathsf{CONF\_HPDCACHE\_PA\_WIDTH -}`
       |     :math:`\scriptsize\mathsf{log_2(\frac{HPDCACHE\_CL\_WIDTH}{8})}`
   * - :math:`\scriptsize\mathsf{HPDCACHE\_SET\_WIDTH}`
     - Width (in bits) of the SET part of the address
     - :math:`\scriptsize\mathsf{log_2(CONF\_HPDCACHE\_SETS)}`
   * - :math:`\scriptsize\mathsf{HPDCACHE\_TAG\_WIDTH}`
     - Width (in bits) of the TAG part of the address
     - | :math:`\scriptsize\mathsf{HPDCACHE\_NLINE\_WIDTH -}`
       |     :math:`\scriptsize\mathsf{HPDCACHE\_SET\_WIDTH}`
   * - :math:`\scriptsize\mathsf{HPDCACHE\_WBUF\_WIDTH}`
     - Width (in bits) of an entry in the write-buffer
     - | :math:`\scriptsize\mathsf{CONF\_HPDCACHE\_WBUF\_WORDS \times}`
       |     :math:`\scriptsize\mathsf{CONF\_HPDCACHE\_WORD\_WIDTH}`


Conventions
-----------

The HPDcache uses the following conventions in the naming of its signals:

 - The ``_i`` suffix for input ports
 - The ``_o`` suffix for output ports
 - The ``_n`` suffix for active low ports
 - The ``clk_`` suffix for clock ports
 - The ``rst_`` suffix for reset ports
 - There may be a mix of suffixes. For example ``_ni`` indicates an active-low
   input port


Global Signals
--------------

.. _tab_global_signals:

.. list-table:: Global Signals
   :widths: 25 15 60
   :header-rows: 1

   * - Signal
     - Source
     - Description
   * - ``clk_i``
     - Clock source
     - Global clock signal.
       The HPDcache is synchronous to the rising-edge of the clock.
   * - ``rst_ni``
     - Reset source
     - Global reset signal. Asynchronous, active LOW, reset signal.
   * - ``wbuf_flush_i``
     - System
     - Force the write-buffer to send all pending writes. Active HIGH,
       one-cycle, pulse signal. Synchronous to ``clk_i``.
   * - ``wbuf_empty_o``
     - Cache
     - Indicates if the write-buffer is empty (there is no pending write
       transactions). When this signal is set to 1, the write-buffer is empty.
   * - ``cfig_base_i``
     - System
     - Base address of the CSR segment in the HPDcache (:ref:`sec_csr`)


Cache-Requesters Interface
--------------------------------------

This section describes the Cache-Requesters Interface (CRI) between requesters
and the HPDcache. It contains two channels: one for requests and one for
responses. There are as many CRIs as requesters from the core/accelerator to
the HPDcache.

This interface is synchronous to the rising edge of the global
clock ``clk_i``.

The address (``core_req_i.addr_offset``), size (``core_req_i.size``),
byte-enable (``core_req_i.be``), write data (``core_req_i.wdata``) and
read data (``core_rsp_o.rdata``) signals shall comply with the alignment
constraints defined in section
:ref:`Address, data, and byte enable alignment <sec_req_alignment>`.

CRI Signal Description
~~~~~~~~~~~~~~~~~~~~~~

.. _tab_req_channel_signals:

.. list-table:: CRI Request Channel Signals
   :widths: 31 13 52
   :align: center
   :header-rows: 1

   * - Signal
     - Source
     - Description
   * - ``core_req_valid_i``
     - Requester
     - Indicates that the corresponding requester has a valid request
   * - ``core_req_ready_o``
     - Cache
     - Indicates that the cache is ready to accept a request from the
       corresponding requester
   * - ``core_req_i.addr_offset``
     - Requester
     - Least significant bits of the target address of the request
   * - ``core_req_i.wdata``
     - Requester
     - Write data (little-endian)
   * - ``core_req_i.op``
     - Requester
     - Indicates the type of operation to be performed
   * - ``core_req_i.be``
     - Requester
     - Byte-enable for write data (little-endian)
   * - ``core_req_i.size``
     - Requester
     - Indicate the size of the access. The size is encoded as the power-of-two
       of the number of bytes (e.g.
       0 is :math:`\scriptsize\mathsf{2^0~=~1}`,
       5 is :math:`\scriptsize\mathsf{2^5~=~32}`)
   * - ``core_req_i.sid``
     - Requester
     - The identification tag for the requester. It shall be identical to the
       index of the request port binded to that requester
   * - ``core_req_i.tid``
     - Requester
     - The identification tag for the request. A requester can issue multiple
       requests. The corresponding response from the cache will return this tid
   * - ``core_req_i.need_rsp``
     - Requester
     - Indicates if the request needs a response from the cache. When unset,
       the cache will not issue a response for the corresponding request
   * - ``core_req_i.phys_indexed``
     - Requester
     - Indicates wheter the access uses virtual (unset) or physical indexing
       (set)
   * - ``core_req_i.addr_tag``
     - Requester
     - Most significant bits of the target address of the request. It is only
       valid when using physical indexing (``core_req_i.phys_indexed = 1``)
   * - ``core_req_i.pma.uncacheable``
     - Requester
     - Indicates whether the access needs to be cached (unset) or not (set).
       Uncacheable accesses are directly forwarded to the memory. It is only
       valid when using physical indexing (``core_req_i.phys_indexed = 1``)
   * - ``core_req_i.pma.io``
     - Requester
     - Indicates whether the request targets input/output (IO) peripherals
       (set) or not (unset). IO accesses are directly forwarded to the memory.
       It is only valid when using physical indexing
       (``core_req_i.phys_indexed = 1``)
   * - ``core_req_i.pma.wr_policy_hint``
     - Requester
     - Indicates whether the target cacheline shall be managed as write-back
       (write allocate) or write-through (write non-allocate).
       It is only valid when using physical indexing
       (``core_req_i.phys_indexed = 1``)
   * - ``core_req_tag_i``
     - Requester
     - Most significant bits of the target address of the request. This signal
       must be delayed of 1 cycle after
       ``(core_req_valid_i & core_req_ready_o) = 1``.
       It is valid when using virtual indexing
       (``core_req_i.phys_indexed = 0``)
   * - ``core_req_pma_i.uncacheable``
     - Requester
     - Indicates whether the access needs to be cached (unset) or not (set).
       Uncacheable accesses are directly forwarded to the memory. This signal
       must be delayed of 1 cycle after
       ``(core_req_valid_i & core_req_ready_o) = 1``.
       It is only valid when using virtual indexing
       (``core_req_i.phys_indexed = 0``)
   * - ``core_req_pma_i.io``
     - Requester
     - Indicates whether the access targets input/output (IO) peripherals (set)
       or not (unset). IO accesses are directly forwarded to the memory. This
       signal must be delayed of 1 cycle after
       ``(core_req_valid_i & core_req_ready_o) = 1``.
       It is only valid when using virtual indexing
       (``core_req_i.phys_indexed = 0``)
   * - ``core_req_pma_i.wr_policy_hint``
     - Requester
     - Indicates whether the target cacheline shall be managed as write-back
       (write allocate) or write-through (write non-allocate).
       It is only valid when using virtual indexing
       (``core_req_i.phys_indexed = 0``)

.. _tab_resp_channel_signals:

.. list-table:: CRI Response Channel Signals
   :widths: 31 13 52
   :header-rows: 1

   * - Signal
     - Source
     - Description
   * - ``core_rsp_valid_o``
     - Cache
     - Indicates that the HPDcache has a valid response for the corresponding
       requester
   * - ``core_rsp_o.rdata``
     - Cache
     - Response read data
   * - ``core_rsp_o.sid``
     - Cache
     - The identification tag for the requester. It corresponds to the **sid**
       transferred with the request
   * - ``core_rsp_o.tid``
     - Cache
     - The identification tag for the request. It corresponds to the **tid**
       transferred with the request
   * - ``core_rsp_o.error``
     - Cache
     - Indicates whether there was an error condition while processing the
       request
   * - ``core_rsp_o.aborted``
     - Cache
     - Indicates if the request issued in the previous cycle shall be aborted.
       It is only considered if the previous request used virtual indexing

Cache Memory Interfaces
----------------------------------

This section describes the Cache-Memory Interface (CMI) between the HPDcache
and the NoC/memory. It implements 5 different channels.

This interface is synchronous to the rising edge of the global clock
``clk_i``.

All CMI interfaces implements the ready-valid protocol described in section
:ref:`sec_ready_valid_handshake` for the handshake
between the HPDcache and the NoC/Memory.

The address (``mem_req_addr``), size (``mem_req_size``),
write data (``mem_req_w_data``) and write byte-enable (``mem_req_w_be``)
signals shall comply with the alignment constraints defined in section
:ref:`Address, data, and byte enable alignment <sec_req_alignment>`.


.. _sec_mi_signal_descriptions:

CMI Signal Descriptions
~~~~~~~~~~~~~~~~~~~~~~~

- **Memory Read Interfaces**

.. _tab_read_req_channel_signals:

.. list-table:: CMI Read Request Channel Signals
   :widths: 31 13 52
   :header-rows: 1

   * - Signal
     - Source
     - Description
   * - ``mem_req_read_valid_o``
     - Cache
     - Indicates that the channel is signaling a valid request
   * - ``mem_req_read_ready_i``
     - NoC
     - Indicates that the NoC is ready to accept a request
   * - ``mem_req_read_o.mem_req_addr``
     - Cache
     - Target physical address of the request. The address shall be aligned to
       the ``mem_req_read_o.mem_req_size`` field.
   * - ``mem_req_read_o.mem_req_len``
     - Cache
     - Indicates the number of transfers in a burst minus one
   * - ``mem_req_read_o.mem_req_size``
     - Cache
     - Indicate the size of the access. The size is encoded as the power-of-two
       of the number of bytes
   * - ``mem_req_read_o.mem_req_id``
     - Cache
     - The identification tag for the request. The HPDcache always use unique
       IDs on the memory interface (i.e. two or more in-flight requests cannot
       share the same ID).
   * - ``mem_req_read_o.mem_req_command``
     - Cache
     - Indicates the type of operation to be performed
   * - ``mem_req_read_o.mem_req_atomic``
     - Cache
     - In case of atomic operations, it indicates its type
   * - ``mem_req_read_o.mem_req_cacheable``
     - Cache
     - This is a hint for the cache hierarchy in the system. It indicates if
       the request can be allocated by the cache hierarchy. That is, data can
       be prefetched from memory or can be reused for multiple read
       transactions


.. _tab_read_miss_resp_channel_signals:

.. list-table:: CMI Read Response Channel Signals
   :widths: 31 13 52
   :header-rows: 1

   * - Signal
     - Source
     - Description
   * - ``mem_resp_read_valid_i``
     - NoC
     - Indicates that the channel is signaling a valid response
   * - ``mem_resp_read_ready_o``
     - Cache
     - Indicates that the cache is ready to accept a response
   * - ``mem_resp_read_i.mem_resp_r_error``
     - NoC
     - Indicates whether there was an error condition while processing the
       request
   * - ``mem_resp_read_i.mem_resp_r_id``
     - NoC
     - The identification tag for the request. It corresponds to the ID
       transferred with the request
   * - ``mem_resp_read_i.mem_resp_r_data``
     - NoC
     - Response read data. It shall be naturally aligned to the request address
   * - ``mem_resp_read_i.mem_resp_r_last``
     - NoC
     - Indicates the last transfer in a read response burst


- **Memory Write Interfaces**

.. _tab_write_req_channel_signals:

.. list-table:: CMI Write Request Channel Signals
   :widths: 31 13 52
   :header-rows: 1

   * - Signal
     - Source
     - Description
   * - ``mem_req_write_valid_o``
     - Cache
     - Indicates that the channel is signaling a valid request
   * - ``mem_req_write_ready_i``
     - NoC
     - Indicates that the cache is ready to accept a response
   * - ``mem_req_write_o.mem_req_addr``
     - Cache
     - Target physical address of the request
   * - ``mem_req_write_o.mem_req_len``
     - Cache
     - Indicates the number of transfers in a burst minus one
   * - ``mem_req_write_o.mem_req_size``
     - Cache
     - Indicate the size of the access. The size is encoded as the
       power-of-two of the number of bytes
   * - ``mem_req_write_o.mem_req_id``
     - Cache
     - The identification tag for the request. The HPDcache always use unique
       IDs on the memory interface (i.e. two or more in-flight requests cannot
       share the same ID).
   * - ``mem_req_write_o.mem_req_command``
     - Cache
     - Indicates the type of operation to be performed
   * - ``mem_req_write_o.mem_req_atomic``
     - Cache
     - In case of atomic operations, it indicates its type
   * - ``mem_req_write_o.mem_req_cacheable``
     - Cache
     - This is a hint for the cache hierarchy in the system. It indicates if
       the write is bufferable by the cache hierarchy. This means that the
       write must be visible in a timely manner at the final destination.
       However, write responses can be obtained from an intermediate point


.. _tab_write_data_channel_signals:

.. list-table:: CMI Write Data Channel Signals
   :widths: 31 13 52
   :header-rows: 1

   * - Signal
     - Source
     - Description
   * - ``mem_req_write_data_valid_o``
     - Cache
     - Indicates that the channel is transferring a valid data
   * - ``mem_req_write_data_ready_i``
     - NoC
     - Indicates that the target is ready to accept the data
   * - ``mem_req_write_data_o.mem_req_w_data``
     - Cache
     - Request write data. It shall be naturally aligned to the request
       address
   * - ``mem_req_write_data_o.mem_req_w_be``
     - Cache
     - Request write byte-enable. It shall be naturally aligned to the request
       address
   * - ``mem_req_write_data_o.mem_req_w_last``
     - Cache
     - Indicates the last transfer in a write request burst


.. _tab_write_resp_channel_signals:

.. list-table:: CMI Write Response Channel Signals
   :widths: 31 13 52
   :header-rows: 1

   * - Signal
     - Source
     - Description
   * - ``mem_resp_write_valid_i``
     - NoC
     - Indicates that the channel is transferring a valid write acknowledgement
   * - ``mem_resp_write_ready_o``
     - Cache
     - Indicates that the cache is ready to accept the acknowledgement
   * - ``mem_resp_write_i.mem_resp_w_is_atomic``
     - NoC
     - Indicates whether the atomic operation was successfully processed
       (atomically)
   * - ``mem_resp_write_i.mem_resp_w_error``
     - NoC
     - Indicates whether there was an error condition while processing the
       request
   * - ``mem_resp_write_i.mem_resp_w_id``
     - NoC
     - The identification tag for the request. It corresponds to the ID
       transferred with the request


Interfaces’ requirements
------------------------

This section describes the basic protocol transaction requirements for the
different interfaces in the HPDcache.


..  _sec_ready_valid_handshake:

Valid/Ready handshake process
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

All interfaces in the HPDcache use a **valid**/**ready** handshake process to
transfer a payload between the source and the destination. The payload contains
the address, data and control information.

As a reminder, the 7 interfaces in the HPDcache are the following:

#. CRI request interface
#. CRI response interface
#. CMI read request interface
#. CMI read response interface
#. CMI write request interface
#. CMI write data request interface
#. CMI write response interface

The source sets to 1 the **valid** signal to indicate when the payload is
available. The destination sets to 1 the **ready** signal to indicate that it
can accept that payload. Transfer occurs only when both the **valid** and
**ready** signals are set to 1 on the next rising edge of the clock.

A source is not permitted to wait until **ready** is set to 1 before setting
**valid** to 1.

A destination may or not wait for **valid** to set the **ready** to 1
(:numref:`cases (a) and (d) in Table %s <tab_ready_valid_scenarios>`).
In other words, a destination may set **ready** to 1 before an actual transfer
is available.

When **valid** is set to 1, the source must keep it that way until the
handshake occurs. This is, at the next rising edge when both **valid** and
**ready** (from the destination) are set to 1. In other words, a source cannot
retire a pending **valid** transfer
(:numref:`Case (b) in Table %s <tab_ready_valid_scenarios>`).

After an effective transfer (**valid** and **ready** set to 1), the source may
keep **valid** set to 1 in the next cycle to signal a new transfer (with a new
payload). In the same manner, the destination may keep **ready** set to 1 if it
can accept a new transfer. This allows back-to-back transfers, with no idle
cycles, between a source and a destination
(:numref:`Case (d) in Table %s <tab_ready_valid_scenarios>`).

All interfaces are synchronous to the rising edge of the same global
clock (``clk_i``).

.. _tab_ready_valid_scenarios:

.. list-table:: valid/ready scenarios
   :class: borderless
   :align: center

   * - **(a)**
     - **(b)**
   * - .. image:: images/wave_ready_before_valid.*
     - .. image:: images/wave_valid_before_ready.*
   * - **(c)**
     - **(d)**
   * - .. image:: images/wave_ready_when_valid.*
     - .. image:: images/wave_back_to_back.*


CRI Response Interface
'''''''''''''''''''''''''''''

In the case of the CRI response interfaces, there is a particularity.
For these interfaces, it is assumed that the **ready** signal is always set to
1. That is why the **ready** signal is not actually implemented on those
interfaces. In other words, the requester unconditionally accepts any incoming
response.

.. _sec_req_alignment:

Address, data and byte enable alignment
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Address alignment
'''''''''''''''''

The address transferred (**addr**) in all request interfaces (CRI and CMI)
shall be byte-aligned to the value of the corresponding **size** signal in that
interface.

Some examples are illustrated in
:numref:`Figure %s <fig_request_data_alignment>`. In the first case, the
**size** value is 2 (which corresponds to :math:`\scriptsize\mathsf{2^2=4}` bytes).
Thus, the address must be a multiple of 4; In the second case, **size** value
is 3. Thus, the address must be a multiple of 8. Finally, in the third case,
**size** value is 0. Thus, there is no constraint on the address alignment.

Data alignment
''''''''''''''

The data must be naturally aligned to the address (**addr**) and the maximum
valid bytes of the transfer must be equal to :math:`\scriptsize\mathsf{2^{size}}`.
This means that the first valid byte in the **data** signal must be at the
indicated offset of the address. Here, the offset corresponds to the least
significant bits of the address, that allow to indicate a byte within the
**data** word. For example, if the **data** signal is 128 bits wide (16
bytes), then the offset corresponds to the first 4 bits of the **addr** signal.

Some examples are illustrated in
:numref:`Figure %s <fig_request_data_alignment>`. As illustrated, within the
data word, only bytes in the range from the indicated offset in the address, to
that offset plus :math:`\scriptsize\mathsf{2^{size}}` can contain valid data. Other bytes must
be ignored by the destination.

Additionally, within the range described above, the **be** signal indicates
which bytes within that range are actually valid. Bytes in the **data**
signal where the **be** signals are set to 0, must be ignored by the
destination.

Byte Enable (BE) alignment
''''''''''''''''''''''''''

The **be** signal must be naturally aligned to the address (**addr**) and the
number of bits set in this signal must be less or equal to
:math:`\scriptsize\mathsf{2^\text{size}}`. This means that the first valid bit in the
**be** signal must be at the indicated offset of the address. The offset is
the same as the one explained above in the "Data alignment" paragraph.

Some examples are illustrated in
:numref:`Figure %s <fig_request_data_alignment>`. As illustrated, within the
**be** word, only bits in the range from the indicated offset in the address,
to that offset plus :math:`\scriptsize\mathsf{2^{size}}` can be set. Other bits
outside that range must be set to 0.

.. _fig_request_data_alignment:

.. figure:: images/hpdcache_request_address_data_alignment.*
   :align: center
   :alt: Address, Data and Byte Enable Alignment in Requests

   Address, Data and Byte Enable Alignment in Requests


Cache-Requesters Interface (CRI) Attributes
-------------------------------------------

.. _sec_vipt:

Physical or Virtual Indexing
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The HPDcache allows the address and physical memory attributes (PMA) to be sent
by the requesters in two different (but consecutive) cycles.

This is useful to allow the pipelining of the address translation mechanism
(when the core has one). This is illustrated in
:numref:`Figure %s <fig_vipt>`.
Doing the translation and directly forwarding to the cache is usually too
costly in terms of timing. Instead, the requesters can:

.. list-table::
   :widths: 15 85
   :header-rows: 0

   * - Cycle 0
     - During the first cycle, forward the least significant bits of the
       address (``addr_offset``), which usually do not need to be translated,
       along with the other fields of the request (operation, identifiers,
       etc). In the meanwhile the core can perform the translation of the
       address to compute the most significant bits (``addr_tag``)

   * - Cycle 1
     - During the second cycle, forward the previously translated most
       significant bits of the address (``addr_tag``), and the corresponding
       PMAs. PMAs are sent during this second cycle because usually they depend
       on the target physical address. The requester can abort the request
       during this cycle as explained in the next section (:ref:`sec_req_abort`).

.. _fig_vipt:

.. figure:: images/hpdcache_vipt.*
   :align: center
   :width: 80%
   :alt: Pipelining of the Virtual and Physical Part of the Address

   Pipelining of the Virtual and Physical Part of the Address

This kind of indexing is named **Virtually-Indexed Physically-Tagged (VIPT)**.

The requester shall send the tag and PMAs the next cycle after the
``core_req_valid_i`` and ``core_req_ready_o`` signals were set to 1 and the
``core_req_i.phys_indexed`` signal was set to 0.The number of bits of the
address offset (``addr_offset``) depends on the number of cache sets
(:math:`\scriptsize\mathsf{CONF\_HPDCACHE\_SETS}`) and the size of the cachelines
(:math:`\scriptsize\mathsf{CONF\_HPDCACHE\_CL\_WIDTH/8}`).
The address offset represents the concatenation of these two fields of the
address: the byte offset in the cacheline and the set index. Requests can be
sent back-to-back with no idle cycle in-between.

If requesters do not need virtual indexing, they can send the full address in
the first cycle by setting the ``core_req_i.phys_indexed`` bit to 1. The address
offset and the tag shall be sent through the ``core_req_i.addr_offset`` and
``core_req_i.addr_tag``, respectively. A given requester is free to alternate
between virtual and physical indexing on different clock cycles. Different
requesters can use different indexing schemes (virtual or physical).

.. _sec_req_abort:

Request Abortion
~~~~~~~~~~~~~~~~~~~~~

When using the virtual indexing, the requester can abort the request during the
second cycle of the addressing pipeline. In that case, the requester needs to
set the req_abort signal to 1.

When a request is aborted, and the ``core_req_i.need_rsp`` field was set to 1, the
HPDcache respond to the corresponding requester with the bit
``core_rsp_o.aborted`` set to 1.

CRI Type of Operation
~~~~~~~~~~~~~~~~~~~~~

A requester indicates the required operation on the 5-bit, ``HPDCACHE_REQ_OP``
signal. The supported operation are detailed in :numref:`tab_req_op_types`.

.. _tab_req_op_types:

.. list-table:: Requesters Operation Types
   :widths: 30 15 55
   :header-rows: 1

   * - Mnemonic
     - Encoding
     - Type
   * - ``HPDCACHE_REQ_LOAD``
     - 0b00000
     - Read operation
   * - ``HPDCACHE_REQ_STORE``
     - 0b00001
     - Write operation
   * - ``HPDCACHE_REQ_AMO_LR``
     - 0b00100
     - Atomic Load-reserved operation
   * - ``HPDCACHE_REQ_AMO_SC``
     - 0b00101
     - Atomic Store-conditional operation
   * - ``HPDCACHE_REQ_AMO_SWAP``
     - 0b00110
     - Atomic SWAP operation
   * - ``HPDCACHE_REQ_AMO_ADD``
     - 0b00111
     - Atomic integer ADD operation
   * - ``HPDCACHE_REQ_AMO_AND``
     - 0b01000
     - Atomic bitwise AND operation
   * - ``HPDCACHE_REQ_AMO_OR``
     - 0b01001
     - Atomic bitwise OR operation
   * - ``HPDCACHE_REQ_AMO_XOR``
     - 0b01010
     - Atomic bitwise XOR operation
   * - ``HPDCACHE_REQ_AMO_MAX``
     - 0b01011
     - Atomic integer signed MAX operation
   * - ``HPDCACHE_REQ_AMO_MAXU``
     - 0b01100
     - Atomic integer unsigned MAX operation
   * - ``HPDCACHE_REQ_AMO_MIN``
     - 0b01101
     - Atomic integer signed MIN operation
   * - ``HPDCACHE_REQ_AMO_MINU``
     - 0b01110
     - Atomic integer unsigned MIN operation
   * - ``HPDCACHE_CMO_FENCE``
     - 0b10000
     - Memory write fence
   * - ``HPDCACHE_CMO_PREFETCH``
     - 0b10001
     - Prefetch a cacheline given its address
   * - ``HPDCACHE_CMO_INVAL_NLINE``
     - 0b10010
     - Invalidate a cacheline given its address
   * - ``HPDCACHE_CMO_INVAL_ALL``
     - 0b10011
     - Invalidate all Cachelines
   * - ``HPDCACHE_CMO_FLUSH_NLINE``
     - 0b10100
     - Flush a cacheline given its Address
   * - ``HPDCACHE_CMO_FLUSH_ALL``
     - 0b10101
     - Flush All Cachelines
   * - ``HPDCACHE_CMO_FLUSH_INVAL_NLINE``
     - 0b10110
     - Flush and invalidate a cacheline given its address
   * - ``HPDCACHE_CMO_FLUSH_INVAL_ALL``
     - 0b10111
     - Flush and invalidate all cachelines

Load and store operations are normal read and write operations from/to the
specified address.

Atomic operations are the ones specified in the Atomic (A) extension of the
[RISCVUP2019]_. More details on how the HPDcache implements AMOs are found in
section :ref:`sec_amo`.

CMOs are explained in :ref:`sec_cmo`.

Source identifier
~~~~~~~~~~~~~~~~~

Each request identifies its source through the ``core_req_i.sid`` signal. The
``core_req_i.sid`` signal shall be decoded when the ``core_req_valid_i`` signal
is set to 1. The width of this signal is
:math:`\scriptsize\mathsf{CONF\_HPDCACHE\_REQ\_SRC\_ID\_WIDTH}` bits.
The HPDcache reflects the value of the **sid** of the request into the
corresponding **sid** of the response.

Each port must have a unique ID that corresponds to its number. Each port is
numbered from 0 to N-1. This number shall be constant for a given port
(requester). The HPDcache uses this information to route responses to the
correct requester.

Transaction identifier
~~~~~~~~~~~~~~~~~~~~~~

Each request identifies transactions through the
``core_req_i.tid`` signal. The
``core_req_i.tid`` signal shall be decoded when the
``core_req_valid_i`` signal is set to 1. The width of this signal is
:math:`\scriptsize\mathsf{CONF\_HPDCACHE\_REQ\_TRANS\_ID\_WIDTH}` bits.

This signal can contain any value from 0 to
:math:`\scriptsize\mathsf{2^{CONF\_HPDCACHE\_REQ\_TRANS\_ID\_WIDTH} - 1}`.
The HPDcache forwards the value of the **tid** of the request into the **tid**
of the corresponding response.

A requester can issue multiple transactions without waiting for earlier
transactions to complete. Because the HPDcache can respond to these transactions
in a different order than the one of requests, the requester can use the **tid**
to match the responses with respect to requests.

The ID of transactions is not necessarily unique. A requester may reuse a given
transaction ID for different transactions. That is, even when some of these
transactions are not yet completed. However, when the requester starts multiple
transactions with the same **tid**, it cannot match responses and requests
because responses can be in a different order that the one of requests.


.. _sec_req_cacheability:

Cacheability
~~~~~~~~~~~~

This cache considers that the memory space is segmented. A segment corresponds
to an address range: a **base address** and an **end address**. Some segments
are cacheable and others not. The HPDcache needs to know which segments are
cacheable to determine if for a given read request, it needs to copy the read
data into the cache.

The request interface implements an uncacheable bit
(``core_req_i.pma.uncacheable`` or ``core_req_pma_i.uncacheable``).  When this
bit is set, the access is considered uncacheable. The
``core_req_i.pma.uncacheable`` signal shall be decoded when the
``core_req_valid_i`` signal is set to 1. The ``core_req_pma_i.uncacheable``
shall be decoded when the ``core_req_valid_i``, ``core_req_ready_o`` and the
``core_req_i.phys_indexed`` signals were set to 1 the previous cycle.

.. admonition:: Caution
   :class: caution

   For a given address, the uncacheable attribute must be consistent between
   accesses. The granularity is the cacheline. **In the event that the same
   address is accessed with different values in the uncacheable attribute, the
   behavior of the cache for that address is unpredictable**.

Need response
~~~~~~~~~~~~~

For any given request, a requester can set the bit ``core_req_i.need_rsp`` to 0
to indicate that it does not want a response for that request. The
``core_req_i.need_rsp`` signal shall be decoded when the ``core_req_valid_i``
signal is set to 1.

When ``core_req_i.need_rsp`` is set to 0, the HPDcache processes the request
but it does not send an acknowledgement to the corresponding requester when the
transaction is completed.

Write-Policy Hint
~~~~~~~~~~~~~~~~~

The CRI may set dynamically the write-policy (write-back or write-through) for
the target cacheline. In the request interface, there are specific flags (hint)
to indicate the desired policy for a given request.

The request interface drives the hint through the
``core_req_i.pma.wr_policy_hint`` or ``core_req_pma_i.wr_policy_hint`` signals.
The ``core_req_i.pma.wr_policy_hint`` signal shall be decoded when the
``core_req_valid_i`` signal is set to 1. The ``core_req_pma_i.wr_policy_hint``
shall be decoded when the ``core_req_valid_i``, ``core_req_ready_o`` and the
``core_req_i.phys_indexed`` signals were set to 1 the previous cycle.

The supported hints are detailed in :numref:`tab_req_wr_policy_hints`.

.. _tab_req_wr_policy_hints:

.. list-table:: Requesters Write-Policy Hint
   :widths: 30 15 55
   :header-rows: 1

   * - Mnemonic
     - Encoding
     - Type
   * - ``HPDCACHE_WR_POLICY_AUTO``
     - 0b001
     - Request to to keep the current write-policy for the target cacheline if
       there is a copy in the cache, or use the default policy otherwise.
   * - ``HPDCACHE_WR_POLICY_WB``
     - 0b010
     - Request a write-back (write allocate) policy for the target cacheline
   * - ``HPDCACHE_WR_POLICY_WT``
     - 0b100
     - Request a write-through (write non-allocate) policy for the target
       cacheline

Error response
~~~~~~~~~~~~~~

The response interface contains a single-bit ``core_rsp_o.error`` signal.  This
signal is set to 1 by the HPDcache when some error condition occurred during the
processing of the corresponding request. The ``core_rsp_o.error`` signal shall
be decoded when the ``core_rsp_valid_o`` signal is set to 1.

When the ``core_rsp_o.error`` signal is set to 1 in the response, the effect of
the corresponding request is undefined. If this **error** signal is set in the
case of **LOAD** or **AMOs** operations, the **rdata** signal does not contain
any valid data.

Cache-Memory Interface (CMI) Attributes
---------------------------------------

.. _CMI_type-of-operation:

CMI Type of operation
~~~~~~~~~~~~~~~~~~~~~

.. list-table:: Memory request operation types
   :widths: 35 15 50
   :header-rows: 1

   * - Mnemonic
     - Encoding
     - Type
   * - ``HPDCACHE_MEM_READ``
     - 0b00
     - Read operation
   * - ``HPDCACHE_MEM_WRITE``
     - 0b01
     - Write operation
   * - ``HPDCACHE_MEM_ATOMIC``
     - 0b10
     - Atomic operation

``HPDCACHE_MEM_READ`` and ``HPDCACHE_MEM_WRITE`` are respectively normal read
and write operations from/to the specified address.

In case of an atomic operation request (``HPDCACHE_MEM_ATOMIC``), the specific
operation is specified in the ``MEM_REQ_ATOMIC`` signal. These operations are
listed in :numref:`tab_mem_req_atomics_types`. Note that these
operations are compatible with the ones defined in the AMBA AXI prototol.

.. _tab_mem_req_atomics_types:

.. list-table:: Memory request atomic operation types
   :widths: 35 15 50
   :header-rows: 1

   * - Mnemonic
     - Encoding
     - Type
   * - ``HPDCACHE_MEM_ATOMIC_ADD``
     - 0b0000
     - Atomic fetch-and-add operation
   * - ``HPDCACHE_MEM_ATOMIC_CLR``
     - 0b0001
     - Atomic fetch-and-clear operation
   * - ``HPDCACHE_MEM_ATOMIC_SET``
     - 0b0010
     - Atomic fetch-and-set operation
   * - ``HPDCACHE_MEM_ATOMIC_EOR``
     - 0b0011
     - Atomic fetch-and-exclusive-or operation
   * - ``HPDCACHE_MEM_ATOMIC_SMAX``
     - 0b0100
     - Atomic fetch-and-maximum (signed) operation
   * - ``HPDCACHE_MEM_ATOMIC_SMIN``
     - 0b0101
     - Atomic fetch-and-minimum (signed) operation
   * - ``HPDCACHE_MEM_ATOMIC_UMAX``
     - 0b0110
     - Atomic fetch-and-maximum (unsigned) operation
   * - ``HPDCACHE_MEM_ATOMIC_UMIN``
     - 0b0111
     - Atomic fetch-and-minimum (unsigned) operation
   * - ``HPDCACHE_MEM_ATOMIC_SWAP``
     - 0b1000
     - Atomic swap operation
   * - ``HPDCACHE_MEM_ATOMIC_LDEX``
     - 0b1100
     - Load-exclusive operation
   * - ``HPDCACHE_MEM_ATOMIC_STEX``
     - 0b1101
     - Store-exclusive operation


Type of operation per CMI request channel
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

As a reminder, the HPDcache implements two request channels to the memory:

#. Memory read request channel
#. Memory write request channel

:numref:`tab_optypes_by_cmi_req_channel` indicates the type of
operations that each of these two request channels can issue.

.. _tab_optypes_by_cmi_req_channel:

.. list-table:: Operation Types Supported by CMI Request Channels
   :widths: 30 50
   :header-rows: 1

   * - Type
     - Channels
   * - ``HPDCACHE_MEM_READ``
     - - CMI read request
   * - ``HPDCACHE_MEM_WRITE``
     - - CMI write request
   * - ``HPDCACHE_MEM_ATOMIC``
     - - CMI write request


Read-Modify-Write Atomic Operations
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The following atomic operations behave as read-modify-write operations:

- ``HPDCACHE_MEM_ATOMIC_ADD``
- ``HPDCACHE_MEM_ATOMIC_CLR``
- ``HPDCACHE_MEM_ATOMIC_SET``
- ``HPDCACHE_MEM_ATOMIC_EOR``
- ``HPDCACHE_MEM_ATOMIC_SMAX``
- ``HPDCACHE_MEM_ATOMIC_SMIN``
- ``HPDCACHE_MEM_ATOMIC_UMAX``
- ``HPDCACHE_MEM_ATOMIC_UMIN``
- ``HPDCACHE_MEM_ATOMIC_SWAP``

These requests are forwarded to the memory through the CMI write request
interface. A particularity of these requests is that they generate two responses
from the memory:

#. Old data value from memory is returned through the CMI read response
   interface.

#. Write acknowledgement is returned through the CMI write response interface.

Both responses may arrive in any given order to the initiating HPDcache.

Regarding errors, if any response has its **error** signal set to 1
(``mem_resp_*_i.mem_resp_r_error`` or ``mem_resp_*_i.mem_resp_w_error``), the
HPDcache considers that the operation was not completed. It waits for both
responses and it forwards an error response (``core_rsp_o.error = 1``) to the
corresponding requester on the HPDcache requesters’ side.


Exclusive Load/Store Atomic Operations
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Exclusive load and store operations are issued as normal load and store
operations on the CMI read request interface and CMI write request interface,
respectively.

Specific operation types are however used on these exclusive requests:
``HPDCACHE_MEM_ATOMIC_LDEX`` for loads; and
``HPDCACHE_MEM_ATOMIC_STEX`` for stores.

These requests behave similarly to normal load and store to the memory but
provide some additional properties described in :ref:`sec_amo`.

In the case of the ``HPDCACHE_MEM_ATOMIC_STEX`` request, the write
acknowledgement contains an additional information in the
``mem_resp_w_is_atomic`` signal.
If this signal is set to 1, the exclusive store was "atomic", hence the data was
written in memory.
If this signal is set to 0, the exclusive store was "non-atomic". Hence the
write operation was abandoned.

The HPDcache uses exclusive stores in case of SC operations from requesters.
Depending on the ``mem_resp_w_is_atomic`` value, the HPDcache responds to the
requester according to the rules explained in :ref:`sec_amo`. A "non-atomic"
response is considered a **SC Failure**, and a "atomic" response is considered a
**SC Success**.

CMI Transaction identifier
~~~~~~~~~~~~~~~~~~~~~~~~~~

Each request identifies transactions through the ``mem_req_*_o.mem_req_id``
signals. The ``mem_req_*_o.mem_req_id`` signal shall be decoded when the
``mem_req_*_valid_o`` signal is set to 1. The width of these ID signals is
:math:`\scriptsize\mathsf{CONF\_HPDCACHE\_MEM\_ID\_WIDTH}` bits.

The target (memory or peripheral) shall respond to a request by setting the
``mem_resp*_i.mem_resp_*_id`` signal to the corresponding
``mem_req*_i.mem_req_id``.

``mem_req_*_o.mem_req_id`` signals can contain any value from 0 to
:math:`\scriptsize\mathsf{2^CONF\_HPDCACHE\_MEM\_ID\_WIDTH - 1}`.

The HPDcache can issue multiple memory transactions without waiting for earlier
transactions to complete. The HPDcache uses unique IDs for each request.  Unique
IDs means that two or more in-flight requests never share the same ID. In-flight
requests are those that have been issued by the HPDcache but have not yet
received their respective response.

The target (memory or peripheral) of the in-flight request may respond to CMI
in-flight requests in any order.


- **Transaction IDs in the CMI read request channel**

The HPDcache can have the following number of in-flight read miss transactions:

   :math:`\scriptsize\mathsf{CONF\_HPDCACHE\_MSHR\_SETS{}\times{}CONF\_HPDCACHE\_MSHR\_WAYS}`

Each in-flight transaction has a unique transaction ID. This ID is formatted as
follows:

   - For cacheable requests:

   ``(mshr_way << log2(HPDCACHE_MSHR_SETS)) | mshr_set``

   The ID is the concatenation of two indexes: the MSHR set and the MSHR way
   occupied by the corresponding request.

   - For uncacheable requests

   The HPDcache can issue up to 1 in-flight, uncached, read transaction.
   Uncached transactions have a unique transaction ID with all bits set to 1.


- **Transaction IDs in the CMI wbuf write request channel**

The HPDcache can have the following number of in-flight write transactions:

   :math:`\scriptsize\mathsf{CONF\_HPDCACHE\_WBUF\_DIR\_ENTRIES}`

Each in-flight transaction has a unique transaction ID. This ID is formatted as
follows:

  - For cacheable requests:

   The ID corresponds to the index of the entry in the write-buffer directory.

   ``wbuf_dir_index``


  - For uncacheable requests

    The HPDcache can issue up to 1 in-flight, uncached, write transaction.
    Uncached transactions have a unique transaction ID with all bits set to 1.


Event signals
-------------

In addition to the performance registers explained in :ref:`sec_perf_counters`,
the HPDcache provides a set of one-shot signals that indicate when a given event
is detected.  These signals are set to 1 for one cycle each time the
corresponding event is detected. If the same event is detected N cycles in a
row, the corresponding event signal will remain set to 1 for N cycles.
:numref:`Table %s <tab_events>` lists these event signals.

These event signals are output-only. They can be either left unconnected, if
they are not used, or connected with the remainder of the system. The system can
use those signals, for example, for counting those events externally or for
triggering some specific actions.

.. _tab_events:

.. list-table:: Event Signals in the HPDcache
   :widths: 31 13 52
   :header-rows: 1

   * - **Signal**
     - **Source**
     - **Description**
   * - ``evt_o.write_req``
     - Cache
     - Write request accepted
   * - ``evt_o.read_req``
     - Cache
     - Read request accepted
   * - ``evt_o.prefetch_req``
     - Cache
     - Prefetch request accepted
   * - ``evt_o.uncached_req``
     - Cache
     - Uncached request accepted
   * - ``evt_o.cmo_req``
     - Cache
     - CMO request accepted
   * - ``evt_o.accepted_req``
     - Cache
     - One request accepted (any type)
   * - ``evt_o.cache_write_miss``
     - Cache
     - Write miss event
   * - ``evt_o.cache_read_miss``
     - Cache
     - Read miss event
   * - ``evt_o.req_onhold``
     - Cache
     - Request put on-hold in the RTAB
   * - ``evt_o.req_onhold_mshr``
     - Cache
     - Request put on-hold because of a MSHR conflict
   * - ``evt_o.req_onhold_wbuf``
     - Cache
     - Request put on-hold because of a WBUF conflict
   * - ``evt_o.req_onhold_rollback``
     - Cache
     - Request put on-hold (again) after a rollback
   * - ``evt_o.stall``
     - Cache
     - Cache stalls request event

