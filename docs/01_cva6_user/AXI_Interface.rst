..
   Copyright (c) 2023 OpenHW Group
   Copyright (c) 2023 Thales

   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1

   Original Author: Alae Eddine EZ ZEJJARI (alae-eddine.ez-zejjari@external.thalesgroup.com)

.. _cva6_axi:

AXI
===

Introduction
------------
   In this chapter, we describe in detail the restriction that apply to the supported features.

   In order to understand how the AXI memory interface behaves in CVA6, it is necessary to read the AMBA AXI and ACE Protocol Specification (https://developer.arm.com/documentation/ihi0022/hc) and this chapter.


About the AXI4 protocol
~~~~~~~~~~~~~~~~~~~~~~~

   The AMBA AXI protocol supports high-performance, high-frequency system designs for communication between Manager and Subordinate components.

   The AXI protocol features are:

     * It is suitable for high-bandwidth and low-latency designs.
     * High-frequency operation is provided, without using complex bridges.
     * The protocol meets the interface requirements of a wide range of components.
     * It is suitable for memory controllers with high initial access latency.
     * Flexibility in the implementation of interconnect architectures is provided.
     * It is backward-compatible with AHB and APB interfaces.

   The key features of the AXI protocol are:

     * Separate address/control and data phases.
     * Support for unaligned data transfers, using byte strobes.
     * Uses burst-based transactions with only the start address issued.
     * Separate read and write data channels, that can provide low-cost Direct Memory Access (DMA).
     * Support for issuing multiple outstanding addresses.
     * Support for out-of-order transaction completion.
     * Permits easy addition of register stages to provide timing closure.

   The present specification is based on :

      https://developer.arm.com/documentation/ihi0022/hc


AXI4 and CVA6
~~~~~~~~~~~~~

   The AXI bus protocol is used with the CVA6 processor as a memory interface. Since the processor is the one that initiates the connection with the memory, it will have a manager interface to send requests to the subordinate, which will be the memory.

   Features supported by CVA6 are the ones in the AMBA AXI4 specification and the Atomic Operation feature from AXI5. With restriction that apply to some features.

   This doesn’t mean that all the full set of signals available on an AXI interface are supported by the CVA6. Nevertheless, all required AXI signals are implemented.

   Supported AXI4 features are defined in AXI Protocol Specification sections: A3, A4, A5, A6 and A7.

   Supported AXI5 feature are defined in AXI Protocol Specification section: E1.1.


Signal Description (Section A2)
-------------------------------

   This section introduces the AXI memory interface signals of CVA6. Most of the signals are supported by CVA6, the tables summarizing the signals identify the exceptions.

   In the following tables, the *Src* column tells whether the signal is driven by Manager ou Subordinate.

   The AXI required and optional signals, and the default signals values that apply when an optional signal is not implemented are defined in AXI Protocol Specification section A9.3.


Global signals (Section A2.1)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

   Table 2.1 shows the global AXI memory interface signals.


.. list-table::
   :widths: 15 15 55
   :header-rows: 1

   * - **Signal**
     - **Src**
     - **Description**
   * - **ACLK**
     - Clock source
     - | Global clock signal. Synchronous signals are sampled on the
       | rising edge of the global clock.
   * - **WDATA**
     - Reset source
     - | Global reset signal. This signal is active-LOW.


Write address channel signals (Section A2.2)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

   Table 2.2 shows the AXI memory interface write address channel signals. Unless the description indicates otherwise, a signal can take any parameter if is supported.


.. list-table::
   :widths: 15 15 15 40
   :header-rows: 1

   * - **Signal**
     - **Src**
     - **Support**
     - **Description**
   * - **AWID**
     - M
     - | Yes
       | (optional)
     - | Identification tag for a write transaction.
       | CVA6 gives the id depending on the type of transaction.
       | See :ref:`transaction_identifiers_label`.
   * - **AWADDR**
     - M
     - Yes
     - | The address of the first transfer in a write transaction.
   * - **AWLEN**
     - M
     - | Yes
       | (optional)
     - | Length, the exact number of data transfers in a write
       | transaction. This information determines the number of
       | data transfers associated with the address.
       | All write transactions performed by CVA6 are of length 1.
       | (AWLEN = 0b00000000)
   * - **AWSIZE**
     - M
     - | Yes
       | (optional)
     - | Size, the number of bytes in each data transfer in a write
       | transaction
       | See :ref:`address_structure_label`.
   * - **AWBURST**
     - M
     - | Yes
       | (optional)
     - | Burst type, indicates how address changes between each
       | transfer in a write transaction.
       | All write transactions performed by CVA6 are of burst type
       | INCR. (AWBURST = 0b01)
   * - **AWLOCK**
     - M
     - | Yes
       | (optional)
     - | Provides information about the atomic characteristics of a
       | write transaction.
   * - **AWCACHE**
     - M
     - | Yes
       | (optional)
     - | Indicates how a write transaction is required to progress
       | through a system.
       | The subordinate is always of type Device Non-bufferable.
       | (AWCACHE = 0b0000)
   * - **AWPROT**
     - M
     - Yes
     - | Protection attributes of a write transaction:
       | privilege, security level, and access type.
       | The value of AWPROT is always 0b000.
   * - **AWQOS**
     - M
     - | No
       | (optional)
     - | Quality of Service identifier for a write transaction.
       | AWQOS = 0b0000
   * - **AWREGION**
     - M
     - | No
       | (optional)
     - | Region indicator for a write transaction.
       | AWREGION = 0b0000
   * - **AWUSER**
     - M
     - | No
       | (optional)
     - | User-defined extension for the write address channel.
       | AWUSER = 0b00
   * - **AWATOP**
     - M
     - | Yes
       | (optional)
     - | AWATOP indicates the Properties of the Atomic Operation
       | used for a write transaction.
       | See :ref:`atomic_transactions_label`.
   * - **AWVALID**
     - M
     - Yes
     - | Indicates that the write address channel signals are valid.
   * - **AWREADY**
     - S
     - Yes
     - | Indicates that a transfer on the write address channel
       | can be accepted.


Write data channel signals (Section A2.3)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

   Table 2.3 shows the AXI write data channel signals. Unless the description indicates otherwise, a signal can take any parameter if is supported.

.. list-table::
   :widths: 15 15 15 40
   :header-rows: 1

   * - **Signal**
     - **Src**
     - **Support**
     - **Description**
   * - **WID**
     - M
     - | Yes
       | (optional)
     - | The ID tag of the write data transfer.
       | CVA6 gives the id depending on the type of transaction.
       | See :ref:`transaction_identifiers_label`.
   * - **WDATA**
     - M
     - Yes
     - | Write data.
   * - **WSTRB**
     - M
     - | Yes
       | (optional)
     - | Write strobes, indicate which byte lanes hold valid data
       | See :ref:`data_read_and_write_structure_label`.
   * - **WLAST**
     - M
     - Yes
     - | Indicates whether this is the last data transfer in a write
       | transaction.
   * - **WUSER**
     - M
     - | Yes
       | (optional)
     - | User-defined extension for the write data channel.
   * - **WVALID**
     - M
     - Yes
     - | Indicates that the write data channel signals are valid.
   * - **WREADY**
     - S
     - Yes
     - | Indicates that a transfer on the write data channel can be
       | accepted.




Write Response Channel signals (Section A2.4)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

   Table 2.4 shows the AXI write response channel signals. Unless the description indicates otherwise, a signal can take any parameter if is supported.


.. list-table::
   :widths: 15 15 15 40
   :header-rows: 1

   * - **Signal**
     - **Src**
     - **Support**
     - **Description**
   * - **BID**
     - S
     - | Yes
       | (optional)
     - | Identification tag for a write response.
       | CVA6 gives the id depending on the type of transaction.
       | See :ref:`transaction_identifiers_label`.
   * - **BRESP**
     - S
     - Yes
     - | Write response, indicates the status of a write transaction.
       | See :ref:`read_and_write_response_structure_label`.
   * - **BUSER**
     - S
     - | No
       | (optional)
     - | User-defined extension for the write response channel.
       | BUSER= 0b00
   * - **BVALID**
     - S
     - Yes
     - | Indicates that the write response channel signals are valid.
   * - **BREADY**
     - M
     - Yes
     - | Indicates that a transfer on the write response channel can be
       | accepted.




Read address channel signals (Section A2.5)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

   Table 2.5 shows the AXI read address channel signals. Unless the description indicates otherwise, a signal can take any parameter if is supported.


.. list-table::
   :widths: 15 15 15 40
   :header-rows: 1

   * - **Signal**
     - **Src**
     - **Support**
     - **Description**
   * - **ARID**
     - M
     - | Yes
       | (optional)
     - | Identification tag for a read transaction.
       | CVA6 gives the id depending on the type of transaction.
       | See :ref:`transaction_identifiers_label`.
   * - **ARADDR**
     - M
     - | Yes
     - | The address of the first transfer in a read transaction.
   * - **ARLEN**
     - M
     - | Yes
       | (optional)
     - | Length, the exact number of data transfers in a read
       | transaction. This information determines the number of data
       | transfers associated with the address.
       | All read transactions performed by CVA6 are of length less or
       | equal to ICACHE_LINE_WIDTH/64.
   * - **ARSIZE**
     - M
     - | Yes
       | (optional)
     - | Size, the number of bytes in each data transfer in a read
       | transaction
       | See :ref:`address_structure_label`.
   * - **ARBURST**
     - M
     - | Yes
       | (optional)
     - | Burst type, indicates how address changes between each
       | transfer in a read transaction.
       | All Read transactions performed by CVA6 are of burst type INCR.
       | (ARBURST = 0b01)
   * - **ARLOCK**
     - M
     - | Yes
       | (optional)
     - | Provides information about the atomic characteristics of
       | a read transaction.
   * - **ARCACHE**
     - M
     - | Yes
       | (optional)
     - | Indicates how a read transaction is required to progress
       | through a system.
       | The memory is always of type Device Non-bufferable.
       | (ARCACHE = 0b0000)
   * - **ARPROT**
     - M
     - | Yes
     - | Protection attributes of a read transaction:
       | privilege, security level, and access type.
       | The value of ARPROT is always 0b000.
   * - **ARQOS**
     - M
     - | No
       | (optional)
     - | Quality of Service identifier for a read transaction.
       | ARQOS= 0b00
   * - **ARREGION**
     - M
     - | No
       | (optional)
     - | Region indicator for a read transaction.
       | ARREGION= 0b00
   * - **ARUSER**
     - M
     - | No
       | (optional)
     - | User-defined extension for the read address channel.
       | ARUSER= 0b00
   * - **ARVALID**
     - M
     - | Yes
       | (optional)
     - | Indicates that the read address channel signals are valid.
   * - **ARREADY**
     - S
     - | Yes
       | (optional)
     - | Indicates that a transfer on the read address channel can be
       | accepted.


Read data channel signals (Section A2.6)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

   Table 2.6 shows the AXI read data channel signals. Unless the description indicates otherwise, a signal can take any parameter if is supported.


.. list-table::
   :widths: 15 15 15 40
   :header-rows: 1

   * - **Signal**
     - **Src**
     - **Support**
     - **Description**
   * - **RID**
     - S
     - | Yes
       | (optional)
     - | The ID tag of the read data transfer.
       | CVA6 gives the id depending on the type of transaction.
       | See :ref:`transaction_identifiers_label`.
   * - **RDATA**
     - S
     - Yes
     - | Read data.
   * - **RLAST**
     - S
     - Yes
     - | Indicates whether this is the last data transfer in a read
       | transaction.
   * - **RUSER**
     - S
     - | Yes
       | (optional)
     - | User-defined extension for the read data channel.
       | Not supported. (RUSER= 0b00)
   * - **RVALID**
     - S
     - Yes
     - | Indicates that the read data channel signals are valid.
   * - **RREADY**
     - M
     - Yes
     - | Indicates that a transfer on the read data channel can be accepted.




Single Interface Requirements: Transaction structure (Section A3.4)
-------------------------------------------------------------------
|

This section describes the structure of transactions. The following sections define the address, data, and response
structures

|

.. _address_structure_label:

Address structure (Section A3.4.1)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The AXI protocol is burst-based. The Manager begins each burst by driving control information and the address of the first byte in the transaction to the Subordinate. As the burst progresses, the Subordinate must calculate the addresses of subsequent transfers in the burst.

**Burst length**

   The burst length is specified by:

   • **ARLEN[7:0]**, for read transfers
   • **AWLEN[7:0]**, for write transfers

   The burst length for AXI4 is defined as:

      ``Burst_Length = AxLEN[3:0] + 1``

   CVA6 has some limitation governing the use of bursts:

   * *All read transactions performed by CVA6 are of burst length less or equal to ICACHE_LINE_WIDTH/64.*
   * *All write transactions performed by CVA6 are of burst length equal to 1.*

**Burst size**

   The maximum number of bytes to transfer in each data transfer, or beat, in a burst, is specified by:

   * **ARSIZE[2:0]**, for read transfers
   * **AWSIZE[2:0]**, for write transfers

   *AXI DATA WIDTH used by CVA6 is 64-bit. For that, the maximum value can be taking by AXSIZE is 3 (8 bytes by transfer).*


**Burst type**

   The AXI protocol defines three burst types:

   * **FIXED**
   * **INCR**
   * **WRAP**

   The burst type is specified by:

   * **ARBURST[1:0]**, for read transfers
   * **AWBURST[1:0]**, for write transfers

   *All transactions performed by CVA6 are of burst type INCR. (AXBURST = 0b01)*


.. _data_read_and_write_structure_label:

Data read and write structure: Write strobes (Section A3.4.4)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

   The WSTRB[n:0] signals when HIGH, specify the byte lanes of the data bus that contain valid information. There is one write strobe
   for each 8 bits of the write data bus, therefore WSTRB[n] corresponds to WDATA[(8n)+7: (8n)].

   *AXI DATA WIDTH used by CVA6 is 64-bit. Therefore, Write Strobe width is equal to eight (n = 7).*

.. _read_and_write_response_structure_label:

Read and write response structure (Section A3.4.5)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

   The AXI protocol provides response signaling for both read and write transactions:

   * For read transactions, the response information from the Subordinate is signaled on the read data channel.
   * For write transactions, the response information is signaled on the write response channel.

   *CVA6 does not consider the responses sent by the memory except in the exclusive Access ( XRESP[1:0] = 0b01 ).*

Transaction Attributes: Memory types (Section A4)
--------------------------------------------------

   This section describes the attributes that determine how a transaction should be treated by the AXI subordinate that is connected to the CVA6.

   *AXCACHE always take 0b0000. The subordinate should be a Device Non-bufferable.*

   The required behavior for Device Non-bufferable memory is:

   * The write response must be obtained from the final destination.
   * Read data must be obtained from the final destination.
   * Transactions are Non-modifiable.
   * Reads must not be prefetched. Writes must not be merged.


.. _transaction_identifiers_label:

Transaction Identifiers (Section A5)
-------------------------------------

   The AXI protocol includes AXI ID transaction identifiers. A Manager can use these to identify separate transactions that must be returned in order.

   The CVA6 identify each type of transaction with a specific ID

      *For read transaction id can be 0 or 1.*

      *For write transaction id = 1.*

      *For Atomic operation id = 3. This ID must be sent in the write channels and also in the read channel if the transaction performed requires response data.*

AXI Ordering Model (Section A6)
-------------------------------

AXI ordering model overview (Section A6.1)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


   The AXI ordering model is based on the use of the transaction identifier, which is signaled on ARID or AWID.

   Transaction requests on the same channel, with the same ID and destination are guaranteed to remain in order.

   Transaction responses with the same ID are returned in the same order as the requests were issued.

   Write transaction requests, with the same destination are guaranteed to remain in order. Because all write transaction performed by CVA6 have the same ID.

   CVA6 can perform multiple outstanding write address transactions.

   CVA6 cannot perform a Read transaction and a Write one at the same time. Therefore there no ordering problems between Read and write transactions.


   The ordering model does not give any ordering guarantees between:

   * Transactions from different Managers
   * Read Transactions with different IDs
   * Transactions to different Memory locations

   If the CVA6 requires ordering between transactions that have no ordering guarantee, the Manager must wait to receive a response to the first transaction before issuing the second transaction.


Memory locations and Peripheral regions (Section A6.2)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

   The address map in AMBA is made up of Memory locations and Peripheral regions. But the AXI is associated to the memory interface of CVA6.

   A Memory location has all of the following properties:

   * A read of a byte from a Memory location returns the last value that was written to that byte location.
   * A write to a byte of a Memory location updates the value at that location to a new value that is obtained by a subsequent read of that location.
   * Reading or writing to a Memory location has no side-effects on any other Memory location.
   * Observation guarantees for Memory are given for each location.
   * The size of a Memory location is equal to the single-copy atomicity size for that component.


Transactions and ordering (Section A6.3)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

   A transaction is a read or a write to one or more address locations. The locations are determined by AxADDR and any relevant qualifiers such as the Non-secure bit in AxPROT.

   * Ordering guarantees are given only between accesses to the same Memory location or Peripheral region.
   * A transaction to a Peripheral region must be entirely contained within that region.
   * A transaction that spans multiple Memory locations has multiple ordering guarantees.

   *Transaction performed by CVA6 is of type Device. Because AxCACHE[1] deasserted.*

   Device transactions can be used to access Peripheral regions or Memory locations.

   *A write transaction performed by CVA6 is Non-bufferable (It is possible to send an early response to Bufferable write). Because AxCACHE[0] deasserted.*

Ordered write observation (Section A6.8)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
   To improve compatibility with interface protocols that support a different ordering model, a Subordinate interface can give stronger ordering guarantees for write transactions. A stronger ordering guarantee is known as Ordered Write Observation.

   *The CVA6 AXI interface exhibits Ordered Write Observation, so the Ordered_Write_Observation property is True.*

   An interface that exhibits Ordered Write Observation gives guarantees for write transactions that are not dependent on the destination or address:

   * A write W1 is guaranteed to be observed by a write W2, where W2 is issued after W1, from the same Manager, with the same ID.


.. _atomic_transactions_label:

Atomic transactions (Section E1.1)
-----------------------------------

   AMBA 5 introduces Atomic transactions, which perform more than just a single access and have an operation that is associated with the transaction. Atomic transactions enable sending the operation to the data, permitting the operation to be performed closer to where the data is located. Atomic transactions are suited to situations where the data is located a significant distance from the agent that must perform the operation.

   *CVA6 support just the AtomicLoad and AtomicSwap transaction. So AWATOP[5:4] can be 00, 10 or 11*

   *CVA6 perform only little-endian operation. So AWATOP[3] = 0*

   *For AtomicLoad, CVA6 support all arithmetic operations encoded on the lower-order AWATOP[2:0] signals*
