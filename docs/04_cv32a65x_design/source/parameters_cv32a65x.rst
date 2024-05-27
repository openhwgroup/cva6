..
   Copyright 2024 Thales DIS France SAS
   Licensed under the Solderpad Hardware License, Version 2.1 (the "License");
   you may not use this file except in compliance with the License.
   SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
   You may obtain a copy of the License at https://solderpad.org/licenses/

   Original Author: Jean-Roch COULON - Thales

.. _cv32a65x_PARAMETERS:

.. list-table:: cv32a65x parameter configuration
   :header-rows: 1

   * - Name
     - description
     - Value

   * - XLEN
     - General Purpose Register Size (in bits)
     - 32

   * - RVA
     - Atomic RISC-V extension
     - False

   * - RVB
     - Bit manipulation RISC-V extension
     - True

   * - RVV
     - Vector RISC-V extension
     - False

   * - RVC
     - Compress RISC-V extension
     - True

   * - RVH
     - Hypervisor RISC-V extension
     - False

   * - RVZCB
     - Zcb RISC-V extension
     - True

   * - RVZCMP
     - Zcmp RISC-V extension
     - False

   * - RVZiCond
     - Zicond RISC-V extension
     - False

   * - RVF
     - Floating Point
     - False

   * - RVD
     - Floating Point
     - False

   * - XF16
     - Non standard 16bits Floating Point extension
     - False

   * - XF16ALT
     - Non standard 16bits Floating Point Alt extension
     - False

   * - XF8
     - Non standard 8bits Floating Point extension
     - False

   * - XFVec
     - Non standard Vector Floating Point extension
     - False

   * - PerfCounterEn
     - Perf counters
     - False

   * - MmuPresent
     - MMU
     - False

   * - RVS
     - Supervisor mode
     - False

   * - RVU
     - User mode
     - False

   * - DebugEn
     - Debug support
     - False

   * - DmBaseAddress
     - Base address of the debug module
     - 0x0

   * - HaltAddress
     - Address to jump when halt request
     - 0x800

   * - ExceptionAddress
     - Address to jump when exception
     - 0x808

   * - TvalEn
     - Tval Support Enable
     - False

   * - NrPMPEntries
     - PMP entries number
     - 8

   * - PMPCfgRstVal
     - PMP CSR configuration reset values
     - [0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]

   * - PMPAddrRstVal
     - PMP CSR address reset values
     - [0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]

   * - PMPEntryReadOnly
     - PMP CSR read-only bits
     - 0

   * - NrNonIdempotentRules
     - PMA non idempotent rules number
     - 2

   * - NonIdempotentAddrBase
     - PMA NonIdempotent region base address
     - [0b0, 0b0]

   * - NonIdempotentLength
     - PMA NonIdempotent region length
     - [0b0, 0b0]

   * - NrExecuteRegionRules
     - PMA regions with execute rules number
     - 3

   * - ExecuteRegionAddrBase
     - PMA Execute region base address
     - [0x80000000, 0x10000, 0x0]

   * - ExecuteRegionLength
     - PMA Execute region address base
     - [0x40000000, 0x10000, 0x1000]

   * - NrCachedRegionRules
     - PMA regions with cache rules number
     - 1

   * - CachedRegionAddrBase
     - PMA cache region base address
     - [0x80000000]

   * - CachedRegionLength
     - PMA cache region rules
     - [0x40000000]

   * - CvxifEn
     - CV-X-IF coprocessor interface enable
     - True

   * - NOCType
     - NOC bus type
     - config_pkg::NOC_TYPE_AXI4_ATOP

   * - AxiAddrWidth
     - AXI address width
     - 64

   * - AxiDataWidth
     - AXI data width
     - 64

   * - AxiIdWidth
     - AXI ID width
     - 4

   * - AxiUserWidth
     - AXI User width
     - 32

   * - AxiBurstWriteEn
     - AXI burst in write
     - False

   * - MemTidWidth
     - TODO
     - 4

   * - IcacheByteSize
     - Instruction cache size (in bytes)
     - 2048

   * - IcacheSetAssoc
     - Instruction cache associativity (number of ways)
     - 2

   * - IcacheLineWidth
     - Instruction cache line width
     - 128

   * - DCacheType
     - Cache Type
     - config_pkg::HPDCACHE

   * - DcacheIdWidth
     - Data cache ID
     - 1

   * - DcacheByteSize
     - Data cache size (in bytes)
     - 32768

   * - DcacheSetAssoc
     - Data cache associativity (number of ways)
     - 8

   * - DcacheLineWidth
     - Data cache line width
     - 128

   * - DataUserEn
     - User field on data bus enable
     - 0

   * - WtDcacheWbufDepth
     - Write-through data cache write buffer depth
     - 2

   * - FetchUserEn
     - User field on fetch bus enable
     - 0

   * - FetchUserWidth
     - Width of fetch user field
     - 32

   * - FpgaEn
     - Is FPGA optimization of CV32A6
     - False

   * - NrCommitPorts
     - Number of commit ports
     - 1

   * - NrLoadPipeRegs
     - Load cycle latency number
     - 0

   * - NrStorePipeRegs
     - Store cycle latency number
     - 0

   * - NrScoreboardEntries
     - Scoreboard length
     - 4

   * - NrLoadBufEntries
     - Load buffer entry buffer
     - 2

   * - MaxOutstandingStores
     - Maximum number of outstanding stores
     - 7

   * - RASDepth
     - Return address stack depth
     - 2

   * - BTBEntries
     - Branch target buffer entries
     - 0

   * - BHTEntries
     - Branch history entries
     - 32

   * - InstrTlbEntries
     - MMU instruction TLB entries
     - 2

   * - DataTlbEntries
     - MMU data TLB entries
     - 2

   * - UseSharedTlb
     - MMU option to use shared TLB
     - True

   * - SharedTlbDepth
     - MMU depth of shared TLB
     - 64
