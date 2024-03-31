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
     - 0

   * - RVB
     - Bit manipulation RISC-V extension
     - 1

   * - RVV
     - Vector RISC-V extension
     - 0

   * - RVC
     - Compress RISC-V extension
     - 1

   * - RVH
     - Hypervisor RISC-V extension
     - 0

   * - RVZCB
     - Zcb RISC-V extension
     - 1

   * - RVZCMP
     - Zcmp RISC-V extension
     - 0

   * - RVZiCond
     - Zicond RISC-V extension
     - 0

   * - FpuEn
     - Floating Point
     - 0

   * - XF16
     - Non standard 16bits Floating Point extension
     - 0

   * - XF16ALT
     - Non standard 16bits Floating Point Alt extension
     - 0

   * - XF8
     - Non standard 8bits Floating Point extension
     - 0

   * - XFVec
     - Non standard Vector Floating Point extension
     - 0

   * - RVS
     - Supervisor mode
     - 0

   * - RVU
     - User mode
     - 0

   * - DebugEn
     - Debug support
     - 0

   * - DmBaseAddress
     - Base address of the debug module
     - 64'h0

   * - HaltAddress
     - Address to jump when halt request
     - 64'h800

   * - ExceptionAddress
     - Address to jump when exception
     - 64'h808

   * - TvalEn
     - Tval Support Enable
     - 0

   * - NrPMPEntries
     - PMP entries number
     - 8

   * - PMPCfgRstVal
     - PMP CSR configuration reset values
     - {16{64'h0}}

   * - PMPAddrRstVal
     - PMP CSR address reset values
     - {16{64'h0}}

   * - PMPEntryReadOnly
     - PMP CSR read-only bits
     - 16'd0

   * - NrNonIdempotentRules
     - PMA non idempotent rules number
     - 2

   * - NonIdempotentAddrBase
     - PMA NonIdempotent region base address
     - {64'b0 64'b0}

   * - NonIdempotentLength
     - PMA NonIdempotent region length
     - {64'b0 64'b0}

   * - NrExecuteRegionRules
     - PMA regions with execute rules number
     - 3

   * - ExecuteRegionAddrBase
     - PMA Execute region base address
     - {64'h8000_0000 64'h1_0000 64'h0}

   * - ExecuteRegionLength
     - PMA Execute region address base
     - {64'h40000000 64'h10000 64'h1000}

   * - NrCachedRegionRules
     - PMA regions with cache rules number
     - 1

   * - CachedRegionAddrBase
     - PMA cache region base address
     - {64'h8000_0000}

   * - CachedRegionLength
     - PMA cache region rules
     - {64'h40000000}

   * - CvxifEn
     - CV-X-IF coprocessor interface enable
     - 1

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
     - 0

   * - MemTidWidth
     - TODO
     - 2

   * - IcacheByteSize
     - Instruction cache size (in bytes)
     - 2048

   * - IcacheSetAssoc
     - Instruction cache associativity (number of ways)
     - 2

   * - IcacheLineWidth
     - Instruction cache line width
     - 128

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

   * - FetchUserEn
     - User field on fetch bus enable
     - 0

   * - FetchUserWidth
     - Width of fetch user field
     - 32

   * - FPGAEn
     - Is FPGA optimization of CV32A6
     - 0

   * - NrCommitPorts
     - Number of commit ports
     - 1

   * - NrScoreboardEntries
     - Scoreboard length
     - 4

   * - NrLoadBufEntries
     - Load buffer entry buffer
     - 1

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
