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

   * - NrCommitPorts
     - Number of commit ports
     - 1

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

   * - NrLoadBufEntries
     - TO_BE_COMPLETED
     - 1

   * - FpuEn
     - FPU is enabled
     - 0

   * - XF16
     - TO_BE_COMPLETED
     - 0

   * - XF16ALT
     - TO_BE_COMPLETED
     - 0

   * - XF8
     - TO_BE_COMPLETED
     - 0

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

   * - RVZCB
     - Zcb RISC-V extension
     - 1

   * - XFVec
     - TO_BE_COMPLETED
     - 0

   * - CvxifEn
     - CV-X-IF coprocessor interface is supported
     - 1

   * - ZiCondExtEn
     - Zicond RISC-V extension is enabled
     - 0

   * - RVF
     - Single precision FP RISC-V extension
     - 0

   * - RVD
     - Double precision FP RISC-V extension
     - 0

   * - FpPresent
     - Floating point is present
     - 0

   * - NSX
     - TO_BE_COMPLETED
     - 0

   * - FLen
     - TO_BE_COMPLETED
     - 0

   * - RVFVec
     - Vector floating point extension
     - 0

   * - XF16Vec
     - 16 bits vector floating point extension
     - 0

   * - XF16ALTVec
     - TO_BE_COMPLETED
     - 0

   * - XF8Vec
     - 8 bits vector floating point extension
     - 0

   * - NrRgprPorts
     - TO_BE_COMPLETED
     - 0

   * - NrWbPorts
     - TO_BE_COMPLETED
     - 0

   * - EnableAccelerator
     - Accelerate Port coprocessor interface
     - 0

   * - RVS
     - Supervisor mode
     - 0

   * - RVU
     - User mode
     - 0

   * - HaltAddress
     - Address to jump when halt request
     - 64'h800

   * - ExceptionAddress
     - Address to jump when exception 
     - 64'h808

   * - RASDepth
     - Return address stack depth
     - 2

   * - BTBEntries
     - Branch target buffer entries
     - 0

   * - BHTEntries
     - Branch history entries
     - 32

   * - DmBaseAddress
     - Base address of the debug module
     - 64'h0

   * - TvalEn
     - Tval Support Enable
     - 0

   * - NrPMPEntries
     - Number of PMP entries
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

   * - NOCType
     - NOC bus type
     - config_pkg::NOC_TYPE_AXI4_ATOP

   * - NrNonIdempotentRules
     - Number of PMA non idempotent rules
     - 2

   * - NonIdempotentAddrBase
     - PMA NonIdempotent region base address
     - {64'b0 64'b0}

   * - NonIdempotentLength
     - PMA NonIdempotent region length
     - {64'b0 64'b0}

   * - NrExecuteRegionRules
     - Number of PMA regions with execute rules
     - 3

   * - ExecuteRegionAddrBase
     - PMA Execute region base address
     - {64'h8000_0000 64'h1_0000 64'h0}

   * - ExecuteRegionLength
     - PMA Execute region address base
     - {64'h40000000 64'h10000 64'h1000}

   * - NrCachedRegionRules
     - Number of PMA regions with cache rules
     - 1

   * - CachedRegionAddrBase
     - PMA cache region base address
     - {64'h8000_0000}

   * - CachedRegionLength
     - PMA cache region rules
     - {64'h40000000}

   * - MaxOutstandingStores
     - Maximum number of outstanding stores
     - 7

   * - DebugEn
     - Debug mode
     - 0

   * - NonIdemPotenceEn
     - Non idem potency
     - 0

   * - AxiBurstWriteEn
     - AXI burst in write
     - 0
