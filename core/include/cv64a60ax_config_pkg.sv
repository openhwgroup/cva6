// Copyright 2021 Thales DIS design services SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Jean-Roch COULON - Thales
//
// Copyright 2023 Commissariat a l'Energie Atomique et aux Energies
//                Alternatives (CEA)
//
// Author: Tanuj Khandelwal - CEA
// Date: January, 2025
// Description: CVA6 configuration package using the HPDcache as cache subsystem


package cva6_config_pkg;

  localparam CVA6ConfigXlen = 64;
  localparam CVA6ConfigRvfiTrace = 1;

  localparam CVA6ConfigAxiIdWidth = 4;
  localparam CVA6ConfigAxiAddrWidth = 39;
  localparam CVA6ConfigAxiDataWidth = 128;
  localparam CVA6ConfigDataUserWidth = 12;


`ifndef __UVMA_AXI_MACROS_SV__
  `define __UVMA_AXI_MACROS_SV__

  `define IFNDEF_DEFINE(name,value) \
    `ifndef name \
      `define name value \
  `endif

  `define UVMA_AXI_ADDR_MAX_WIDTH   39
  `define UVMA_AXI_DATA_MAX_WIDTH   128
  `define UVMA_AXI_USER_MAX_WIDTH   12
  `define UVMA_AXI_ID_MAX_WIDTH     4
  // `IFNDEF_DEFINE(UVMA_AXI_STRB_MAX_WIDTH , 8   )

  `define UVMA_AXI_MAX_NB_TXN_BURST  256
  `define UVMA_AXI_LOOP_MAX_WIDTH    8  
  `define UVMA_AXI_MMUSID_MAX_WIDTH  32 
  `define UVMA_AXI_MMUSSID_MAX_WIDTH 20 

`endif // __UVMA_AXI_MACROS_SV__


localparam config_pkg::cva6_user_cfg_t cva6_cfg = '{
   XLEN: unsigned'(CVA6ConfigXlen),
   VLEN: unsigned'(64),
   FpgaEn: bit'(0),  // for Xilinx and Altera
   FpgaAlteraEn: bit'(0),  // for Altera (only)
   TechnoCut: bit'(0),
   SuperscalarEn: bit'(0),
   ALUBypass: bit'(0),
   NrCommitPorts: unsigned'(2),
   AxiAddrWidth: unsigned'(CVA6ConfigAxiAddrWidth),
   AxiDataWidth: unsigned'(CVA6ConfigAxiDataWidth),
   AxiIdWidth: unsigned'(CVA6ConfigAxiIdWidth),
   AxiUserWidth: unsigned'(CVA6ConfigDataUserWidth),
   MemTidWidth: unsigned'(CVA6ConfigAxiIdWidth),
   NrLoadBufEntries: unsigned'(8),
   RVF: bit'(1),
   RVD: bit'(1),
   XF16: bit'(0),
   XF16ALT: bit'(0),
   XF8: bit'(0),
   RVA: bit'(1),
   RVB: bit'(1),
   ZKN: bit'(0),
   RVV: bit'(0),
   RVC: bit'(1),
   RVH: bit'(0),
   RVZCMT: bit'(0),
   RVZCB: bit'(1),
   RVZCMP: bit'(0),
   XFVec: bit'(0),
   CvxifEn: bit'(1),
   CoproType: config_pkg::COPRO_EXAMPLE,
   RVZiCond: bit'(1),
   RVZicntr: bit'(1),
   RVZihpm: bit'(1),
   NrScoreboardEntries: unsigned'(8),
   PerfCounterEn: bit'(1),
   MmuPresent: bit'(1),
   RVS: bit'(1),
   RVU: bit'(1),
   SoftwareInterruptEn: bit'(1),
   HaltAddress: 64'h800,
   ExceptionAddress: 64'h808,
   RASDepth: unsigned'(2),
   BTBEntries: unsigned'(16),
   BPType: config_pkg::BHT,
   BHTEntries: unsigned'(64),
   BHTHist: unsigned'(3),
   DmBaseAddress: 64'h300_0000,
   TvalEn: bit'(1),
   DirectVecOnly: bit'(0),
   NrPMPEntries: unsigned'(8),
   PMPCfgRstVal: {64{64'h0}},
   PMPAddrRstVal: {64{64'h0}},
   PMPEntryReadOnly: 64'd0,
   PMPNapotEn: bit'(1),
   NOCType: config_pkg::NOC_TYPE_AXI4_ATOP,
   NrNonIdempotentRules: unsigned'(2),
   NonIdempotentAddrBase: 1024'({64'b0, 64'b0}),
   NonIdempotentLength: 1024'({64'b0, 64'b0}),
   NrExecuteRegionRules: unsigned'(6),
   ExecuteRegionAddrBase: 1024'({64'h1_0000_0000, 64'h8000_0000, 64'h300_0000, 64'h0, 64'h2000_0000, 64'h8_0000_0000}),
   ExecuteRegionLength: 1024'({64'h2_0000_0000, 64'h1_0000, 64'h1000, 64'h1_0000, 64'h2000_0000, 64'h7_FFFF_FFFF}),
   NrCachedRegionRules: unsigned'(2),
   CachedRegionAddrBase: 1024'({64'h1_0000_0000, 64'h8000_0000}),
   CachedRegionLength: 1024'({64'h2_0000_0000, 64'h1_0000}),
   MaxOutstandingStores: unsigned'(7),
   DebugEn: bit'(1),
   SDTRIG: bit'(0),
   Mcontrol6: bit'(0),
   Icount: bit'(0),
   Etrigger: bit'(0),
   Itrigger: bit'(0),
   AxiBurstWriteEn: bit'(0),
   IcacheByteSize: unsigned'(32768),
   IcacheSetAssoc: unsigned'(8),
   IcacheLineWidth: unsigned'(512),
   DCacheType: config_pkg::HPDCACHE_WT,
   DcacheByteSize: unsigned'(32768),
   DcacheSetAssoc: unsigned'(8),
   DcacheLineWidth: unsigned'(512),
   DcacheFlushOnFence: bit'(0),
   DcacheInvalidateOnFlush: bit'(0),
   DataUserEn: unsigned'(0),
   WtDcacheWbufDepth: int'(8),
   FetchUserWidth: unsigned'(32),
   FetchUserEn: unsigned'(0),
   InstrTlbEntries: int'(16),
   DataTlbEntries: int'(16),
   UseSharedTlb: bit'(0),
   SharedTlbDepth: int'(64),
   NrLoadPipeRegs: int'(0),
   NrStorePipeRegs: int'(0),
   DcacheIdWidth: int'(3)
};

endpackage
