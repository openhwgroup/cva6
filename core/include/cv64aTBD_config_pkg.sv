// Copyright 2022 Thales DIS design services SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Ludovic PION - CEA

package cva6_config_pkg;


  localparam CVA6ConfigSuperscalarEn = 1;  // superscalar

  localparam config_pkg::cva6_user_cfg_t cva6_cfg = '{
      XLEN: unsigned'(64),
      FpgaEn: bit'(0),
      NrCommitPorts: unsigned'(2),
      AxiAddrWidth: unsigned'(64),
      AxiDataWidth: unsigned'(64), //Ideally we would like to target 256 bits of data
      AxiIdWidth: unsigned'(6),
      AxiUserWidth: unsigned'(32),
      MemTidWidth: unsigned'(6),
      NrLoadBufEntries: unsigned'(8),
      RVF: bit'(1),
      RVD: bit'(1),
      XF16: bit'(0),
      XF16ALT: bit'(0),
      XF8: bit'(0),
      RVA: bit'(1),
      RVB: bit'(1),
      RVV: bit'(0),
      RVC: bit'(1),
      RVH: bit'(0),
      RVZCB: bit'(1),
      RVZCMP: bit'(0),
      XFVec: bit'(0),
      CvxifEn: bit'(1),
      RVZiCond: bit'(1),
      NrScoreboardEntries: unsigned'(8),
      PerfCounterEn: bit'(1),
      MmuPresent: bit'(1),
      RVS: bit'(1),
      RVU: bit'(1),
      HaltAddress: 64'h800,
      ExceptionAddress: 64'h808,
      RASDepth: unsigned'(4),
      BTBEntries: unsigned'(16),
      BHTEntries: unsigned'(64),
      DmBaseAddress: 64'h0,
      TvalEn: bit'(1),
      NrPMPEntries: unsigned'(8),
      PMPCfgRstVal: {16{64'h0}},
      PMPAddrRstVal: {16{64'h0}},
      PMPEntryReadOnly: 16'd0,
      NOCType: config_pkg::NOC_TYPE_AXI4_ATOP,
      NrNonIdempotentRules: unsigned'(0),
      NonIdempotentAddrBase: 1024'({64'b0, 64'b0}),
      NonIdempotentLength: 1024'({64'b0, 64'b0}),
      NrExecuteRegionRules: unsigned'(4),
      ExecuteRegionAddrBase: 1024'({64'h1_0000_0000, 64'h8000_0000, 4'h1_0000, 64'h0}),
      ExecuteRegionLength: 1024'({64'h2_0000_0000, 64'h1_0000, 64'h1_0000, 64'h100}),
      NrCachedRegionRules: unsigned'(1),
      CachedRegionAddrBase: 1024'({64'h8000_0000}),
      CachedRegionLength: 1024'({64'h4000_0000}),
      MaxOutstandingStores: unsigned'(7),
      DebugEn: bit'(1),
      AxiBurstWriteEn: bit'(1),
      IcacheByteSize: unsigned'(32768),
      IcacheSetAssoc: unsigned'(8),
      IcacheLineWidth: unsigned'(512),
      DCacheType: config_pkg::HPDCACHE,
      DcacheByteSize: unsigned'(32768),
      DcacheSetAssoc: unsigned'(8),
      DcacheLineWidth: unsigned'(512),
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
