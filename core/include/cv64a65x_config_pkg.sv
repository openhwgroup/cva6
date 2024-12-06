// Copyright 2022 Thales DIS design services SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Jean-Roch COULON - Thales

package cva6_config_pkg;

  localparam CVA6ConfigXlen = 64;

  localparam CVA6ConfigRvfiTrace = 1;

  localparam CVA6ConfigAxiIdWidth = 6;  // axi_pkg.sv
  localparam CVA6ConfigAxiAddrWidth = 64;  // axi_pkg.sv
  localparam CVA6ConfigAxiDataWidth = 64;  // axi_pkg.sv
  localparam CVA6ConfigDataUserWidth = 64;  // axi_pkg.sv

  localparam CVA6ConfigSuperscalarEn = 0;  // superscalar

  localparam CVA6ConfigNrScoreboardEntries = 8;  // cvxif_pkg.sv

  localparam config_pkg::cache_type_t CVA6ConfigDcacheType = config_pkg::HPDCACHE;

  localparam config_pkg::cva6_user_cfg_t cva6_cfg = '{
      XLEN: unsigned'(CVA6ConfigXlen),
      FpgaEn: bit'(0),
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
      RVV: bit'(0),
      RVC: bit'(1),
      RVH: bit'(0),
      RVZCB: bit'(1),
      RVZCMP: bit'(0),
      XFVec: bit'(0),
      CvxifEn: bit'(1),
      RVZiCond: bit'(1),
      NrScoreboardEntries: unsigned'(CVA6ConfigNrScoreboardEntries),
      PerfCounterEn: bit'(1),
      MmuPresent: bit'(1),
      RVS: bit'(1),
      RVU: bit'(1),
      HaltAddress: 64'h800,
      ExceptionAddress: 64'h808,
      RASDepth: unsigned'(2),
      BTBEntries: unsigned'(32),
      BHTEntries: unsigned'(128),
      DmBaseAddress: 64'h0,
      TvalEn: bit'(0),
      NrPMPEntries: unsigned'(8),
      PMPCfgRstVal: {16{64'h0}},
      PMPAddrRstVal: {16{64'h0}},
      PMPEntryReadOnly: 16'd0,
      NOCType: config_pkg::NOC_TYPE_AXI4_ATOP,
      NrNonIdempotentRules: unsigned'(2),
      NonIdempotentAddrBase: 1024'({64'b0, 64'b0}),
      NonIdempotentLength: 1024'({64'b0, 64'b0}),
      NrExecuteRegionRules: unsigned'(3),
      ExecuteRegionAddrBase: 1024'({64'h8000_0000, 64'h1_0000, 64'h0}),
      ExecuteRegionLength: 1024'({64'h40000000, 64'h10000, 64'h1000}),
      NrCachedRegionRules: unsigned'(1),
      CachedRegionAddrBase: 1024'({64'h8000_0000}),
      CachedRegionLength: 1024'({64'h40000000}),
      MaxOutstandingStores: unsigned'(7),
      DebugEn: bit'(1),
      AxiBurstWriteEn: bit'(0),
      IcacheByteSize: unsigned'(32768),
      IcacheSetAssoc: unsigned'(8),
      IcacheLineWidth: unsigned'(512),
      DCacheType: config_pkg::HPDCACHE,
      DcacheByteSize: unsigned'(32768),
      DcacheSetAssoc: unsigned'(8),
      DcacheLineWidth: unsigned'(512),
      DataUserEn: unsigned'(1),
      WtDcacheWbufDepth: int'(8),
      FetchUserWidth: unsigned'(64),
      FetchUserEn: unsigned'(0),
      InstrTlbEntries: int'(16),
      DataTlbEntries: int'(16),
      UseSharedTlb: bit'(0),
      SharedTlbDepth: int'(64),
      NrLoadPipeRegs: int'(1),
      NrStorePipeRegs: int'(0),
      DcacheIdWidth: int'(3)
  };

endpackage
