// Copyright 2023 Thales DIS France SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Jean-Roch COULON - Thales

package config_pkg;

  // ---------------
  // Global Config
  // ---------------
  localparam int unsigned ILEN = 32;
  localparam int unsigned NRET = 1;

  /// The NoC type is a top-level parameter, hence we need a bit more
  /// information on what protocol those type parameters are supporting.
  /// Currently two values are supported"
  typedef enum {
    /// The "classic" AXI4 protocol.
    NOC_TYPE_AXI4_ATOP,
    /// In the OpenPiton setting the WT cache is connected to the L15.
    NOC_TYPE_L15_BIG_ENDIAN,
    NOC_TYPE_L15_LITTLE_ENDIAN
  } noc_type_e;

  /// Cache type parameter
  typedef enum logic [1:0] {
    WB = 0,
    WT = 1,
    HPDCACHE = 2
  } cache_type_t;

  localparam NrMaxRules = 16;

  typedef struct packed {
    int unsigned XLEN;
    bit BITMANIP;
    int unsigned NR_SB_ENTRIES;
    bit FPGA_EN;  // Is FPGA optimization of CV32A6
    /// Number of commit ports, i.e., maximum number of instructions that the
    /// core can retire per cycle. It can be beneficial to have more commit
    /// ports than issue ports, for the scoreboard to empty out in case one
    /// instruction stalls a little longer.
    int unsigned                 NrCommitPorts;
    /// AXI parameters.
    int unsigned AxiAddrWidth;
    int unsigned AxiDataWidth;
    int unsigned AxiIdWidth;
    int unsigned AxiUserWidth;

    int unsigned MemTidWidth;

    // I$
    int unsigned IcacheByteSize;  // in byte
    int unsigned IcacheSetAssoc;  // number of ways
    int unsigned IcacheLineWidth; // number of ways
    // D$
    int unsigned DcacheByteSize;  // in byte
    int unsigned DcacheSetAssoc;  // number of ways
    int unsigned DcacheLineWidth; // number of ways

    int unsigned NrLoadBufEntries;
    bit FpuEn;
    bit XF16;
    bit XF16ALT;
    bit XF8;
    bit RVA;
    bit RVV;
    bit RVC;
    bit RVZCB;
    bit XFVec;
    bit CvxifEn;
    bit ZiCondExtEn;
    bit RVS;
    bit RVU;
    int unsigned FETCH_USER_WIDTH;
    int unsigned DATA_USER_WIDTH;
    int unsigned AXI_USER_WIDTH;
    bit DATA_USER_EN;
    bit FETCH_USER_EN;

    /// Return address stack depth, good values are around 2 to 4.
    int unsigned                 RASDepth;
    /// Branch target buffer entries.
    int unsigned                 BTBEntries;
    /// Branch history (2-bit saturation counter) size, to keep track of
    /// branch otucomes.
    int unsigned                 BHTEntries;
    /// Offset of the debug module.
    logic [63:0]                 DmBaseAddress;
    /// Number of PMP entries.
    int unsigned                 NrPMPEntries;
    /// Set to the bus type in use.
    noc_type_e                   NOCType;
    /// Physical Memory Attributes (PMAs)
    /// Number of non idempotent rules.
    int unsigned                 NrNonIdempotentRules;
    /// Base which needs to match.
    logic [NrMaxRules-1:0][63:0] NonIdempotentAddrBase;
    /// Bit mask which bits to consider when matching the rule.
    logic [NrMaxRules-1:0][63:0] NonIdempotentLength;
    /// Number of regions which have execute property.
    int unsigned                 NrExecuteRegionRules;
    /// Base which needs to match.
    logic [NrMaxRules-1:0][63:0] ExecuteRegionAddrBase;
    /// Bit mask which bits to consider when matching the rule.
    logic [NrMaxRules-1:0][63:0] ExecuteRegionLength;
    /// Number of regions which have cached property.
    int unsigned                 NrCachedRegionRules;
    /// Base which needs to match.
    logic [NrMaxRules-1:0][63:0] CachedRegionAddrBase;
    /// Bit mask which bits to consider when matching the rule.
    logic [NrMaxRules-1:0][63:0] CachedRegionLength;
    /// Maximum number of outstanding stores.
    int unsigned                 MaxOutstandingStores;
    bit                          DebugEn;
  } cva6_user_cfg_t;

  typedef struct packed {
    int unsigned XLEN;
    bit BITMANIP;
    int unsigned NR_SB_ENTRIES;
    // depending on the number of scoreboard entries we need that many bits
    // to uniquely identify the entry in the scoreboard
    int unsigned TRANS_ID_BITS;
    int unsigned ASID_WIDTH;
    bit FPGA_EN;
    int unsigned VLEN;  // virtual address length
    int unsigned PLEN;  // physical address length
    bit IS_XLEN32;
    bit IS_XLEN64;
    int unsigned XLEN_ALIGN_BYTES;
    int unsigned ModeW;
    int unsigned ASIDW;
    int unsigned PPNW;
    riscv::vm_mode_t MODE_SV;
    int unsigned SV;
    int unsigned VPN2;

    /// Number of commit ports, i.e., maximum number of instructions that the
    /// core can retire per cycle. It can be beneficial to have more commit
    /// ports than issue ports, for the scoreboard to empty out in case one
    /// instruction stalls a little longer.
    int unsigned                 NrCommitPorts;
    /// AXI parameters.
    int unsigned                 AxiAddrWidth;
    int unsigned                 AxiDataWidth;
    int unsigned                 AxiIdWidth;
    int unsigned                 AxiUserWidth;
    int unsigned                 NrLoadBufEntries;
    bit                          FpuEn;
    bit                          XF16;
    bit                          XF16ALT;
    bit                          XF8;
    bit                          RVA;
    bit                          RVV;
    bit                          RVC;
    bit                          RVZCB;
    bit                          XFVec;
    bit                          CvxifEn;
    bit                          ZiCondExtEn;
    // Calculated
    bit                          RVF;
    bit                          RVD;
    bit                          FpPresent;
    bit                          NSX;
    int unsigned                 FLen;
    bit                          RVFVec;
    bit                          XF16Vec;
    bit                          XF16ALTVec;
    bit                          XF8Vec;
    int unsigned                 NrRgprPorts;
    int unsigned                 NrWbPorts;
    bit                          EnableAccelerator;
    bit                          RVS;    //Supervisor mode
    bit                          RVU;    //User mode

    logic [63:0]                 HaltAddress;
    logic [63:0]                 ExceptionAddress;
    int unsigned                 RASDepth;
    int unsigned                 BTBEntries;
    int unsigned                 BHTEntries;
    logic [63:0]                 DmBaseAddress;
    int unsigned                 NrPMPEntries;
    noc_type_e                   NOCType;
    int unsigned                 NrNonIdempotentRules;
    logic [NrMaxRules-1:0][63:0] NonIdempotentAddrBase;
    logic [NrMaxRules-1:0][63:0] NonIdempotentLength;
    int unsigned                 NrExecuteRegionRules;
    logic [NrMaxRules-1:0][63:0] ExecuteRegionAddrBase;
    logic [NrMaxRules-1:0][63:0] ExecuteRegionLength;
    int unsigned                 NrCachedRegionRules;
    logic [NrMaxRules-1:0][63:0] CachedRegionAddrBase;
    logic [NrMaxRules-1:0][63:0] CachedRegionLength;
    int unsigned                 MaxOutstandingStores;
    bit                          DebugEn;

    int unsigned FETCH_USER_WIDTH;
    int unsigned DATA_USER_WIDTH;
    bit AXI_USER_EN;
    int unsigned AXI_USER_WIDTH;
    int unsigned MEM_TID_WIDTH;
    int unsigned DCACHE_MAX_TX;
    // I$
    int unsigned ICACHE_SET_ASSOC;
    int unsigned ICACHE_SET_ASSOC_WIDTH;
    int unsigned ICACHE_INDEX_WIDTH;  // in bit, contains also offset width
    int unsigned ICACHE_TAG_WIDTH;
    int unsigned ICACHE_LINE_WIDTH;  // in bit
    int unsigned ICACHE_USER_LINE_WIDTH;  // in bit
    // D$
    int unsigned DCACHE_SET_ASSOC;
    int unsigned DCACHE_SET_ASSOC_WIDTH;
    int unsigned DCACHE_INDEX_WIDTH;  // in bit, contains also offset width
    int unsigned DCACHE_TAG_WIDTH;
    int unsigned DCACHE_LINE_WIDTH;
    int unsigned DCACHE_USER_LINE_WIDTH;  // in bit
    int unsigned DCACHE_USER_WIDTH;

    bit DATA_USER_EN;
    bit FETCH_USER_EN;
    int unsigned FETCH_WIDTH;
    int unsigned INSTR_PER_FETCH;
    // maximum instructions we can fetch on one request (we support compressed instructions)
    int unsigned LOG2_INSTR_PER_FETCH;
  } cva6_cfg_t;

  function automatic cva6_cfg_t build_config(cva6_user_cfg_t CVA6Cfg);
    bit IS_XLEN32 = (CVA6Cfg.XLEN == 32) ? 1'b1 : 1'b0;
    bit IS_XLEN64 = (CVA6Cfg.XLEN == 32) ? 1'b0 : 1'b1;
    bit RVF = (IS_XLEN64 | IS_XLEN32) & CVA6Cfg.FpuEn;
    bit RVD = (IS_XLEN64 ? 1 : 0) & CVA6Cfg.FpuEn;
    bit FpPresent = RVF | RVD | CVA6Cfg.XF16 | CVA6Cfg.XF16ALT | CVA6Cfg.XF8;
    bit NSX = CVA6Cfg.XF16 | CVA6Cfg.XF16ALT | CVA6Cfg.XF8 | CVA6Cfg.XFVec;  // Are non-standard extensions present?
    int unsigned FLen = RVD ? 64 :  // D ext.
    RVF ? 32 :  // F ext.
    CVA6Cfg.XF16 ? 16 :  // Xf16 ext.
    CVA6Cfg.XF16ALT ? 16 :  // Xf16alt ext.
    CVA6Cfg.XF8 ? 8 :  // Xf8 ext.
    1;  // Unused in case of no FP

    // Transprecision floating-point extensions configuration
    bit RVFVec     = RVF             & CVA6Cfg.XFVec & FLen>32; // FP32 vectors available if vectors and larger fmt enabled
    bit XF16Vec    = CVA6Cfg.XF16    & CVA6Cfg.XFVec & FLen>16; // FP16 vectors available if vectors and larger fmt enabled
    bit XF16ALTVec = CVA6Cfg.XF16ALT & CVA6Cfg.XFVec & FLen>16; // FP16ALT vectors available if vectors and larger fmt enabled
    bit XF8Vec     = CVA6Cfg.XF8     & CVA6Cfg.XFVec & FLen>8;  // FP8 vectors available if vectors and larger fmt enabled

    bit EnableAccelerator = CVA6Cfg.RVV;  // Currently only used by V extension (Ara)
    int unsigned NrWbPorts = (CVA6Cfg.CvxifEn || EnableAccelerator) ? 5 : 4;

    riscv::vm_mode_t MODE_SV = (CVA6Cfg.XLEN == 32) ? riscv::ModeSv32 : riscv::ModeSv39;
    int unsigned VLEN = (CVA6Cfg.XLEN == 32) ? 32 : 64;
    int unsigned PLEN = (CVA6Cfg.XLEN == 32) ? 34 : 56;
    int unsigned FETCH_WIDTH = 32;
    int unsigned INSTR_PER_FETCH = CVA6Cfg.RVC == 1'b1 ? (FETCH_WIDTH / 16) : 1;

    int unsigned ICACHE_SET_ASSOC = CVA6Cfg.IcacheSetAssoc;
    int unsigned DCACHE_SET_ASSOC = CVA6Cfg.DcacheSetAssoc;
    int unsigned ICACHE_INDEX_WIDTH = $clog2(CVA6Cfg.IcacheByteSize / ICACHE_SET_ASSOC);
    int unsigned DCACHE_INDEX_WIDTH = $clog2(CVA6Cfg.DcacheByteSize / DCACHE_SET_ASSOC);
    int unsigned DCACHE_OFFSET_WIDTH = $clog2(CVA6Cfg.DcacheLineWidth / 8);

    return
    '{
      XLEN: CVA6Cfg.XLEN,
      BITMANIP: CVA6Cfg.BITMANIP,
      NR_SB_ENTRIES: CVA6Cfg.NR_SB_ENTRIES,
      TRANS_ID_BITS: $clog2(CVA6Cfg.NR_SB_ENTRIES),
      ASID_WIDTH: unsigned'((CVA6Cfg.XLEN == 64) ? 16 : 1),
      FPGA_EN: CVA6Cfg.FPGA_EN,
      VLEN: VLEN,
      PLEN: PLEN,
      IS_XLEN32: IS_XLEN32,
      IS_XLEN64: IS_XLEN64,
      XLEN_ALIGN_BYTES: $clog2(CVA6Cfg.XLEN / 8),
      ModeW: unsigned'((CVA6Cfg.XLEN == 32) ? 1 : 4),
      ASIDW: unsigned'((CVA6Cfg.XLEN == 32) ? 9 : 16),
      PPNW: unsigned'((CVA6Cfg.XLEN == 32) ? 22 : 44),
      MODE_SV: MODE_SV,
      SV: unsigned'((MODE_SV == riscv::ModeSv32) ? 32 : 39),
      VPN2: unsigned'((VLEN - 31 < 8) ? VLEN - 31 : 8),
      NrCommitPorts: CVA6Cfg.NrCommitPorts,
      AxiAddrWidth: CVA6Cfg.AxiAddrWidth,
      AxiDataWidth: CVA6Cfg.AxiDataWidth,
      AxiIdWidth: CVA6Cfg.AxiIdWidth,
      AxiUserWidth: CVA6Cfg.AxiUserWidth,
      NrLoadBufEntries: CVA6Cfg.NrLoadBufEntries,
      FpuEn: CVA6Cfg.FpuEn,
      XF16: CVA6Cfg.XF16,
      XF16ALT: CVA6Cfg.XF16ALT,
      XF8: CVA6Cfg.XF8,
      RVA: CVA6Cfg.RVA,
      RVV: CVA6Cfg.RVV,
      RVC: CVA6Cfg.RVC,
      RVZCB: CVA6Cfg.RVZCB,
      XFVec: CVA6Cfg.XFVec,
      CvxifEn: CVA6Cfg.CvxifEn,
      ZiCondExtEn: CVA6Cfg.ZiCondExtEn,
      RVF: bit'(RVF),
      RVD: bit'(RVD),
      FpPresent: bit'(FpPresent),
      NSX: bit'(NSX),
      FLen: unsigned'(FLen),
      RVFVec: bit'(RVFVec),
      XF16Vec: bit'(XF16Vec),
      XF16ALTVec: bit'(XF16ALTVec),
      XF8Vec: bit'(XF8Vec),
      NrRgprPorts: unsigned'(2),
      NrWbPorts: unsigned'(NrWbPorts),
      EnableAccelerator: bit'(EnableAccelerator),
      RVS: CVA6Cfg.RVS,
      RVU: CVA6Cfg.RVU,
      HaltAddress: CVA6Cfg.HaltAddress,
      ExceptionAddress: CVA6Cfg.ExceptionAddress,
      RASDepth: CVA6Cfg.RASDepth,
      BTBEntries: CVA6Cfg.BTBEntries,
      BHTEntries: CVA6Cfg.BHTEntries,
      DmBaseAddress: CVA6Cfg.DmBaseAddress,
      NrPMPEntries: CVA6Cfg.NrPMPEntries,
      NOCType: CVA6Cfg.NOCType,
      NrNonIdempotentRules: CVA6Cfg.NrNonIdempotentRules,
      NonIdempotentAddrBase: CVA6Cfg.NonIdempotentAddrBase,
      NonIdempotentLength: CVA6Cfg.NonIdempotentLength,
      NrExecuteRegionRules: CVA6Cfg.NrExecuteRegionRules,
      ExecuteRegionAddrBase: CVA6Cfg.ExecuteRegionAddrBase,
      ExecuteRegionLength: CVA6Cfg.ExecuteRegionLength,
      NrCachedRegionRules: CVA6Cfg.NrCachedRegionRules,
      CachedRegionAddrBase: CVA6Cfg.CachedRegionAddrBase,
      CachedRegionLength: CVA6Cfg.CachedRegionLength,
      MaxOutstandingStores: CVA6Cfg.MaxOutstandingStores,
      DebugEn: CVA6Cfg.DebugEn,

      FETCH_USER_WIDTH: CVA6Cfg.FETCH_USER_WIDTH,
      DATA_USER_WIDTH: CVA6Cfg.DATA_USER_WIDTH,
      AXI_USER_EN: CVA6Cfg.DATA_USER_EN | CVA6Cfg.FETCH_USER_EN,
      AXI_USER_WIDTH: CVA6Cfg.AXI_USER_WIDTH,
      MEM_TID_WIDTH: CVA6Cfg.MemTidWidth,
      DCACHE_MAX_TX: 2 ** CVA6Cfg.MemTidWidth,

      ICACHE_SET_ASSOC: ICACHE_SET_ASSOC,
      ICACHE_SET_ASSOC_WIDTH: $clog2(ICACHE_SET_ASSOC),
      ICACHE_INDEX_WIDTH: ICACHE_INDEX_WIDTH,
      ICACHE_TAG_WIDTH: PLEN - ICACHE_INDEX_WIDTH,
      ICACHE_LINE_WIDTH: CVA6Cfg.IcacheLineWidth,
      ICACHE_USER_LINE_WIDTH: (CVA6Cfg.AXI_USER_WIDTH == 1) ? 4 : CVA6Cfg.IcacheLineWidth,

      DCACHE_SET_ASSOC: DCACHE_SET_ASSOC,
      DCACHE_SET_ASSOC_WIDTH: $clog2(DCACHE_SET_ASSOC),
      DCACHE_INDEX_WIDTH: DCACHE_INDEX_WIDTH,
      DCACHE_TAG_WIDTH: PLEN - DCACHE_INDEX_WIDTH,
      DCACHE_LINE_WIDTH: CVA6Cfg.DcacheLineWidth,
      DCACHE_USER_LINE_WIDTH: (CVA6Cfg.AXI_USER_WIDTH == 1) ? 4 : CVA6Cfg.DcacheLineWidth,
      DCACHE_USER_WIDTH: CVA6Cfg.DATA_USER_WIDTH,
      DCACHE_OFFSET_WIDTH: DCACHE_OFFSET_WIDTH,
      DCACHE_NUM_WORDS: 2 ** (DCACHE_INDEX_WIDTH - DCACHE_OFFSET_WIDTH),

      DATA_USER_EN: CVA6Cfg.DATA_USER_EN,
      FETCH_USER_EN: CVA6Cfg.FETCH_USER_EN,
      FETCH_WIDTH: FETCH_WIDTH,
      INSTR_PER_FETCH: INSTR_PER_FETCH,
      LOG2_INSTR_PER_FETCH: CVA6Cfg.RVC == 1'b1 ? $clog2(INSTR_PER_FETCH) : 1
    }
    ;

  endfunction

  /// Empty configuration to sanity check proper parameter passing. Whenever
  /// you develop a module that resides within the core, assign this constant.
  localparam cva6_cfg_t cva6_cfg_empty = '0;

  /// Utility function being called to check parameters. Not all values make
  /// sense for all parameters, here is the place to sanity check them.
  function automatic void check_cfg(cva6_cfg_t Cfg);
    // pragma translate_off
`ifndef VERILATOR
    assert (Cfg.RASDepth > 0);
    assert (2 ** $clog2(Cfg.BTBEntries) == Cfg.BTBEntries);
    assert (2 ** $clog2(Cfg.BHTEntries) == Cfg.BHTEntries);
    assert (Cfg.NrNonIdempotentRules <= NrMaxRules);
    assert (Cfg.NrExecuteRegionRules <= NrMaxRules);
    assert (Cfg.NrCachedRegionRules <= NrMaxRules);
    assert (Cfg.NrPMPEntries <= 16);
    assert (!Cfg.STD_CACHE || (Cfg.PLEN == 56 && Cfg.VLEN == 64));
    assert (Cfg.VLEN >= Cfg.PLEN);
`endif
    // pragma translate_on
  endfunction

  function automatic logic range_check(logic [63:0] base, logic [63:0] len, logic [63:0] address);
    // if len is a power of two, and base is properly aligned, this check could be simplified
    // Extend base by one bit to prevent an overflow.
    return (address >= base) && (({1'b0, address}) < (65'(base) + len));
  endfunction : range_check


  function automatic logic is_inside_nonidempotent_regions(cva6_cfg_t Cfg, logic [63:0] address);
    logic [NrMaxRules-1:0] pass;
    pass = '0;
    for (int unsigned k = 0; k < Cfg.NrNonIdempotentRules; k++) begin
      pass[k] = range_check(Cfg.NonIdempotentAddrBase[k], Cfg.NonIdempotentLength[k], address);
    end
    return |pass;
  endfunction : is_inside_nonidempotent_regions

  function automatic logic is_inside_execute_regions(cva6_cfg_t Cfg, logic [63:0] address);
    // if we don't specify any region we assume everything is accessible
    logic [NrMaxRules-1:0] pass;
    pass = '0;
    for (int unsigned k = 0; k < Cfg.NrExecuteRegionRules; k++) begin
      pass[k] = range_check(Cfg.ExecuteRegionAddrBase[k], Cfg.ExecuteRegionLength[k], address);
    end
    return |pass;
  endfunction : is_inside_execute_regions

  function automatic logic is_inside_cacheable_regions(cva6_cfg_t Cfg, logic [63:0] address);
    automatic logic [NrMaxRules-1:0] pass;
    pass = '0;
    for (int unsigned k = 0; k < Cfg.NrCachedRegionRules; k++) begin
      pass[k] = range_check(Cfg.CachedRegionAddrBase[k], Cfg.CachedRegionLength[k], address);
    end
    return |pass;
  endfunction : is_inside_cacheable_regions

endpackage
