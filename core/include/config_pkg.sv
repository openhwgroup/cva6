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

    localparam NrMaxRules = 16;

    typedef struct packed {
      /// Number of commit ports, i.e., maximum number of instructions that the
      /// core can retire per cycle. It can be beneficial to have more commit
      /// ports than issue ports, for the scoreboard to empty out in case one
      /// instruction stalls a little longer.
      int unsigned NrCommitPorts;
      /// AXI parameters.
      int unsigned AxiAddrWidth;
      int unsigned AxiDataWidth;
      int unsigned AxiIdWidth;
      int unsigned AxiUserWidth;
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
      bit RCONDEXT;
      // Calculated
      bit RVF;
      bit RVD;
      bit FpPresent;
      bit NSX;
      int unsigned FLen;
      bit RVFVec;
      bit XF16Vec;
      bit XF16ALTVec;
      bit XF8Vec;
      int unsigned NrRgprPorts;
      int unsigned NrWbPorts;
      bit EnableAccelerator;
      // Debug Module
      // address to which a hart should jump when it was requested to halt
      logic [63:0] HaltAddress;
      logic [63:0] ExceptionAddress;
      /// Return address stack depth, good values are around 2 to 4.
      int unsigned RASDepth;
      /// Branch target buffer entries.
      int unsigned BTBEntries;
      /// Branch history (2-bit saturation counter) size, to keep track of
      /// branch otucomes.
      int unsigned BHTEntries;
      /// Offset of the debug module.
      logic [63:0] DmBaseAddress;
      /// Number of PMP entries.
      int unsigned NrPMPEntries;
      /// Set to the bus type in use.
      noc_type_e   NOCType;
      /// Physical Memory Attributes (PMAs)
      /// Number of non idempotent rules.
      int unsigned                      NrNonIdempotentRules;
      /// Base which needs to match.
      logic [NrMaxRules-1:0][63:0]      NonIdempotentAddrBase;
      /// Bit mask which bits to consider when matching the rule.
      logic [NrMaxRules-1:0][63:0]      NonIdempotentLength;
      /// Number of regions which have execute property.
      int unsigned                      NrExecuteRegionRules;
      /// Base which needs to match.
      logic [NrMaxRules-1:0][63:0]      ExecuteRegionAddrBase;
      /// Bit mask which bits to consider when matching the rule.
      logic [NrMaxRules-1:0][63:0]      ExecuteRegionLength;
      /// Number of regions which have cached property.
      int unsigned                      NrCachedRegionRules;
      /// Base which needs to match.
      logic [NrMaxRules-1:0][63:0]      CachedRegionAddrBase;
      /// Bit mask which bits to consider when matching the rule.
      logic [NrMaxRules-1:0][63:0]      CachedRegionLength;
    } cva6_cfg_t;

    localparam cva6_cfg_t cva6_cfg_default = '{
      NrCommitPorts: unsigned'(1),
      AxiAddrWidth: unsigned'(64),
      AxiDataWidth: unsigned'(64),
      AxiIdWidth: unsigned'(4),
      AxiUserWidth: unsigned'(32),
      NrLoadBufEntries: unsigned'(2),
      FpuEn: bit'(0),
      XF16: bit'(0),
      XF16ALT: bit'(0),
      XF8: bit'(0),
      RVA: bit'(0),
      RVV: bit'(0),
      RVC: bit'(1),
      RVZCB: bit'(1),
      XFVec: bit'(0),
      CvxifEn: bit'(1),
      EnableZiCond: bit'(0),
      // Extended
      RVF: bit'(0),
      RVD: bit'(0),
      FpPresent: bit'(0),
      NSX: bit'(0),
      FLen: unsigned'(0),
      RVFVec: bit'(0),
      XF16Vec: bit'(0),
      XF16ALTVec: bit'(0),
      XF8Vec: bit'(0),
      NrRgprPorts: unsigned'(0),
      NrWbPorts: unsigned'(0),
      EnableAccelerator: bit'(0),
      HaltAddress: 64'h800,
      ExceptionAddress: 64'h808,
      RASDepth:      2,
      BTBEntries:    32,
      BHTEntries:    128,
      DmBaseAddress: 64'h0,
      NrPMPEntries:  8,
      NOCType:       NOC_TYPE_AXI4_ATOP,
      // idempotent region
      NrNonIdempotentRules:  unsigned'(2),
      NonIdempotentAddrBase: 1024'({64'b0, 64'b0}),
      NonIdempotentLength:   1024'({64'b0, 64'b0}),
      NrExecuteRegionRules:  unsigned'(3),
      //                      DRAM,          Boot ROM,   Debug Module
      ExecuteRegionAddrBase: 1024'({64'h8000_0000, 64'h1_0000, 64'h0}),
      ExecuteRegionLength:   1024'({64'h40000000,  64'h10000,  64'h1000}),
      // cached region
      NrCachedRegionRules:   unsigned'(1),
      CachedRegionAddrBase:  1024'({64'h8000_0000}),
      CachedRegionLength:    1024'({64'h40000000})
    };

    /// Empty configuration to sanity check proper parameter passing. Whenever
    /// you develop a module that resides within the core, assign this constant.
    localparam cva6_cfg_t cva6_cfg_empty = '0;


    /// Utility function being called to check parameters. Not all values make
    /// sense for all parameters, here is the place to sanity check them.
    function automatic void check_cfg (cva6_cfg_t Cfg);
      // pragma translate_off
      `ifndef VERILATOR
        assert(Cfg.RASDepth > 0);
        assert(2**$clog2(Cfg.BTBEntries)  == Cfg.BTBEntries);
        assert(2**$clog2(Cfg.BHTEntries)  == Cfg.BHTEntries);
        assert(Cfg.NrNonIdempotentRules <= NrMaxRules);
        assert(Cfg.NrExecuteRegionRules <= NrMaxRules);
        assert(Cfg.NrCachedRegionRules  <= NrMaxRules);
        assert(Cfg.NrPMPEntries <= 16);
      `endif
      // pragma translate_on
    endfunction

    function automatic logic range_check(logic[63:0] base, logic[63:0] len, logic[63:0] address);
      // if len is a power of two, and base is properly aligned, this check could be simplified
      // Extend base by one bit to prevent an overflow.
      return (address >= base) && (({1'b0, address}) < (65'(base)+len));
    endfunction : range_check


    function automatic logic is_inside_nonidempotent_regions (cva6_cfg_t Cfg, logic[63:0] address);
      logic[NrMaxRules-1:0] pass;
      pass = '0;
      for (int unsigned k = 0; k < Cfg.NrNonIdempotentRules; k++) begin
        pass[k] = range_check(Cfg.NonIdempotentAddrBase[k], Cfg.NonIdempotentLength[k], address);
      end
      return |pass;
    endfunction : is_inside_nonidempotent_regions

    function automatic logic is_inside_execute_regions (cva6_cfg_t Cfg, logic[63:0] address);
      // if we don't specify any region we assume everything is accessible
      logic[NrMaxRules-1:0] pass;
      pass = '0;
      for (int unsigned k = 0; k < Cfg.NrExecuteRegionRules; k++) begin
        pass[k] = range_check(Cfg.ExecuteRegionAddrBase[k], Cfg.ExecuteRegionLength[k], address);
      end
      return |pass;
    endfunction : is_inside_execute_regions

    function automatic logic is_inside_cacheable_regions (cva6_cfg_t Cfg, logic[63:0] address);
      automatic logic[NrMaxRules-1:0] pass;
      pass = '0;
      for (int unsigned k = 0; k < Cfg.NrCachedRegionRules; k++) begin
        pass[k] = range_check(Cfg.CachedRegionAddrBase[k], Cfg.CachedRegionLength[k], address);
      end
      return |pass;
    endfunction : is_inside_cacheable_regions

endpackage
