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
    // Number of commit ports
    int unsigned                 NrCommitPorts;
    // AXI address width
    int unsigned                 AxiAddrWidth;
    // AXI data width
    int unsigned                 AxiDataWidth;
    // AXI ID width
    int unsigned                 AxiIdWidth;
    // AXI User width
    int unsigned                 AxiUserWidth;
    // TO_BE_COMPLETED
    int unsigned                 NrLoadBufEntries;
    // FPU is enabled
    bit                          FpuEn;
    // TO_BE_COMPLETED
    bit                          XF16;
    // TO_BE_COMPLETED
    bit                          XF16ALT;
    // TO_BE_COMPLETED
    bit                          XF8;
    // Atomic RISC-V extension
    bit                          RVA;
    // Bit manipulation RISC-V extension
    bit                          RVB;
    // Vector RISC-V extension
    bit                          RVV;
    // Compress RISC-V extension
    bit                          RVC;
    // Zcb RISC-V extension
    bit                          RVZCB;
    // TO_BE_COMPLETED
    bit                          XFVec;
    // CV-X-IF coprocessor interface is supported
    bit                          CvxifEn;
    // Zicond RISC-V extension is enabled
    bit                          ZiCondExtEn;
    // Single precision FP RISC-V extension
    bit                          RVF;
    // Double precision FP RISC-V extension
    bit                          RVD;
    // Floating point is present
    bit                          FpPresent;
    // TO_BE_COMPLETED
    bit                          NSX;
    // TO_BE_COMPLETED
    int unsigned                 FLen;
    // Vector floating point extension
    bit                          RVFVec;
    // 16 bits vector floating point extension
    bit                          XF16Vec;
    // TO_BE_COMPLETED
    bit                          XF16ALTVec;
    // 8 bits vector floating point extension
    bit                          XF8Vec;
    // TO_BE_COMPLETED
    int unsigned                 NrRgprPorts;
    // TO_BE_COMPLETED
    int unsigned                 NrWbPorts;
    // Accelerate Port coprocessor interface
    bit                          EnableAccelerator;
    // Supervisor mode is enabled
    bit                          RVS;
    // User mode is enabled
    bit                          RVU;
    // Address to jump when halt request
    logic [63:0]                 HaltAddress;
    // Address to jump when exception 
    logic [63:0]                 ExceptionAddress;
    // Address stack depth
    int unsigned                 RASDepth;
    // Branch target buffer entries
    int unsigned                 BTBEntries;
    // Branch history entries
    int unsigned                 BHTEntries;
    // Base address of the debug module.
    logic [63:0]                 DmBaseAddress;
    // Tval Support Enable
    bit                          TvalEn;
    // Number of PMP entries.
    int unsigned                 NrPMPEntries;
    // PMP CSR configuration reset values
    logic [15:0][63:0]           PMPCfgRstVal;
    // PMP CSR address reset values
    logic [15:0][63:0]           PMPAddrRstVal;
    // PMP CSR read-only bits
    bit [15:0]                   PMPEntryReadOnly;
    // NOC bus type, can be AXI or Open Piton
    noc_type_e                   NOCType;
    // Number of PMA non idempotent rules
    int unsigned                 NrNonIdempotentRules;
    // PMA NonIdempotent region base address
    logic [NrMaxRules-1:0][63:0] NonIdempotentAddrBase;
    // PMA NonIdempotent region length
    logic [NrMaxRules-1:0][63:0] NonIdempotentLength;
    // PMA Execute region rules
    int unsigned                 NrExecuteRegionRules;
    // PMA Execute region base address
    logic [NrMaxRules-1:0][63:0] ExecuteRegionAddrBase;
    // PMA Execute region address base
    logic [NrMaxRules-1:0][63:0] ExecuteRegionLength;
    // PMA cache region properties
    int unsigned                 NrCachedRegionRules;
    // PMA cache region base address
    logic [NrMaxRules-1:0][63:0] CachedRegionAddrBase;
    // PMA cache region rules
    logic [NrMaxRules-1:0][63:0] CachedRegionLength;
    // Maximum number of outstanding stores
    int unsigned                 MaxOutstandingStores;
    // Debug mode is enabled
    bit                          DebugEn;
    // Non idem potency is enabled
    bit                          NonIdemPotenceEn;
    // AXI burst in write is enabled
    bit                          AxiBurstWriteEn;
  } cva6_cfg_t;


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
