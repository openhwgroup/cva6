// Copyright 2021 Thales DIS design services SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Jean-Roch COULON (jean-roch.coulon@thalesgroup.com)


package cva6_config_pkg;

    localparam CVA6ConfigXlen = 32;

    localparam CVA6ConfigFpuEn = 0;
    localparam CVA6ConfigF16En = 0;
    localparam CVA6ConfigF16AltEn = 0;
    localparam CVA6ConfigF8En = 0;
    localparam CVA6ConfigFVecEn = 0;

    localparam CVA6ConfigCvxifEn = 0;
    localparam CVA6ConfigCExtEn = 0;
    localparam CVA6ConfigAExtEn = 1;

    localparam CVA6ConfigFetchUserEn = 0;
    localparam CVA6ConfigFetchUserWidth = CVA6ConfigXlen;
    localparam CVA6ConfigDataUserEn = 0;
    localparam CVA6ConfigDataUserWidth = CVA6ConfigXlen;

    localparam CVA6ConfigRenameEn = 0;

    localparam CVA6ConfigIcacheSetAssoc = 2;
    localparam CVA6ConfigDcacheSetAssoc = 2;

    localparam CVA6ConfigNrCommitPorts = 1;
    localparam CVA6ConfigNrScoreboardEntries = 4;

    localparam CVA6ConfigFPGAEn = 1;

    localparam CVA6ConfigNrLoadPipeRegs = 1;
    localparam CVA6ConfigNrStorePipeRegs = 0;

    localparam CVA6ConfigInstrTlbEntries = 2;
    localparam CVA6ConfigDataTlbEntries = 2;

    // This is the new user config interface system. If you need to parameterize something
    // within Ariane add a field here and assign a default value to the config. Please make
    // sure to add a propper parameter check to the `check_cfg` function.
    localparam NrMaxRules = 16;
    typedef struct packed {
      int                               RASDepth;
      int                               BTBEntries;
      int                               BHTEntries;
      // PMAs
      int unsigned                      NrNonIdempotentRules;  // Number of non idempotent rules
      logic [NrMaxRules-1:0][63:0]      NonIdempotentAddrBase; // base which needs to match
      logic [NrMaxRules-1:0][63:0]      NonIdempotentLength;   // bit mask which bits to consider when matching the rule
      int unsigned                      NrExecuteRegionRules;  // Number of regions which have execute property
      logic [NrMaxRules-1:0][63:0]      ExecuteRegionAddrBase; // base which needs to match
      logic [NrMaxRules-1:0][63:0]      ExecuteRegionLength;   // bit mask which bits to consider when matching the rule
      int unsigned                      NrCachedRegionRules;   // Number of regions which have cached property
      logic [NrMaxRules-1:0][63:0]      CachedRegionAddrBase;  // base which needs to match
      logic [NrMaxRules-1:0][63:0]      CachedRegionLength;    // bit mask which bits to consider when matching the rule
      // cache config
      bit                               AxiCompliant;          // set to 1 when using in conjunction with 64bit AXI bus adapter
      bit                               SwapEndianess;         // set to 1 to swap endianess inside L1.5 openpiton adapter
      //
      logic [63:0]                      DmBaseAddress;         // offset of the debug module
      int unsigned                      NrPMPEntries;          // Number of PMP entries
    } ariane_cfg_t;

    localparam ariane_cfg_t ArianeDefaultConfig = '{
      RASDepth: 2,
      BTBEntries: 32,
      BHTEntries: 128,
      // idempotent region
      NrNonIdempotentRules: 2,
      NonIdempotentAddrBase: {64'b0, 64'b0},
      NonIdempotentLength:   {64'b0, 64'b0},
      NrExecuteRegionRules: 3,
      //                      DRAM,          Boot ROM,   Debug Module
      ExecuteRegionAddrBase: {64'h8000_0000, 64'h1_0000, 64'h0},
      ExecuteRegionLength:   {64'h40000000,  64'h10000,  64'h1000},
      // cached region
      NrCachedRegionRules:    1,
      CachedRegionAddrBase:  {64'h8000_0000},
      CachedRegionLength:    {64'h40000000},
      //  cache config
      AxiCompliant:           1'b1,
      SwapEndianess:          1'b0,
      // debug
      DmBaseAddress:          64'h0,
      NrPMPEntries:           8
    };

endpackage
