// Copyright 2021 Thales DIS design services SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Jean-Roch COULON - Thales


package cva6_config_pkg;

    typedef enum logic {
      WB = 0,
      WT = 1
    } cache_type_t ;

    localparam CVA6ConfigXlen = 32;

    localparam CVA6ConfigFpuEn = 1;
    localparam CVA6ConfigF16En = 0;
    localparam CVA6ConfigF16AltEn = 0;
    localparam CVA6ConfigF8En = 0;
    localparam CVA6ConfigFVecEn = 0;

    localparam CVA6ConfigCvxifEn = 0;
    localparam CVA6ConfigCExtEn = 1;
    localparam CVA6ConfigAExtEn = 1;
    localparam CVA6ConfigBExtEn = 0;

    localparam CVA6ConfigAxiIdWidth = 4;
    localparam CVA6ConfigAxiAddrWidth = 64;
    localparam CVA6ConfigAxiDataWidth = 64;
    localparam CVA6ConfigFetchUserEn = 0;
    localparam CVA6ConfigFetchUserWidth = CVA6ConfigXlen;
    localparam CVA6ConfigDataUserEn = 0;
    localparam CVA6ConfigDataUserWidth = CVA6ConfigXlen;

    localparam CVA6ConfigRenameEn = 0;

    localparam CVA6ConfigIcacheByteSize = 16384;
    localparam CVA6ConfigIcacheSetAssoc = 4;
    localparam CVA6ConfigIcacheLineWidth = 128;
    localparam CVA6ConfigDcacheByteSize = 32768;
    localparam CVA6ConfigDcacheSetAssoc = 8;
    localparam CVA6ConfigDcacheLineWidth = 128;

    localparam CVA6ConfigDcacheIdWidth = 1;
    localparam CVA6ConfigMemTidWidth = 2;

    localparam CVA6ConfigWtDcacheWbufDepth = 8;

    localparam CVA6ConfigNrCommitPorts = 2;
    localparam CVA6ConfigNrScoreboardEntries = 8;

    localparam CVA6ConfigFPGAEn = 0;

    localparam CVA6ConfigNrLoadPipeRegs = 1;
    localparam CVA6ConfigNrStorePipeRegs = 0;

    localparam CVA6ConfigInstrTlbEntries = 2;
    localparam CVA6ConfigDataTlbEntries = 2;

    localparam CVA6ConfigRASDepth = 2;
    localparam CVA6ConfigBTBEntries = 32;
    localparam CVA6ConfigBHTEntries = 128;

    localparam CVA6ConfigNrPMPEntries = 8;

    localparam CVA6ConfigPerfCounterEn = 1;

    localparam CVA6ConfigDcacheType = WB;

    localparam CVA6ConfigMmuPresent = 1;

    `define RVFI_PORT

    // Do not modify
    `ifdef RVFI_PORT
       localparam CVA6ConfigRvfiTrace = 1;
    `else
       localparam CVA6ConfigRvfiTrace = 0;
    `endif

endpackage
