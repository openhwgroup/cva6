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

    typedef struct packed {
      int unsigned NrCommitPorts;
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
    } cva6_cfg_t;

    localparam cva6_cfg_t cva6_cfg_default = {
      unsigned'(1),      // NrCommitPorts
      unsigned'(64),     // AxiAddrWidth
      unsigned'(64),     // AxiDataWidth
      unsigned'(4),      // AxiIdWidth
      unsigned'(32),     // AxiUserWidth
      unsigned'(2),      // NrLoadBufEntries
      bit'(0),           // FpuEn
      bit'(0),           // XF16
      bit'(0),           // XF16ALT
      bit'(0),           // XF8
      bit'(0),           // RVA
      bit'(0),           // RVV
      bit'(1),           // RVC
      bit'(0),           // RVZCB
      bit'(0),           // XFVec
      bit'(1),           // CvxifEn
      bit'(0),           // EnableZiCond
      // Extended
      bit'(0),           // RVF
      bit'(0),           // RVD
      bit'(0),           // FpPresent
      bit'(0),           // NSX
      unsigned'(0),      // FLen
      bit'(0),           // RVFVec
      bit'(0),           // XF16Vec
      bit'(0),           // XF16ALTVec
      bit'(0),           // XF8Vec
      unsigned'(0),      // NrRgprPorts
      unsigned'(0),      // NrWbPorts
      bit'(0),           // EnableAccelerator
      64'h800,           // HaltAddress
      64'h808            // ExceptionAddress
    } ;

    localparam cva6_cfg_t cva6_cfg_empty = {
      unsigned'(0),      // NrCommitPorts
      unsigned'(0),      // AxiAddrWidth
      unsigned'(0),      // AxiDataWidth
      unsigned'(0),      // AxiIdWidth
      unsigned'(0),      // AxiUserWidth
      unsigned'(0),      // NrLoadBufEntries
      bit'(0),           // FpuEn
      bit'(0),           // XF16
      bit'(0),           // XF16ALT
      bit'(0),           // XF8
      bit'(0),           // RVA
      bit'(0),           // RVV
      bit'(0),           // RVC
      bit'(0),           // RVZCB
      bit'(0),           // XFVec
      bit'(0),           // CvxifEn
      bit'(0),           // EnableZiCond
      // Extended
      bit'(0),           // RVF
      bit'(0),           // RVD
      bit'(0),           // FpPresent
      bit'(0),           // NSX
      unsigned'(0),      // FLen
      bit'(0),           // RVFVec
      bit'(0),           // XF16Vec
      bit'(0),           // XF16ALTVec
      bit'(0),           // XF8Vec
      unsigned'(0),      // NrRgprPorts
      unsigned'(0),      // NrWbPorts
      bit'(0),           // EnableAccelerator
      64'h0,             // HaltAddress
      64'h0              // ExceptionAddress
    } ;


endpackage
