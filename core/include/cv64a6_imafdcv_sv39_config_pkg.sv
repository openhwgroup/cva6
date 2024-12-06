// Copyright 2021 Thales DIS design services SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Jean-Roch COULON - Thales


package cva6_config_pkg;

  localparam CVA6ConfigXlen = 64;

  localparam CVA6ConfigNrCommitPorts = 2;

  localparam CVA6ConfigRVF = 1;
  localparam CVA6ConfigF16En = 0;
  localparam CVA6ConfigF16AltEn = 0;
  localparam CVA6ConfigF8En = 0;
  localparam CVA6ConfigFVecEn = 0;

  localparam CVA6ConfigCvxifEn = 0;
  localparam CVA6ConfigCExtEn = 1;
  localparam CVA6ConfigZcbExtEn = 0;
  localparam CVA6ConfigZcmpExtEn = 0;
  localparam CVA6ConfigAExtEn = 1;
  localparam CVA6ConfigBExtEn = 0;
  localparam CVA6ConfigHExtEn = 0;
  localparam CVA6ConfigVExtEn = 1;
  localparam CVA6ConfigRVZiCond = 0;

  localparam CVA6ConfigAxiIdWidth = 4;
  localparam CVA6ConfigAxiAddrWidth = 64;
  localparam CVA6ConfigAxiDataWidth = 64;
  localparam CVA6ConfigFetchUserEn = 0;
  localparam CVA6ConfigFetchUserWidth = 1; // Just not to raise warnings
  localparam CVA6ConfigDataUserEn = 0;
  localparam CVA6ConfigDataUserWidth = CVA6ConfigXlen;

  localparam CVA6ConfigIcacheByteSize = 16384;
  localparam CVA6ConfigIcacheSetAssoc = 4;
  localparam CVA6ConfigIcacheLineWidth = 128;
  localparam CVA6ConfigDcacheByteSize = 16384;
  localparam CVA6ConfigDcacheSetAssoc = 4;
  localparam CVA6ConfigDcacheLineWidth = 128;

  localparam CVA6ConfigDcacheIdWidth = 1;
  localparam CVA6ConfigMemTidWidth = 2;

  localparam CVA6ConfigWtDcacheWbufDepth = 8;

  localparam CVA6ConfigNrScoreboardEntries = 8;

  localparam CVA6ConfigNrLoadPipeRegs = 1;
  localparam CVA6ConfigNrStorePipeRegs = 0;
  localparam CVA6ConfigNrLoadBufEntries = 2;

  localparam CVA6ConfigRASDepth = 2;
  localparam CVA6ConfigBTBEntries = 32;
  localparam CVA6ConfigBHTEntries = 128;

  localparam CVA6ConfigTvalEn = 1;

  localparam CVA6ConfigNrPMPEntries = 8;

  localparam CVA6ConfigPerfCounterEn = 1;

  localparam config_pkg::cache_type_t CVA6ConfigDcacheType = config_pkg::WT;

  localparam CVA6ConfigMmuPresent = 1;

  localparam CVA6ConfigRvfiTrace = 1;

  localparam config_pkg::cva6_user_cfg_t cva6_cfg = '{
      XLEN: unsigned'(CVA6ConfigXlen),
      VLEN: unsigned'(64),
      PLEN: unsigned'(56),
      GPLEN: unsigned'(41),
      PPNW: unsigned'(44),
      FpgaEn: bit'(0),  // for Xilinx and Altera
      FpgaAlteraEn: bit'(0),  // for Altera (only)
      TechnoCut: bit'(0),
      SuperscalarEn: bit'(0),
      NrCommitPorts: unsigned'(CVA6ConfigNrCommitPorts),
      AxiAddrWidth: unsigned'(CVA6ConfigAxiAddrWidth),
      AxiDataWidth: unsigned'(CVA6ConfigAxiDataWidth),
      AxiIdWidth: unsigned'(CVA6ConfigAxiIdWidth),
      AxiUserWidth: unsigned'(CVA6ConfigDataUserWidth),
      MemTidWidth: unsigned'(CVA6ConfigMemTidWidth),
      NrLoadBufEntries: unsigned'(CVA6ConfigNrLoadBufEntries),
      RVF: bit'(CVA6ConfigRVF),
      RVD: bit'(CVA6ConfigRVF),
      XF16: bit'(CVA6ConfigF16En),
      XF16ALT: bit'(CVA6ConfigF16AltEn),
      XF8: bit'(CVA6ConfigF8En),
      RVA: bit'(CVA6ConfigAExtEn),
      RVB: bit'(CVA6ConfigBExtEn),
      RVV: bit'(CVA6ConfigVExtEn),
      RVC: bit'(CVA6ConfigCExtEn),
      RVH: bit'(CVA6ConfigHExtEn),
      RVZCB: bit'(CVA6ConfigZcbExtEn),
      RVZCMP: bit'(CVA6ConfigZcmpExtEn),
      XFVec: bit'(CVA6ConfigFVecEn),
      CvxifEn: bit'(CVA6ConfigCvxifEn),
      RVZiCond: bit'(CVA6ConfigRVZiCond),
      RVZicntr: bit'(1),
      RVZihpm: bit'(1),
      NrScoreboardEntries: unsigned'(CVA6ConfigNrScoreboardEntries),
      PerfCounterEn: bit'(CVA6ConfigPerfCounterEn),
      MmuPresent: bit'(CVA6ConfigMmuPresent),
      RVS: bit'(1),
      RVU: bit'(1),
      HaltAddress: 64'h800,
      ExceptionAddress: 64'h808,
      RASDepth: unsigned'(CVA6ConfigRASDepth),
      BTBEntries: unsigned'(CVA6ConfigBTBEntries),
      BHTEntries: unsigned'(CVA6ConfigBHTEntries),
      DmBaseAddress: 64'h0,
      TvalEn: bit'(CVA6ConfigTvalEn),
      DirectVecOnly: bit'(0),
      NrPMPEntries: unsigned'(CVA6ConfigNrPMPEntries),
      PMPCfgRstVal: {64{64'h0}},
      PMPAddrRstVal: {64{64'h0}},
      PMPEntryReadOnly: 64'd0,
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
      IcacheByteSize: unsigned'(CVA6ConfigIcacheByteSize),
      IcacheSetAssoc: unsigned'(CVA6ConfigIcacheSetAssoc),
      IcacheLineWidth: unsigned'(CVA6ConfigIcacheLineWidth),
      DcacheByteSize: unsigned'(CVA6ConfigDcacheByteSize),
      DcacheSetAssoc: unsigned'(CVA6ConfigDcacheSetAssoc),
      DcacheLineWidth: unsigned'(CVA6ConfigDcacheLineWidth),
      DataUserEn: unsigned'(CVA6ConfigDataUserEn),
      WtDcacheWbufDepth: int'(CVA6ConfigWtDcacheWbufDepth),
      FetchUserWidth: unsigned'(CVA6ConfigFetchUserWidth),
      FetchUserEn: unsigned'(CVA6ConfigFetchUserEn),
      DCacheType: CVA6ConfigDcacheType,
      InstrTlbEntries: int'(16),
      DataTlbEntries: int'(16),
      UseSharedTlb: bit'(0),
      SharedTlbDepth: int'(64),
      NrLoadPipeRegs: int'(CVA6ConfigNrLoadPipeRegs),
      NrStorePipeRegs: int'(CVA6ConfigNrStorePipeRegs),
      DcacheIdWidth: int'(CVA6ConfigDcacheIdWidth),
      TRANS_ID_BITS: $clog2(unsigned'(CVA6ConfigNrScoreboardEntries))
  };

  typedef struct packed {
    logic [cva6_cfg.XLEN-1:0] cause;  // cause of exception
    logic [cva6_cfg.XLEN-1:0] tval;  // additional information of causing exception (e.g.: instruction causing it),
    // address of LD/ST fault
    logic [cva6_cfg.GPLEN-1:0] tval2;  // additional information when the causing exception in a guest exception
    logic [31:0] tinst;  // transformed instruction information
    logic gva;  // signals when a guest virtual address is written to tval
    logic valid;
  } exception_t;

  // Accelerator - CVA6's
  typedef struct packed {
    logic                              req_valid;
    logic                              resp_ready;
    logic [31:0]                       insn;
    logic [cva6_cfg.XLEN-1:0]          rs1;
    logic [cva6_cfg.XLEN-1:0]          rs2;
    fpnew_pkg::roundmode_e             frm;
    logic [cva6_cfg.TRANS_ID_BITS-1:0] trans_id;
    logic                              store_pending;
    logic                              acc_cons_en; // Invalidation interface
    logic                              inval_ready; // Invalidation interface
  } accelerator_req_t;

  typedef struct packed {
    logic                                 req_ready;
    logic                                 resp_valid;
    logic [cva6_cfg.XLEN-1:0]             result;
    logic [cva6_cfg.TRANS_ID_BITS-1:0]    trans_id;
    exception_t                           exception;
    logic                                 store_pending;
    logic                                 store_complete;
    logic                                 load_complete;
    logic [4:0]                           fflags;
    logic                                 fflags_valid;
    logic                                 inval_valid; // Invalidation interface
    logic [63:0]                          inval_addr; // Invalidation interface
  } accelerator_resp_t;

  // Accelerator - CVA6's MMU
  typedef struct packed {
    logic                     acc_mmu_misaligned_ex;
    logic                     acc_mmu_req;
    logic [cva6_cfg.VLEN-1:0] acc_mmu_vaddr;
    logic                     acc_mmu_is_store;
  } acc_mmu_req_t;

  typedef struct packed {
    logic                     acc_mmu_dtlb_hit;
    logic [cva6_cfg.PPNW-1:0] acc_mmu_dtlb_ppn;
    logic                     acc_mmu_valid;
    logic [cva6_cfg.PLEN-1:0] acc_mmu_paddr;
    exception_t               acc_mmu_exception;
  } acc_mmu_resp_t;

  typedef struct packed {
    accelerator_req_t                     acc_req; // Insn/mem
    logic                                 acc_mmu_en; // MMU
    acc_mmu_resp_t                        acc_mmu_resp; // MMU
  } cva6_to_acc_t;

  typedef struct packed {
    accelerator_resp_t                    acc_resp; // Insn/mem
    acc_mmu_req_t                         acc_mmu_req; // MMU
  } acc_to_cva6_t;
endpackage
