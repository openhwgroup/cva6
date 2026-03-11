// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Author: Enrico Zelioli <ezelioli@iis.ee.ethz.ch>

package cva6tb_pkg;

  `include "axi/typedef.svh"
  `include "register_interface/typedef.svh"
  `include "rvfi_types.svh"

  import ariane_pkg::*;

  // The memory attributes describe this SoC's address map, not the core, so they
  // are set here for every configuration. They go into the user configuration,
  // before build_config, because it derives NonIdemPotenceEn from them.
  function automatic config_pkg::cva6_cfg_t gen_cva6_cfg(config_pkg::cva6_user_cfg_t user_cfg);
    config_pkg::cva6_user_cfg_t cfg = user_cfg;
    // Everything below the SPM -- the error slave and the regbus peripherals -- is
    // device space: stores there must not be merged, nor loads issued speculatively.
    cfg.NrNonIdempotentRules  = unsigned'(1);
    cfg.NonIdempotentAddrBase = 1024'({64'h0000_0000});
    cfg.NonIdempotentLength   = 1024'({64'h2000_0000});
    cfg.NrExecuteRegionRules  = unsigned'(4);
    cfg.ExecuteRegionAddrBase = 1024'({64'h8000_0000, 64'h2000_0000, 64'(56'h01A0_0000), 64'h0001_0000});
    cfg.ExecuteRegionLength   = 1024'({64'h4000_0000, 64'h0010_0000, 64'(56'h0000_4000), 64'h0001_0000});
    cfg.NrCachedRegionRules   = unsigned'(2);
    cfg.CachedRegionAddrBase  = 1024'({64'h8000_0000, 64'h2000_0000});
    cfg.CachedRegionLength    = 1024'({64'h4000_0000, 64'h0010_0000});
    return build_config_pkg::build_config(cfg);
  endfunction

  // CVA6 configuration struct
  localparam config_pkg::cva6_user_cfg_t CVA6UserCfg = cva6_config_pkg::cva6_cfg;
  localparam config_pkg::cva6_cfg_t          CVA6Cfg = gen_cva6_cfg(CVA6UserCfg);

  ////////////////////////////
  // Test SoC configuration //
  ////////////////////////////

  localparam int unsigned AxiXbarMasters   = 1;
  localparam int unsigned AxiXbarSlaves    = 4;
  localparam int unsigned AxiSlvIdWidth    = CVA6UserCfg.AxiIdWidth + $clog2(AxiXbarMasters);
  localparam int unsigned AxiXbarAddrRules = 5;
  localparam int unsigned AxiSlvIdErrSlv   = 0;
  localparam int unsigned AxiSlvIdReg      = 1;
  localparam int unsigned AxiSlvIdDram     = 2;
  localparam int unsigned AxiSlvIdSpm      = 3;

  localparam int unsigned RegbusOutNum     = 8;
  localparam int unsigned RegbusRulesNum   = 8;
  localparam int unsigned RegbusErrId      = 0;
  localparam int unsigned RegbusBootromId  = 1;
  localparam int unsigned RegbusClintId    = 2;
  localparam int unsigned RegbusPlicId     = 3;
  localparam int unsigned RegbusPCRsId     = 4;
  localparam int unsigned RegbusConsoleId  = 5;
  localparam int unsigned RegbusRTCTimerId = 6;
  localparam int unsigned RegbusClicId     = 7;

  localparam int unsigned NumClicIntIrqs   = 18;
  localparam int unsigned NumClicExtIrqs   = 256 - NumClicIntIrqs;
  localparam int unsigned NumClicIrqs      = NumClicIntIrqs + NumClicExtIrqs;

  localparam int unsigned NumPlicIntIrqs   = 16;
  localparam int unsigned NumPlicExtIrqs   = 32 - NumPlicIntIrqs;
  localparam int unsigned NumPlicIrqs      = NumPlicIntIrqs + NumPlicExtIrqs;

  // AXI xbar configuration
  localparam axi_pkg::xbar_cfg_t AxiXbarCfg = '{
    NoSlvPorts:         AxiXbarMasters,
    NoMstPorts:         AxiXbarSlaves,
    MaxMstTrans:        24,
    MaxSlvTrans:        24,
    FallThrough:        0,
    LatencyMode:        axi_pkg::CUT_ALL_PORTS,
    PipelineStages:     0,
    AxiIdWidthSlvPorts: CVA6UserCfg.AxiIdWidth,
    AxiIdUsedSlvPorts:  CVA6UserCfg.AxiIdWidth,
    UniqueIds:          0,
    AxiAddrWidth:       CVA6UserCfg.AxiAddrWidth,
    AxiDataWidth:       CVA6UserCfg.AxiDataWidth,
    NoAddrRules:        AxiXbarAddrRules,
    default:            '0
  };

  //////////////////////
  // Type definitions //
  //////////////////////

  localparam type rvfi_instr_t        = `RVFI_INSTR_T(CVA6Cfg);
  localparam type rvfi_csr_elmt_t     = `RVFI_CSR_ELMT_T(CVA6Cfg);
  localparam type rvfi_csr_t          = `RVFI_CSR_T(CVA6Cfg, rvfi_csr_elmt_t);
  localparam type rvfi_probes_instr_t = `RVFI_PROBES_INSTR_T(CVA6Cfg);
  localparam type rvfi_probes_csr_t   = `RVFI_PROBES_CSR_T(CVA6Cfg);
  localparam type rvfi_probes_t       = struct packed {
    rvfi_probes_csr_t   csr;
    rvfi_probes_instr_t instr;
  };

  localparam type axi_addr_t   = logic [CVA6UserCfg.AxiAddrWidth-1:0];
  localparam type axi_data_t   = logic [CVA6UserCfg.AxiDataWidth-1:0];
  localparam type axi_strb_t   = logic [CVA6UserCfg.AxiDataWidth/8-1:0];
  localparam type axi_mst_id_t = logic [CVA6UserCfg.AxiIdWidth-1:0];
  localparam type axi_slv_id_t = logic [AxiSlvIdWidth-1:0];
  localparam type axi_user_t   = logic [CVA6UserCfg.AxiUserWidth-1:0];

  `AXI_TYPEDEF_ALL(axi_mst, axi_addr_t, axi_mst_id_t, axi_data_t, axi_strb_t, axi_user_t);
  `AXI_TYPEDEF_ALL(axi_slv, axi_addr_t, axi_slv_id_t, axi_data_t, axi_strb_t, axi_user_t);
  typedef axi_mst_resp_t axi_mst_rsp_t;
  typedef axi_slv_resp_t axi_slv_rsp_t;

  localparam type reg_addr_t = logic [31:0];
  localparam type reg_idx_t  = logic [cf_math_pkg::idx_width(RegbusOutNum)-1:0];

  `REG_BUS_TYPEDEF_ALL(reg, reg_addr_t, logic [31:0], logic [3:0])

  // Type for address map entries
  typedef struct packed {
    logic [5:0] idx;
    axi_addr_t  start_addr;
    axi_addr_t  end_addr;
  } addr_rule_t;

  // Type for regbus address map entries
  typedef struct packed {
    logic [5:0] idx;
    reg_addr_t  start_addr;
    reg_addr_t  end_addr;
  } reg_addr_rule_t;

  //////////////////////////
  // Test SoC address map //
  //////////////////////////

  // AXI error slave region
  localparam axi_addr_t AxiErrBaseAddr       = CVA6UserCfg.AxiAddrWidth'(64'h0000_0000);
  localparam axi_addr_t AxiErrSize           = CVA6UserCfg.AxiAddrWidth'(64'h0001_0000);
  // Regbus region
  localparam axi_addr_t RegbusBaseAddr       = CVA6UserCfg.AxiAddrWidth'(64'h0001_0000);
  localparam axi_addr_t RegbusSize           = CVA6UserCfg.AxiAddrWidth'(64'h100F_0000);
  // SPM region
  localparam axi_addr_t SpmBaseAddr          = CVA6UserCfg.AxiAddrWidth'(64'h2000_0000);
  localparam axi_addr_t SpmSize              = CVA6UserCfg.AxiAddrWidth'(64'h0010_0000);
  // Uncached alias of the DRAM region
  localparam axi_addr_t DramUncachedBaseAddr = CVA6UserCfg.AxiAddrWidth'(64'h4000_0000);
  localparam axi_addr_t DramUncachedSize     = CVA6UserCfg.AxiAddrWidth'(64'h1000_0000);
  localparam axi_addr_t DramUncachedMask     = CVA6UserCfg.AxiAddrWidth'(64'h3FFF_FFFF);
  // DRAM region (cached range)
  localparam axi_addr_t DramBaseAddr         = CVA6UserCfg.AxiAddrWidth'(64'h8000_0000);
  localparam axi_addr_t DramSize             = CVA6UserCfg.AxiAddrWidth'(64'h1000_0000);

  // Regbus error slave region
  localparam reg_addr_t RegErrBaseAddr   = 32'h1007_0000;
  localparam reg_addr_t RegErrSize       = 32'h0009_0000;
  // Bootrom region
  localparam reg_addr_t BootromBaseAddr  = 32'h0001_0000;
  localparam reg_addr_t BootromSize      = 32'h0000_1000;
  // CLINT region
  localparam reg_addr_t ClintBaseAddr    = 32'h0204_0000;
  localparam reg_addr_t ClintSize        = 32'h0004_0000;
  // PLIC region
  localparam reg_addr_t PlicBaseAddr     = 32'h0C00_0000;
  localparam reg_addr_t PlicSize         = 32'h0400_0000;
  // Platform Control Registers region
  localparam reg_addr_t PCRsBaseAddr     = 32'h1000_0000;
  localparam reg_addr_t PCRsSize         = 32'h0000_1000;
  // Sim console region
  localparam reg_addr_t ConsoleBaseAddr  = 32'h1000_1000;
  localparam reg_addr_t ConsoleSize      = 32'h0000_1000;
  // RTC timer region
  localparam reg_addr_t RTCTimerBaseAddr = 32'h1000_2000;
  localparam reg_addr_t RTCTimerSize     = 32'h0000_1000;
  // CLIC region
  localparam reg_addr_t ClicBaseAddr     = 32'h1004_0000;
  localparam reg_addr_t ClicSize         = 32'h0003_0000;

  localparam addr_rule_t [AxiXbarAddrRules-1:0] AxiMap = {
    addr_rule_t'{ idx: AxiSlvIdErrSlv, start_addr: AxiErrBaseAddr,       end_addr: (AxiErrBaseAddr + AxiErrSize)             }, // AXI error slave
    addr_rule_t'{ idx: AxiSlvIdReg,    start_addr: RegbusBaseAddr,       end_addr: (RegbusBaseAddr + RegbusSize)             }, // Regbus
    addr_rule_t'{ idx: AxiSlvIdSpm,    start_addr: SpmBaseAddr,          end_addr: (SpmBaseAddr + SpmSize)                   }, // AXI SPM
    addr_rule_t'{ idx: AxiSlvIdDram,   start_addr: DramUncachedBaseAddr, end_addr: (DramUncachedBaseAddr + DramUncachedSize) }, // AXI Sim Mem Alias
    addr_rule_t'{ idx: AxiSlvIdDram,   start_addr: DramBaseAddr,         end_addr: (DramBaseAddr + DramSize)                 }  // AXI Sim Mem
  };

  localparam reg_addr_rule_t [RegbusRulesNum-1:0] RegbusMap = {
    reg_addr_rule_t'{ idx: RegbusErrId,      start_addr:   RegErrBaseAddr, end_addr: (RegErrBaseAddr + RegErrSize)     }, // Regbus error slave
    reg_addr_rule_t'{ idx: RegbusBootromId,  start_addr:  BootromBaseAddr, end_addr: (BootromBaseAddr + BootromSize)   }, // Bootrom
    reg_addr_rule_t'{ idx: RegbusClintId,    start_addr:    ClintBaseAddr, end_addr: (ClintBaseAddr + ClintSize)       }, // CLINT
    reg_addr_rule_t'{ idx: RegbusPlicId,     start_addr:     PlicBaseAddr, end_addr: (PlicBaseAddr + PlicSize)         }, // PLIC
    reg_addr_rule_t'{ idx: RegbusPCRsId,     start_addr:     PCRsBaseAddr, end_addr: (PCRsBaseAddr + PCRsSize)         }, // Platform Control Registers
    reg_addr_rule_t'{ idx: RegbusConsoleId,  start_addr:  ConsoleBaseAddr, end_addr: (ConsoleBaseAddr + ConsoleSize)   }, // Sim console
    reg_addr_rule_t'{ idx: RegbusRTCTimerId, start_addr: RTCTimerBaseAddr, end_addr: (RTCTimerBaseAddr + RTCTimerSize) }, // RTC timer
    reg_addr_rule_t'{ idx: RegbusClicId,     start_addr:     ClicBaseAddr, end_addr: (ClicBaseAddr + ClicSize)         }  // CLIC
  };

  //////////////////////
  // Helper functions //
  //////////////////////

  function automatic void log(string msg);
    $display("@%t | [TB ] %s", $realtime, msg);
  endfunction

  function automatic void setup(string fstfile);
    $display("===========================================");
    $display("======== CVA6 standalone testbench ========");
    $display("===========================================");
    // Time format
    $timeformat(-9, 0, "ns", 9); // 1: scale (ns=-9), 2: decimals, 3: suffix, 4: print-field width
    `ifdef CVA6TB_WAVES
    if (fstfile != "") begin
      $dumpfile(fstfile);
      $dumpvars;
    end
    `endif
  endfunction

  function automatic void cleanup();
    $display("===========================================");
    $display("============ End of simulation ============");
    $display("===========================================");
    `ifdef CVA6TB_WAVES
    $dumpflush;
    `endif
    $finish;
  endfunction

  function automatic void pass();
    log("**SIMULATION PASSED**");
    cleanup();
  endfunction

  function automatic void fail();
    log("**SIMULATION FAILED**");
    cleanup();
  endfunction

endpackage
