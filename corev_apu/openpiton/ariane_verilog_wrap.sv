// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Michael Schaffner <schaffner@iis.ee.ethz.ch>, ETH Zurich
// Date: 19.03.2017
// Description: Ariane Top-level wrapper to break out SV structs to logic vectors.

module ariane_verilog_wrap
    import ariane_pkg::*;
    import config_pkg::*;
    import l15_pkg::*;
#(
  parameter int unsigned               RASDepth              = 2,
  parameter int unsigned               BTBEntries            = 32,
  parameter int unsigned               BHTEntries            = 128,
  parameter int unsigned               NrCommitPorts         = 2,
  parameter int unsigned               NrLoadBufEntries      = 2,
  parameter int unsigned               NrRgprPorts           = 0,
  parameter int unsigned               NrWbPorts             = 0,
  parameter int unsigned               MaxOutstandingStores  = 7,
  parameter logic [63:0]               HaltAddress           = 64'h800,
  parameter logic [63:0]               ExceptionAddress      = 64'h808,
  parameter bit                        EnableAccelerator     = 0,
  parameter bit                        SupervisorModeEn      = 1,
  parameter bit                        TvalEn                = 1,
  parameter bit                        DebugEn               = 1,
  parameter bit                        NonIdemPotenceEn      = 0,
  parameter int unsigned               XLEN                  = 64,
  parameter int unsigned               VLEN                  = 64,
  parameter bit                        FpgaEn                = 0,
  parameter bit                        FpgaAlteraEn          = 0,
  // RISCV extensions
  parameter bit                        FpuEn                 = 1,
  parameter bit                        F16En                 = 0,
  parameter bit                        F16AltEn              = 0,
  parameter bit                        F8En                  = 0,
  parameter bit                        FVecEn                = 0,
  parameter bit                        CvxifEn               = 0,
  parameter bit                        CExtEn                = 1,
  parameter bit                        ZcbExtEn              = 0,
  parameter bit                        AExtEn                = 1,
  parameter bit                        BExtEn                = 0,
  parameter bit                        VExtEn                = 0,
  parameter bit                        ZcmpExtEn             = 0,
  parameter bit                        FExtEn                = 0,
  parameter bit                        DExtEn                = 0,
  parameter bit                        RVUEn                 = 1,
  parameter bit                        RVZicntrEn            = 0,
  parameter bit                        RVZiCondEn            = 0,
  parameter bit                        RVZihpmEn             = 0,
  parameter bit                        HExtEn                = 0,
  parameter bit                        RVFEn                 = 1,
  parameter bit                        RVDEn                 = 1,
  // extended
  parameter bit                        FpPresent             = 0,
  parameter int unsigned               FLen                  = 0,
  parameter bit                        NSXEn                 = 0, // non standard extensions present
  parameter bit                        RVFVecEn              = 0,
  parameter bit                        XF16VecEn             = 0,
  parameter bit                        XF16ALTVecEn          = 0,
  parameter bit                        XF8VecEn              = 0,
  parameter bit                        PerfCounterEn         = 0,
  // debug module base address
  parameter logic [63:0]               DmBaseAddress         = 64'h0,
  // swap endianness in l15 adapter
  parameter bit                        SwapEndianess         = 1,
  // AXI Configuration
  parameter int unsigned               AxiIdWidth            = 4,
  parameter int unsigned               AxiUserWidth          = 64,
  parameter int unsigned               AxiBurstWriteEn       = 0,
  // PMA configuration
  // idempotent region
  parameter int unsigned               NrNonIdempotentRules  =  1,
  parameter logic [NrMaxRules*64-1:0]  NonIdempotentAddrBase = 64'h00C0000000,
  parameter logic [NrMaxRules*64-1:0]  NonIdempotentLength   = 64'hFFFFFFFFFF,
  // executable regions
  parameter int unsigned               NrExecuteRegionRules  =  0,
  parameter logic [NrMaxRules*64-1:0]  ExecuteRegionAddrBase = '0,
  parameter logic [NrMaxRules*64-1:0]  ExecuteRegionLength   = '0,
  // cacheable regions
  parameter int unsigned               NrCachedRegionRules   =  0,
  parameter logic [NrMaxRules*64-1:0]  CachedRegionAddrBase  = '0,
  parameter logic [NrMaxRules*64-1:0]  CachedRegionLength    = '0,
  // PMP
  parameter int unsigned               NrPMPEntries          =  8,
  // HPDC Write coalescing
  parameter bit                        WriteCoalescingEn     =  0,
  parameter int unsigned               WriteCoalescingTh     =  0,
  parameter bit                        UseHPDcache           =  0 // 1: HPDC, 0: WTcache
) (
  input                       clk_i,
  input                       reset_l,      // this is an openpiton-specific name, do not change (hier. paths in TB use this)
  output                      spc_grst_l,   // this is an openpiton-specific name, do not change (hier. paths in TB use this)
  // Core ID, Cluster ID and boot address are considered more or less static
  input  [VLEN-1:0]               boot_addr_i,  // reset boot address
  input  [XLEN-1:0]               hart_id_i,    // hart id in a multicore environment (reflected in a CSR)
  // Interrupt inputs
  input  [1:0]                irq_i,        // level sensitive IR lines, mip & sip (async)
  input                       ipi_i,        // inter-processor interrupts (async)
  // Timer facilities
  input                       time_irq_i,   // timer interrupt in (async)
  input                       debug_req_i,  // debug request (async)

  // L15 (memory side)
  output [$size(l15_pkg::l15_req_t)-1:0]  l15_req_o,
  input  [$size(l15_pkg::l15_rtrn_t)-1:0] l15_rtrn_i
 );

  localparam cva6_user_cfg_t cva6_user_cfg = '{
    XLEN:                   XLEN,
    VLEN:                   VLEN,
    RVA:                    AExtEn,
    RVB:                    BExtEn,
    ZKN:                    1'b0,  // Scalar Cryptography extension disabled
    RVV:                    VExtEn,
    RVC:                    CExtEn,
    RVH:                    HExtEn,
    RVZCB:                  ZcbExtEn,
    RVZCMP:                 ZcmpExtEn,
    RVZCMT:                 1'b0,  // Zcmt extension disabled
    RVZiCond:               RVZiCondEn,
    RVZicntr:               RVZicntrEn,
    RVZihpm:                RVZihpmEn,
    RVZiCbom:               1'b0, // OpenPiton doesn't support CMOs at this time
    RVF:                    RVFEn,
    RVD:                    RVDEn,
    XF16:                   F16En,
    XF16ALT:                F16AltEn,
    XF8:                    F8En,
    XFVec:                  FVecEn,
    PerfCounterEn:          PerfCounterEn,
    MmuPresent:             1'b1,
    RVS:                    SupervisorModeEn,
    RVU:                    RVUEn,
    SoftwareInterruptEn:    1'b1,  // Software interrupts enabled
    DebugEn:                DebugEn,
    DmBaseAddress:          DmBaseAddress,
    HaltAddress:            HaltAddress,
    ExceptionAddress:       ExceptionAddress,
    TvalEn:                 TvalEn,
    DirectVecOnly:          1'b0,
    NrPMPEntries:           NrPMPEntries,
    PMPCfgRstVal:           {16{64'h0}},
    PMPAddrRstVal:          {16{64'h0}},
    PMPEntryReadOnly:       16'd0,
    PMPNapotEn:             1'b1,  // PMP NAPOT mode enabled
    NrNonIdempotentRules:   NrNonIdempotentRules,
    NonIdempotentAddrBase:  NonIdempotentAddrBase,
    NonIdempotentLength:    NonIdempotentLength,
    NrExecuteRegionRules:   NrExecuteRegionRules,
    ExecuteRegionAddrBase:  ExecuteRegionAddrBase,
    ExecuteRegionLength:    ExecuteRegionLength,
    NrCachedRegionRules:    NrCachedRegionRules,
    CachedRegionAddrBase:   CachedRegionAddrBase,
    CachedRegionLength:     CachedRegionLength,
    CvxifEn:                CvxifEn,
    CoproType:              config_pkg::COPRO_NONE,  // No coprocessor
    NOCType:                SwapEndianess ? NOC_TYPE_L15_BIG_ENDIAN : NOC_TYPE_L15_LITTLE_ENDIAN,
    AxiAddrWidth:           40,
    AxiDataWidth:           128, // Used to calculate the mem data width of hpdc
    AxiIdWidth:             6,
    AxiUserWidth:           AxiUserWidth,
    AxiBurstWriteEn:        AxiBurstWriteEn,
    MemTidWidth:            6,
    IcacheByteSize:         16384,
    IcacheSetAssoc:         4,
    IcacheLineWidth:        256,
    DCacheType:             UseHPDcache ? config_pkg::HPDCACHE_WT : config_pkg::WT,
    DcacheIdWidth:          1,
    DcacheByteSize:         8192,
    DcacheSetAssoc:         4,
    DcacheLineWidth:        128,
    DcacheFlushOnFence:     1'b0,  // Don't flush D$ on fence
    DcacheFlushOnFenceI:    1'b0,
    DcacheInvalidateOnFlush: 1'b0, // Don't invalidate on flush
    DataUserEn:             1'b0,
    WtDcacheWbufDepth:      8,
    FetchUserEn:            0,
    FetchUserWidth:         64,
    FpgaEn:                 FpgaEn,
    FpgaAlteraEn:           FpgaAlteraEn,
    TechnoCut:              1'b0,
    SuperscalarEn:          1'b0,
    ALUBypass:              1'b0,  // ALU bypass disabled
    NrCommitPorts:          NrCommitPorts,
    NrLoadPipeRegs:         2,
    NrStorePipeRegs:        0,
    NrScoreboardEntries:    8,
    NrLoadBufEntries:       NrLoadBufEntries,
    MaxOutstandingStores:   MaxOutstandingStores,
    RASDepth:               RASDepth,
    BTBEntries:             BTBEntries,
    BPType:                 config_pkg::BHT,  // Bimodal predictor
    BHTEntries:             BHTEntries,
    BHTHist:                2,  // 2-bit history for BHT
    InstrTlbEntries:        16,
    DataTlbEntries:         16,
    UseSharedTlb:           0,
    SvnapotEn:              0,
    SharedTlbDepth:         64,
    SDTRIG:                 0,
    Mcontrol6:              0,
    Icount:                 0,
    Etrigger:               0,
    Itrigger:               0
  };

  localparam cva6_cfg_t cva6_cfg = build_config_pkg::build_config(cva6_user_cfg);

// assign bitvector to packed struct and vice versa
  // L15 (memory side)
  l15_req_t  l15_req;
  l15_rtrn_t l15_rtrn;

  assign l15_req_o = l15_req;
  assign l15_rtrn  = l15_rtrn_i;


  /////////////////////////////
  // Core wakeup mechanism
  /////////////////////////////

  // // this is a workaround since interrupts are not fully supported yet.
  // // the logic below catches the initial wake up interrupt that enables the cores.
  // logic wake_up_d, wake_up_q;
  // logic rst_n;

  // assign wake_up_d = wake_up_q || ((l15_rtrn.l15_returntype == wt_cache_pkg::L15_INT_RET) && l15_rtrn.l15_val);

  // always_ff @(posedge clk_i or negedge reset_l) begin : p_regs
  //   if(~reset_l) begin
  //     wake_up_q <= 0;
  //   end else begin
  //     wake_up_q <= wake_up_d;
  //   end
  // end

  // // reset gate this
  // assign rst_n = wake_up_q & reset_l;

  // this is a workaround,
  // we basically wait for 32k cycles such that the SRAMs in openpiton can initialize
  // 128KB..8K cycles
  // 256KB..16K cycles
  // etc, so this should be enough for 512k per tile

  logic [15:0] wake_up_cnt_d, wake_up_cnt_q;
  logic rst_n;

  assign wake_up_cnt_d = (wake_up_cnt_q[$high(wake_up_cnt_q)]) ? wake_up_cnt_q : wake_up_cnt_q + 1;

  always_ff @(posedge clk_i or negedge reset_l) begin : p_regs
    if(~reset_l) begin
      wake_up_cnt_q <= 0;
    end else begin
      wake_up_cnt_q <= wake_up_cnt_d;
    end
  end

  // reset gate this
  assign rst_n = wake_up_cnt_q[$high(wake_up_cnt_q)] & reset_l;


  /////////////////////////////
  // synchronizers
  /////////////////////////////

  logic [1:0] irq;
  logic ipi, time_irq, debug_req;

  // reset synchronization
  synchronizer i_sync (
    .clk         ( clk_i      ),
    .presyncdata ( rst_n      ),
    .syncdata    ( spc_grst_l )
  );

  // interrupts
  for (genvar k=0; k<$size(irq_i); k++) begin
    synchronizer i_irq_sync (
      .clk         ( clk_i      ),
      .presyncdata ( irq_i[k]   ),
      .syncdata    ( irq[k]     )
    );
  end

  synchronizer i_ipi_sync (
    .clk         ( clk_i      ),
    .presyncdata ( ipi_i      ),
    .syncdata    ( ipi        )
  );

  synchronizer i_timer_sync (
    .clk         ( clk_i      ),
    .presyncdata ( time_irq_i ),
    .syncdata    ( time_irq   )
  );

  synchronizer i_debug_sync (
    .clk         ( clk_i       ),
    .presyncdata ( debug_req_i ),
    .syncdata    ( debug_req   )
  );

  /////////////////////////////
  // ariane instance
  /////////////////////////////

  ariane #(
    .CVA6Cfg    ( cva6_cfg ),
    .noc_req_t  ( l15_req_t  ),
    .noc_resp_t ( l15_rtrn_t )
  ) ariane (
    .clk_i       ( clk_i      ),
    .rst_ni      ( spc_grst_l ),
    .boot_addr_i              ,// constant
    .hart_id_i                ,// constant
    .irq_i       ( irq        ),
    .ipi_i       ( ipi        ),
    .time_irq_i  ( time_irq   ),
    .debug_req_i ( debug_req  ),
    .noc_req_o   ( l15_req    ),
    .noc_resp_i  ( l15_rtrn   )
  );

endmodule // ariane_verilog_wrap
