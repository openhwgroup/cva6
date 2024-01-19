// Copyright 2024 Thales DIS France SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Yannick Casamatta - Thales
// Date: 09/01/2024


module cva6_rvfi
  import ariane_pkg::*;
#(
    parameter config_pkg::cva6_cfg_t CVA6Cfg = config_pkg::cva6_cfg_empty,
    parameter type rvfi_instr_t = logic,
    parameter type rvfi_probes_t = logic
) (

    input logic clk_i,
    input logic rst_ni,

    input rvfi_probes_t rvfi_probes_i,
    output rvfi_instr_t [CVA6Cfg.NrCommitPorts-1:0] rvfi_o

);

  // ------------------------------------------
  // CVA6 configuration
  // ------------------------------------------
  // Extended config
  localparam bit RVF = (riscv::IS_XLEN64 | riscv::IS_XLEN32) & CVA6Cfg.FpuEn;
  localparam bit RVD = (riscv::IS_XLEN64 ? 1 : 0) & CVA6Cfg.FpuEn;
  localparam bit FpPresent = RVF | RVD | CVA6Cfg.XF16 | CVA6Cfg.XF16ALT | CVA6Cfg.XF8;
  localparam bit NSX = CVA6Cfg.XF16 | CVA6Cfg.XF16ALT | CVA6Cfg.XF8 | CVA6Cfg.XFVec;  // Are non-standard extensions present?
  localparam int unsigned FLen = RVD ? 64 :  // D ext.
  RVF ? 32 :  // F ext.
  CVA6Cfg.XF16 ? 16 :  // Xf16 ext.
  CVA6Cfg.XF16ALT ? 16 :  // Xf16alt ext.
  CVA6Cfg.XF8 ? 8 :  // Xf8 ext.
  1;  // Unused in case of no FP

  // Transprecision floating-point extensions configuration
  localparam bit RVFVec     = RVF             & CVA6Cfg.XFVec & FLen>32; // FP32 vectors available if vectors and larger fmt enabled
  localparam bit XF16Vec    = CVA6Cfg.XF16    & CVA6Cfg.XFVec & FLen>16; // FP16 vectors available if vectors and larger fmt enabled
  localparam bit XF16ALTVec = CVA6Cfg.XF16ALT & CVA6Cfg.XFVec & FLen>16; // FP16ALT vectors available if vectors and larger fmt enabled
  localparam bit XF8Vec     = CVA6Cfg.XF8     & CVA6Cfg.XFVec & FLen>8;  // FP8 vectors available if vectors and larger fmt enabled

  localparam bit EnableAccelerator = CVA6Cfg.RVV;  // Currently only used by V extension (Ara)
  localparam int unsigned NrWbPorts = (CVA6Cfg.CvxifEn || EnableAccelerator) ? 5 : 4;

  localparam NrRgprPorts = 2;

  localparam bit NonIdemPotenceEn = CVA6Cfg.NrNonIdempotentRules && CVA6Cfg.NonIdempotentLength;  // Currently only used by V extension (Ara)

  localparam config_pkg::cva6_cfg_t CVA6ExtendCfg = {
    CVA6Cfg.NrCommitPorts,
    CVA6Cfg.AxiAddrWidth,
    CVA6Cfg.AxiDataWidth,
    CVA6Cfg.AxiIdWidth,
    CVA6Cfg.AxiUserWidth,
    CVA6Cfg.NrLoadBufEntries,
    CVA6Cfg.FpuEn,
    CVA6Cfg.XF16,
    CVA6Cfg.XF16ALT,
    CVA6Cfg.XF8,
    CVA6Cfg.RVA,
    CVA6Cfg.RVB,
    CVA6Cfg.RVV,
    CVA6Cfg.RVC,
    CVA6Cfg.RVZCB,
    CVA6Cfg.XFVec,
    CVA6Cfg.CvxifEn,
    CVA6Cfg.ZiCondExtEn,
    // Extended
    bit'(RVF),
    bit'(RVD),
    bit'(FpPresent),
    bit'(NSX),
    unsigned'(FLen),
    bit'(RVFVec),
    bit'(XF16Vec),
    bit'(XF16ALTVec),
    bit'(XF8Vec),
    unsigned'(NrRgprPorts),
    unsigned'(NrWbPorts),
    bit'(EnableAccelerator),
    CVA6Cfg.RVS,
    CVA6Cfg.RVU,
    CVA6Cfg.HaltAddress,
    CVA6Cfg.ExceptionAddress,
    CVA6Cfg.RASDepth,
    CVA6Cfg.BTBEntries,
    CVA6Cfg.BHTEntries,
    CVA6Cfg.DmBaseAddress,
    CVA6Cfg.NrPMPEntries,
    CVA6Cfg.PMPCfgRstVal,
    CVA6Cfg.PMPAddrRstVal,
    CVA6Cfg.PMPEntryReadOnly,
    CVA6Cfg.NOCType,
    CVA6Cfg.NrNonIdempotentRules,
    CVA6Cfg.NonIdempotentAddrBase,
    CVA6Cfg.NonIdempotentLength,
    CVA6Cfg.NrExecuteRegionRules,
    CVA6Cfg.ExecuteRegionAddrBase,
    CVA6Cfg.ExecuteRegionLength,
    CVA6Cfg.NrCachedRegionRules,
    CVA6Cfg.CachedRegionAddrBase,
    CVA6Cfg.CachedRegionLength,
    CVA6Cfg.MaxOutstandingStores,
    CVA6Cfg.DebugEn,
    NonIdemPotenceEn,
    CVA6Cfg.AxiBurstWriteEn
  };

  logic                                                                   flush;
  logic                                                                   issue_instr_ack;
  logic                                                                   fetch_entry_valid;
  logic              [                           31:0]                    instruction;
  logic                                                                   is_compressed;

  logic              [              TRANS_ID_BITS-1:0]                    issue_pointer;
  logic              [CVA6ExtendCfg.NrCommitPorts-1:0][TRANS_ID_BITS-1:0] commit_pointer;

  logic                                                                   flush_unissued_instr;
  logic                                                                   decoded_instr_valid;
  logic                                                                   decoded_instr_ack;

  riscv::xlen_t                                                           rs1_forwarding;
  riscv::xlen_t                                                           rs2_forwarding;

  scoreboard_entry_t [CVA6ExtendCfg.NrCommitPorts-1:0]                    commit_instr;
  exception_t                                                             ex_commit;
  riscv::priv_lvl_t                                                       priv_lvl;

  lsu_ctrl_t                                                              lsu_ctrl;
  logic              [    CVA6ExtendCfg.NrWbPorts-1:0][  riscv::XLEN-1:0] wbdata;
  logic              [CVA6ExtendCfg.NrCommitPorts-1:0]                    commit_ack;
  logic              [                riscv::PLEN-1:0]                    mem_paddr;
  logic                                                                   debug_mode;
  logic              [CVA6ExtendCfg.NrCommitPorts-1:0][  riscv::XLEN-1:0] wdata;

  logic              [                riscv::VLEN-1:0]                    lsu_addr;
  logic              [            (riscv::XLEN/8)-1:0]                    lsu_rmask;
  logic              [            (riscv::XLEN/8)-1:0]                    lsu_wmask;
  logic              [              TRANS_ID_BITS-1:0]                    lsu_addr_trans_id;

  assign flush = rvfi_probes_i.flush;
  assign issue_instr_ack = rvfi_probes_i.issue_instr_ack;
  assign fetch_entry_valid = rvfi_probes_i.fetch_entry_valid;
  assign instruction = rvfi_probes_i.instruction;
  assign is_compressed = rvfi_probes_i.is_compressed;

  assign issue_pointer = rvfi_probes_i.issue_pointer;
  assign commit_pointer = rvfi_probes_i.commit_pointer;

  assign flush_unissued_instr = rvfi_probes_i.flush_unissued_instr;
  assign decoded_instr_valid = rvfi_probes_i.decoded_instr_valid;
  assign decoded_instr_ack = rvfi_probes_i.decoded_instr_ack;

  assign rs1_forwarding = rvfi_probes_i.rs1_forwarding;
  assign rs2_forwarding = rvfi_probes_i.rs2_forwarding;

  assign commit_instr = rvfi_probes_i.commit_instr;
  assign ex_commit = rvfi_probes_i.ex_commit;
  assign priv_lvl = rvfi_probes_i.priv_lvl;

  assign lsu_ctrl = rvfi_probes_i.lsu_ctrl;
  assign wbdata = rvfi_probes_i.wbdata;
  assign commit_ack = rvfi_probes_i.commit_ack;
  assign mem_paddr = rvfi_probes_i.mem_paddr;
  assign debug_mode = rvfi_probes_i.debug_mode;
  assign wdata = rvfi_probes_i.wdata;

  assign lsu_addr = lsu_ctrl.vaddr;
  assign lsu_rmask = lsu_ctrl.fu == LOAD ? lsu_ctrl.be : '0;
  assign lsu_wmask = lsu_ctrl.fu == STORE ? lsu_ctrl.be : '0;
  assign lsu_addr_trans_id = lsu_ctrl.trans_id;


  //ID STAGE

  typedef struct packed {
    logic        valid;
    logic [31:0] instr;
  } issue_struct_t;
  issue_struct_t issue_n, issue_q;

  always_comb begin
    issue_n = issue_q;

    if (issue_instr_ack) issue_n.valid = 1'b0;

    if ((!issue_q.valid || issue_instr_ack) && fetch_entry_valid) begin
      issue_n.valid = 1'b1;
      issue_n.instr = (is_compressed) ? {{16{1'b0}}, instruction[15:0]} : instruction;
    end

    if (flush) issue_n.valid = 1'b0;
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) begin
      issue_q <= '0;
    end else begin
      issue_q <= issue_n;
    end
  end

  //ISSUE STAGE

  // this is the FIFO struct of the issue queue
  typedef struct packed {
    riscv::xlen_t rs1_rdata;
    riscv::xlen_t rs2_rdata;
    logic [riscv::VLEN-1:0] lsu_addr;
    logic [(riscv::XLEN/8)-1:0] lsu_rmask;
    logic [(riscv::XLEN/8)-1:0] lsu_wmask;
    riscv::xlen_t lsu_wdata;
    logic [31:0] instr;
  } sb_mem_t;
  sb_mem_t [NR_SB_ENTRIES-1:0] mem_q, mem_n;

  always_comb begin : issue_fifo
    mem_n = mem_q;

    if (decoded_instr_valid && decoded_instr_ack && !flush_unissued_instr) begin
      mem_n[issue_pointer] = '{
          rs1_rdata: rs1_forwarding,
          rs2_rdata: rs2_forwarding,
          lsu_addr: '0,
          lsu_rmask: '0,
          lsu_wmask: '0,
          lsu_wdata: '0,
          instr: issue_q.instr
      };
    end

    if (lsu_rmask != 0) begin
      mem_n[lsu_addr_trans_id].lsu_addr  = lsu_addr;
      mem_n[lsu_addr_trans_id].lsu_rmask = lsu_rmask;
    end else if (lsu_wmask != 0) begin
      mem_n[lsu_addr_trans_id].lsu_addr  = lsu_addr;
      mem_n[lsu_addr_trans_id].lsu_wmask = lsu_wmask;
      mem_n[lsu_addr_trans_id].lsu_wdata = wbdata[1];
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : regs
    if (!rst_ni) begin
      mem_q <= '{default: sb_mem_t'(0)};
    end else begin
      mem_q <= mem_n;
    end
  end

  //----------------------------------------------------------------------------------------------------------
  // PACK
  //----------------------------------------------------------------------------------------------------------

  always_comb begin
    for (int i = 0; i < CVA6ExtendCfg.NrCommitPorts; i++) begin
      logic exception;
      exception = commit_instr[i].valid && ex_commit.valid;
      rvfi_o[i].valid    = (commit_ack[i] && !ex_commit.valid) ||
        (exception && (ex_commit.cause == riscv::ENV_CALL_MMODE ||
                  ex_commit.cause == riscv::ENV_CALL_SMODE ||
                  ex_commit.cause == riscv::ENV_CALL_UMODE));
      rvfi_o[i].insn = mem_q[commit_pointer[i]].instr;
      // when trap, the instruction is not executed
      rvfi_o[i].trap = exception;
      rvfi_o[i].cause = ex_commit.cause;
      rvfi_o[i].mode = (CVA6ExtendCfg.DebugEn && debug_mode) ? 2'b10 : priv_lvl;
      rvfi_o[i].ixl = riscv::XLEN == 64 ? 2 : 1;
      rvfi_o[i].rs1_addr = commit_instr[i].rs1[4:0];
      rvfi_o[i].rs2_addr = commit_instr[i].rs2[4:0];
      rvfi_o[i].rd_addr = commit_instr[i].rd[4:0];
      rvfi_o[i].rd_wdata = (CVA6ExtendCfg.FpPresent && is_rd_fpr(commit_instr[i].op)) ?
          commit_instr[i].result : wdata[i];
      rvfi_o[i].pc_rdata = commit_instr[i].pc;
      rvfi_o[i].mem_addr = mem_q[commit_pointer[i]].lsu_addr;
      // So far, only write paddr is reported. TODO: read paddr
      rvfi_o[i].mem_paddr = mem_paddr;
      rvfi_o[i].mem_wmask = mem_q[commit_pointer[i]].lsu_wmask;
      rvfi_o[i].mem_wdata = mem_q[commit_pointer[i]].lsu_wdata;
      rvfi_o[i].mem_rmask = mem_q[commit_pointer[i]].lsu_rmask;
      rvfi_o[i].mem_rdata = commit_instr[i].result;
      rvfi_o[i].rs1_rdata = mem_q[commit_pointer[i]].rs1_rdata;
      rvfi_o[i].rs2_rdata = mem_q[commit_pointer[i]].rs2_rdata;
    end
  end


endmodule
