// Copyright 2025 Thales DIS France SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Maxime Colson - Thales
// Date: 20/03/2025

// Contributors: 
// Darshak Sheladiya, SYSGO GmbH
// Umberto Laghi, UNIBO

// For reference : See Section 4.2 Intruction Trace Inteface from Efficient Trace for RISC-V v2.0 (may 5 2022)
// iti stand for Instruction Trace Interface, changing because tip (Trace Ingress Port) and "type" are too similar creating confusion 

module cva6_iti #(
    parameter config_pkg::cva6_cfg_t CVA6Cfg = config_pkg::cva6_cfg_empty,
    parameter CAUSE_LEN = 5, //Size is ecause_width_p in the E-Trace SPEC
    parameter ITYPE_LEN = 3, //Size is itype_width_p in the E-Trace SPEC (3 or 4)
    parameter IRETIRE_LEN = 32 //Size is iretire_width_p in the E-Trace SPEC
) (
    input logic clk_i,
    input logic rst_ni,

    input logic [CVA6Cfg.NrCommitPorts-1:0] valid_i, 
    input logic [CVA6Cfg.NrCommitPorts-1:0][CVA6Cfg.XLEN-1:0] pc_i,
    input ariane_pkg::fu_op [CVA6Cfg.NrCommitPorts-1:0] op_i,
    input logic [CVA6Cfg.NrCommitPorts-1:0] is_compressed_i,
    input logic [CVA6Cfg.NrCommitPorts-1:0] branch_valid_i,
    input logic [CVA6Cfg.NrCommitPorts-1:0] is_taken_i,
    input logic ex_valid_i,
    input logic [CVA6Cfg.XLEN-1:0] tval_i,
    input logic [CVA6Cfg.XLEN-1:0] cause_i,
    input riscv::priv_lvl_t priv_lvl_i,
    input logic [63:0] time_i,

    output logic [CVA6Cfg.NrCommitPorts-1:0] valid_o,
    output logic [CVA6Cfg.NrCommitPorts-1:0][IRETIRE_LEN-1:0] iretire_o, // size is overkill
    output logic [CVA6Cfg.NrCommitPorts-1:0] ilastsize_o,
    output iti_pkg::itype_t [CVA6Cfg.NrCommitPorts-1:0][2:0] itype_o, // 3 => we use itype = 6 max / 4 else
    output logic [CAUSE_LEN-1:0] cause_o,
    output logic [CVA6Cfg.XLEN-1:0] tval_o,
    output riscv::priv_lvl_t  priv_o,
    output logic [CVA6Cfg.NrCommitPorts-1:0][CVA6Cfg.XLEN-1:0] iaddr_o,
    output logic [63:0] time_o
);

  // pragma translate_off
  int f;
  initial begin
    f = $fopen("iti.trace","w");
  end
  final $fclose(f);
  // pragma translate_on

  /* Structure used for each instr*/
  localparam type uop_entry_t = struct packed {
    logic                    valid;
    logic [CVA6Cfg.XLEN-1:0] pc;
    iti_pkg::itype_t         itype;
    logic                    compressed;
    riscv::priv_lvl_t        priv;
    logic [63:0]             times;
  };

  /* Structure used to output trace_signals if special instr */
  localparam type itt_out_t = struct packed {
    logic                    valid;
    logic [IRETIRE_LEN-1:0]  iretire;
    iti_pkg::itype_t         itype;
    logic                    ilastsize;
    logic [CVA6Cfg.XLEN-1:0] iaddr;
    riscv::priv_lvl_t        priv;
    logic [CAUSE_LEN-1:0]    cause;     
    logic [CVA6Cfg.XLEN-1:0] tval; 
    logic [63:0]            times;
  };

  logic interrupt;
  iti_pkg::itype_t [CVA6Cfg.NrCommitPorts-1:0] itype;

  logic [IRETIRE_LEN-1:0] counter_d, counter_q;
  logic [CVA6Cfg.XLEN-1:0] addr_d, addr_q;
  logic special_d, special_q;

  uop_entry_t [CVA6Cfg.NrCommitPorts-1:0] uop_entry;
  itt_out_t [CVA6Cfg.NrCommitPorts-1:0] itt_out;

  logic [CVA6Cfg.NrCommitPorts-1:0][IRETIRE_LEN-1:0] counter_itt;
  logic [CVA6Cfg.NrCommitPorts-1:0][CVA6Cfg.XLEN-1:0] addr_itt;
  logic [CVA6Cfg.NrCommitPorts-1:0] special_itt;
  logic [CVA6Cfg.NrCommitPorts-1:0][CAUSE_LEN-1:0] cause_itt ;
  logic [CVA6Cfg.NrCommitPorts-1:0][CVA6Cfg.XLEN-1:0] tval_itt ;

  logic [CVA6Cfg.NrCommitPorts-1:0][IRETIRE_LEN-1:0] counter;
  logic [CVA6Cfg.NrCommitPorts-1:0][CVA6Cfg.XLEN-1:0] addr;
  logic [CVA6Cfg.NrCommitPorts-1:0] special;


  assign interrupt = cause_i[CVA6Cfg.XLEN-1];  // determinated based on the MSB of cause

  for (genvar i = 0; i < CVA6Cfg.NrCommitPorts; i++) begin
    itype_detector #(
        .ITYPE_LEN(ITYPE_LEN)
    ) i_itype_detector (
        .valid_i       (valid_i[i]),
        .exception_i   (ex_valid_i),
        .interrupt_i   (interrupt),
        .op_i          (op_i[i]),
        .branch_taken_i(is_taken_i[i]),
        .itype_o       (itype[i])
    );

    // Adding this to ensure that interuption/exception happen only in commit port 0 of cva6
    assign cause_itt[i] = i==0 ? cause_i[CAUSE_LEN-1:0] : '0;
    assign tval_itt[i] = i==0 ? tval_i : '0;
    // Systolic logic (First itt is connected to D Flip-Flop to continue computation if needed)
    assign counter_itt[i] = i==0 ? counter_q : counter[i-1];
    assign addr_itt[i] = i==0 ? addr_q : addr[i-1];
    assign special_itt[i] = i==0 ? special_q : special[i-1];

    instr_to_trace  #(
      .CVA6Cfg(CVA6Cfg),
      .uop_entry_t(uop_entry_t),
      .itt_out_t(itt_out_t),
      .CAUSE_LEN(CAUSE_LEN),
      .ITYPE_LEN(ITYPE_LEN),
      .IRETIRE_LEN(IRETIRE_LEN)
    ) i_instr_to_trace (
      .uop_entry_i(uop_entry[i]),
      .cause_i(cause_itt[i]),
      .tval_i(tval_itt[i]),
      .counter_i(counter_itt[i]),
      .iaddr_i(addr_itt[i]),
      .was_special_i(special_itt[i]),
      .itt_out_o(itt_out[i]),
      .counter_o(counter[i]),
      .iaddr_o(addr[i]),
      .is_special_o(special[i])
    );
  end


  always_comb begin
    cause_o = '0;
    tval_o = '0;

    for (int i = 0; i < CVA6Cfg.NrCommitPorts; i++) begin
      uop_entry[i].valid = valid_i[i];
      uop_entry[i].pc = pc_i[i];
      uop_entry[i].itype = itype[i];
      uop_entry[i].compressed = is_compressed_i[i];
      uop_entry[i].priv = priv_lvl_i;
      uop_entry[i].times = time_i;

      valid_o[i] = 1'b0;
      iretire_o[i] = '0;
      ilastsize_o[i] = '0;
      itype_o[i] = '0;
      iaddr_o[i] = '0;
      if (itt_out[i].valid) begin
        valid_o[i] = itt_out[i].valid;
        iretire_o[i] = itt_out[i].iretire;
        ilastsize_o[i] = itt_out[i].ilastsize;
        itype_o[i] = itt_out[i].itype;
        iaddr_o[i] = itt_out[i].iaddr;
        priv_o = itt_out[i].priv; // privilege don't change between 2 instr comitted in the same cycle
        time_o = itt_out[i].times; // Same here (same time at same cycle)
      end
    end
    if (itt_out[0].valid) begin // interrupt & exception only in port 0
        cause_o = itt_out[0].cause;
        tval_o = itt_out[0].tval;
    end
  end

  assign counter_d = counter[CVA6Cfg.NrCommitPorts-1];
  assign addr_d = addr[CVA6Cfg.NrCommitPorts-1];
  assign special_d = special[CVA6Cfg.NrCommitPorts-1];

  always_ff @(posedge clk_i, negedge rst_ni) begin
    if (!rst_ni) begin
      counter_q <= '0;
      addr_q <= '0;
      special_q <= 1'b1;
    end else begin
      counter_q <= counter_d;
      addr_q <= addr_d;
      special_q <= special_d;
    end
  //pragma translate_off
    for (int i = 0; i < CVA6Cfg.NrCommitPorts; i++) begin
      if (itt_out[i].valid) begin
        $fwrite(f, "i :%d , val = %d , iret = %d, ilast = 0x%d , itype = %d , cause = 0x%h , tval= 0x%h , priv = 0x%d , iadd= 0x%h, time =%d  \n",
        i, itt_out[i].valid, itt_out[i].iretire , itt_out[i].ilastsize , itt_out[i].itype , itt_out[i].cause, itt_out[i].tval, itt_out[i].priv , itt_out[i].iaddr , time_i); 
      end
    end
  //pragma translate_on
  end 


endmodule