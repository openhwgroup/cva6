// Copyright (c) 2025 Thales DIS design services SAS
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
// Author: Maxime Colson - Thales
// Date: 20/03/2025

//Module used to determines the iaddr, ilastsize, iretire in single retirement for Encoder Module


module single_retirement #(
    parameter config_pkg::cva6_cfg_t CVA6Cfg = config_pkg::cva6_cfg_empty,
    parameter type uop_entry_t = logic,
    parameter type itt_out_t = logic,
    parameter CAUSE_LEN = 5,  //Size is ecause_width_p in the E-Trace SPEC
    parameter ITYPE_LEN = 3,  //Size is itype_width_p in the E-Trace SPEC (3 or 4)
    parameter IRETIRE_LEN = 32  //Size is iretire_width_p in the E-Trace SPEC
) (
    input  uop_entry_t                    uop_entry_i,
    input  logic       [   CAUSE_LEN-1:0] cause_i,
    input  logic       [CVA6Cfg.XLEN-1:0] tval_i,
    output itt_out_t                      itt_out_o
);


  logic exception;
  logic interrupt;
  assign exception = (uop_entry_i.itype == iti_pkg::EXC) ? 1'b1 : 1'b0;
  assign interrupt = (uop_entry_i.itype == iti_pkg::INT) ? 1'b1 : 1'b0;

  always_comb begin
    itt_out_o = '0;

    if (uop_entry_i.valid) begin

      itt_out_o.valid = 1'b1;
      itt_out_o.iretire = 1;
      itt_out_o.itype = uop_entry_i.itype;
      itt_out_o.ilastsize = ~uop_entry_i.compressed;
      itt_out_o.iaddr = uop_entry_i.pc;
      itt_out_o.priv = uop_entry_i.priv;
      itt_out_o.cycles = uop_entry_i.cycles;
      itt_out_o.cause = '0;
      itt_out_o.tval = '0;

      if (interrupt) begin
        itt_out_o.cause = cause_i;
        itt_out_o.tval  = '0;
      end

      if (exception) begin
        itt_out_o.cause = cause_i;
        itt_out_o.tval  = tval_i;
      end

    end
  end
endmodule
