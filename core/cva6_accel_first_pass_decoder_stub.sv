// Copyright 2023 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

// Author: Nils Wistoff <nwistoff@iis.ee.ethz.ch>

// Module stub for the cva6_accel_first_pass_decoder. Replace this with your accelerator's
// first pass decoder.

module cva6_accel_first_pass_decoder
  import ariane_pkg::*;
#(
    parameter config_pkg::cva6_cfg_t CVA6Cfg = '0,
    parameter type scoreboard_entry_t = logic
) (
    input  logic              [31:0] instruction_i,           // instruction from IF
    input  riscv::xs_t               fs_i,                    // floating point extension status
    input  riscv::xs_t               vs_i,                    // vector extension status
    output logic                     is_accel_o,              // is an accelerator instruction
    output scoreboard_entry_t        instruction_o,           // predecoded instruction
    output logic                     illegal_instr_o,         // is an illegal instruction
    output logic                     is_control_flow_instr_o  // is a control flow instruction
);

  assign is_accel_o              = 1'b0;
  assign instruction_o           = '0;
  assign illegal_instr_o         = 1'b0;
  assign is_control_flow_instr_o = 1'b0;

  $error("cva6_accel_first_pass_decoder: instantiated non-functional module stub.\
          Please replace this with your accelerator's first pass decoder \
          (or unset ENABLE_ACCELERATOR).");

endmodule : cva6_accel_first_pass_decoder
