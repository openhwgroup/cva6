// Copyright 2024 Thales DIS France SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Privilege Level Modifier
// Generates alternating privilege levels for WT_NEW cache testing
// Ignores actual privilege level and creates predictable switching pattern

module priv_lvl_modifier
  import ariane_pkg::*;
#(
  parameter int unsigned SWITCH_PERIOD = 100  // Clock cycles between privilege level switches
) (
  input  logic clk_i,
  input  logic rst_ni,
  
  // Actual privilege level from CVA6 (ignored for testing)
  input  riscv::priv_lvl_t actual_priv_lvl_i,
  
  // Modified privilege level output (alternating M/U mode)
  output riscv::priv_lvl_t modified_priv_lvl_o,
  
  // Debug signals for VCD visibility
  output logic [31:0] cycle_counter_o,
  output logic privilege_switch_event_o,
  output logic in_machine_mode_o,
  output logic in_user_mode_o
);

  // Counter for privilege level switching
  logic [31:0] cycle_counter;
  logic privilege_state; // 0 = User mode, 1 = Machine mode
  
  // Assign debug outputs
  assign cycle_counter_o = cycle_counter;
  assign privilege_switch_event_o = (cycle_counter == SWITCH_PERIOD - 1);
  assign in_machine_mode_o = privilege_state;
  assign in_user_mode_o = ~privilege_state;
  
  // Generate alternating privilege levels
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      cycle_counter <= '0;
      privilege_state <= 1'b1; // Start in Machine mode
    end else begin
      if (cycle_counter == SWITCH_PERIOD - 1) begin
        cycle_counter <= '0;
        privilege_state <= ~privilege_state; // Toggle between M and U mode
      end else begin
        cycle_counter <= cycle_counter + 1;
      end
    end
  end
  
  // Map privilege state to RISC-V privilege levels
  always_comb begin
    case (privilege_state)
      1'b1: modified_priv_lvl_o = riscv::PRIV_LVL_M;  // Machine mode
      1'b0: modified_priv_lvl_o = riscv::PRIV_LVL_U;  // User mode
      default: modified_priv_lvl_o = riscv::PRIV_LVL_M;
    endcase
  end
  
  // Additional debug signals for VCD analysis
  logic [1:0] priv_lvl_encoding;
  assign priv_lvl_encoding = modified_priv_lvl_o;
  
  // Create readable privilege level name for debugging
  logic machine_mode_active;
  logic user_mode_active;
  logic supervisor_mode_active;
  
  assign machine_mode_active = (modified_priv_lvl_o == riscv::PRIV_LVL_M);
  assign user_mode_active = (modified_priv_lvl_o == riscv::PRIV_LVL_U);
  assign supervisor_mode_active = (modified_priv_lvl_o == riscv::PRIV_LVL_S);
  
  // Performance monitoring: track privilege level changes
  logic priv_lvl_changed;
  riscv::priv_lvl_t prev_priv_lvl;
  
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      prev_priv_lvl <= riscv::PRIV_LVL_M;
      priv_lvl_changed <= 1'b0;
    end else begin
      prev_priv_lvl <= modified_priv_lvl_o;
      priv_lvl_changed <= (prev_priv_lvl != modified_priv_lvl_o);
    end
  end

endmodule