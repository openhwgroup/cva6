// Copyright 2024 Thales Silicon Security
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Côme ALLART - Thales

module round_interval #(
    parameter int unsigned S = 1,
    parameter int unsigned L = 1 << S
) (
    // Start index
    // Included in the interval
    input logic [S-1:0] start_i,
    // Stop index
    // Not included in the interval
    input logic [S-1:0] stop_i,

    // The interval from start to stop, rounding
    // Considered full when start_i == stop_i
    output logic [L-1:0] active_o
);

  // Bit high at index start/stop
  logic [L-1:0] a;
  logic [L-1:0] b;

  for (genvar i = 0; i < L; i++) begin
    assign a[i] = start_i == i;
    assign b[i] = stop_i == i;
  end

  // Propagation to the higher indexes: >=
  logic [L-1:0] ge_a;
  logic [L-1:0] ge_b;

  assign ge_b[0] = b[0];
  assign ge_a[0] = a[0];
  for (genvar i = 1; i < L; i++) begin
    assign ge_b[i] = ge_b[i-1] || b[i];
    assign ge_a[i] = ge_a[i-1] || a[i];
  end

  // < is the negation of >=
  logic [L-1:0] lt_b;
  assign lt_b = ~ge_b;

  // Build the interval
  assign active_o = (start_i <= stop_i) ? lt_b & ge_a : lt_b | ge_a;

endmodule
