// Copyright 2026 Thales France
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Valentin Thomazic (valentin.thomazic@thalesgroup.com)

module dcls_delay_ff #(
    parameter type data_t = logic,
    parameter int unsigned DCLS_DELAY = 1
) (
    input  logic  clk_i,
    input  logic  rst_ni,
    input  data_t data_i,
    output data_t data_o
);
  data_t [DCLS_DELAY-1 : 0] data_n;

  assign data_o = data_n[DCLS_DELAY-1];

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) begin
      data_n <= '{default: 0};
    end else begin
      data_n[0] <= data_i;
      for (int i = 1; i < DCLS_DELAY; i++) begin
        data_n[i] <= data_n[i-1];
      end
    end
  end
endmodule
