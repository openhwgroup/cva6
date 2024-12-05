// Copyright (c), 2024 Darshak Sheladiya, SYSGO GmbH
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
 


module encoder_16_4 (
    input  logic [15:0] in,    // 16-bit input
    output logic [ 3:0] out,   // 4-bit output
    output logic        valid  // Indicates if there is any active input
);

  always_comb begin
    // Initialize output and valid signal
    out   = 4'b0000;
    valid = 1'b0;

    // Priority encoding (highest priority at the highest bit)
    if (in[15]) begin
      out   = 4'b1111;
      valid = 1'b1;
    end else if (in[14]) begin
      out   = 4'b1110;
      valid = 1'b1;
    end else if (in[13]) begin
      out   = 4'b1101;
      valid = 1'b1;
    end else if (in[12]) begin
      out   = 4'b1100;
      valid = 1'b1;
    end else if (in[11]) begin
      out   = 4'b1011;
      valid = 1'b1;
    end else if (in[10]) begin
      out   = 4'b1010;
      valid = 1'b1;
    end else if (in[9]) begin
      out   = 4'b1001;
      valid = 1'b1;
    end else if (in[8]) begin
      out   = 4'b1000;
      valid = 1'b1;
    end else if (in[7]) begin
      out   = 4'b0111;
      valid = 1'b1;
    end else if (in[6]) begin
      out   = 4'b0110;
      valid = 1'b1;
    end else if (in[5]) begin
      out   = 4'b0101;
      valid = 1'b1;
    end else if (in[4]) begin
      out   = 4'b0100;
      valid = 1'b1;
    end else if (in[3]) begin
      out   = 4'b0011;
      valid = 1'b1;
    end else if (in[2]) begin
      out   = 4'b0010;
      valid = 1'b1;
    end else if (in[1]) begin
      out   = 4'b0001;
      valid = 1'b1;
    end else if (in[0]) begin
      out   = 4'b0000;
      valid = 1'b1;
    end else begin
      valid = 1'b0;  // No active input
    end
  end
endmodule
