// (C) 2001-2024 Intel Corporation. All rights reserved.
// Your use of Intel Corporation's design tools, logic functions and other 
// software and tools, and its AMPP partner logic functions, and any output 
// files from any of the foregoing (including device programming or simulation 
// files), and any associated documentation or information are expressly subject 
// to the terms and conditions of the Intel Program License Subscription 
// Agreement, Intel FPGA IP License Agreement, or other applicable 
// license agreement, including, without limitation, that your use is for the 
// sole purpose of programming logic devices manufactured by Intel and sold by 
// Intel or its authorized distributors.  Please refer to the applicable 
// agreement for further details.



///////////////////////////////////////////////////////////////////////////////
// This module handles the creation of a conditional register stage.
// This module may be used to implement a synchronizer (with properly selected
// REGISTER value)
///////////////////////////////////////////////////////////////////////////////

// The following ensures that the register stage isn't synthesized into
// RAM-based shift-regs (especially if customer logic implements another follow-on
// pipeline stage). RAM-based shift-regs can degrade timing for C2P/P2C transfers.
(* altera_attribute = "-name AUTO_SHIFT_REGISTER_RECOGNITION OFF" *)

 module altera_emif_arch_fm_regs #(
   parameter REGISTER       = 0,
   parameter WIDTH          = 0
) (
   input  logic              clk,
   input  logic              reset_n,
   input  logic [WIDTH-1:0]  data_in,
   output logic [WIDTH-1:0]  data_out
) /* synthesis dont_merge */;
   timeunit 1ns;
   timeprecision 1ps;

   generate
      genvar stage;

      if (REGISTER == 0) begin : no_reg
         assign data_out = data_in;
      end else begin : regs
         logic [WIDTH-1:0] sr_out [(REGISTER > 0 ? REGISTER-1 : 0):0];

         assign data_out = sr_out[REGISTER-1];

         for (stage = 0; stage < REGISTER; stage = stage + 1)
         begin : stage_gen
            always_ff @(posedge clk or negedge reset_n) begin
               if (~reset_n) begin
                  sr_out[stage] <= '0;
               end else begin
                  sr_out[stage] <= (stage == 0) ? data_in : sr_out[stage-1];
               end
            end
         end
      end
   endgenerate
endmodule
`ifdef QUESTA_INTEL_OEM
`pragma questa_oem_00 "EVeqkz9MvDzapiiVw7+udc++m43wu2P9R6Bkf/lfBn9ZttFzW71hzuu9P3yzPlvUUu1GESHEht8oUjkuxH5nYF5m2Y4yEaZOsor1W+qakklkcNM5gczDB8G/zUljAitcohcjlH9xX4F5r3RrLLQB1HrtXmnxKKrsVs2RsxKt4plRYJGUCxRjs6twKgr6lps1q22taZT7+7dZh7dYE0uKJfWB1PYeKR+rbOxvrAyMNm3tozkeL1uA0g6U2EUSXAyXVQSjpOKAZHctS0q08TSgBla5+tUOYiiDPSAb9bcqW8CStRlmK7HGvMwv9069DY1wUGZ0y07cixAGitu/K30eRibQpiV8iWJOIl7HtulD0SZbbsYF4CeOunjnp9tXrYEVMUG47w3LW0kccnee89uKQJPJn9ADtaqFPPGB7TwznwzJwUcoFZeLyAO94/WpewMNi2B30PWwBloh/zN9faAvH65NZU6lHEiMc+sGO2ngnIJvaoldVHvgyUDysucNk/o22crj3iWw6cRxRVauERE2To393Ivq2mpvI26hroo/pTqrE2AzpOI/4rVRmGQpoVEjmhraaJ1HuacA1lyOKf82oAhBKgVYwiX7MyfRYWiQn2sCtWSuZtgfSXXXDl5AVctMxRH0sA8UOjT3joWiY8F2YwG7xVC/BEjkNEeofaXqSBKcf0Fod6iNzCrVuYpG8J737B1PHgjVOR6Du6Pwl63RCgYc6QaJHH7R6DSd5IBJwPMpDZi9csIWAXHAxr6DIqDQFn00SEhKPqU3BWOZWjkztjQx5ik+m6hJGI7HUyMI5htPfFVfzwT6ZqEOn9FEU+i7gBSu4PYelN2HhfAPsn43lfngh6JnTjWrOXPqkckUU0uYQ09MRNQEq6b7DJHKuZdjCss0pc8acC4AWHdw46U2MXH38Xz2AVejtf8hRQSL32G4OsTq8uqVp+MDESDawj8M5b5tz+S7vTjdnXO/9TF3BajMmRKqcFi5uFJUy1ijWQUF2aVW9RM+mEbv4mLJXmdv"
`endif