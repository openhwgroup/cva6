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



////////////////////////////////////////////////////////////////////////////////////////////////////////////
//  Expose extra core clocks from IOPLL
//
////////////////////////////////////////////////////////////////////////////////////////////////////////////
module altera_emif_arch_fm_pll_extra_clks #(
   parameter PLL_NUM_OF_EXTRA_CLKS = 0,
   parameter DIAG_SIM_REGTEST_MODE = 0
) (
   input  logic                                               pll_locked,            
   input  logic [8:0]                                         pll_c_counters,        
   output logic                                               pll_extra_clk_0,       
   output logic                                               pll_extra_clk_1,
   output logic                                               pll_extra_clk_2,
   output logic                                               pll_extra_clk_3,
   output logic                                               pll_extra_clk_diag_ok
);
   timeunit 1ns;
   timeprecision 1ps;
   
   logic [3:0] pll_extra_clks;
   
   // Extra core clocks to user logic.
   // These clocks are unrelated to EMIF core clock domains. The feature is intended as a
   // way to reuse EMIF PLL to generate core clocks for designs in which physical PLLs are scarce.
   assign pll_extra_clks   = pll_c_counters[8:5];
   assign pll_extra_clk_0  = pll_extra_clks[0];
   assign pll_extra_clk_1  = pll_extra_clks[1];
   assign pll_extra_clk_2  = pll_extra_clks[2];
   assign pll_extra_clk_3  = pll_extra_clks[3];
   
   // In internal test mode, generate additional counters clocked by the extra clocks
   generate
      genvar i;
      
      if (DIAG_SIM_REGTEST_MODE && PLL_NUM_OF_EXTRA_CLKS > 0) begin: test_mode
         logic [PLL_NUM_OF_EXTRA_CLKS-1:0] pll_extra_clk_diag_done;
      
         for (i = 0; i < PLL_NUM_OF_EXTRA_CLKS; ++i)
         begin : extra_clk
            logic [9:0] counter;

            always_ff @(posedge pll_extra_clks[i] or negedge pll_locked) begin
               if (~pll_locked) begin	
                  counter <= '0;
                  pll_extra_clk_diag_done[i] <= 1'b0;
               end else begin
                  if (~counter[9]) begin
                     counter <= counter + 1'b1;
                  end
                  pll_extra_clk_diag_done[i] <= counter[9];
               end
            end         
         end
         
         assign pll_extra_clk_diag_ok = &pll_extra_clk_diag_done;
         
      end else begin : normal_mode
         assign pll_extra_clk_diag_ok = 1'b1;
      end
   endgenerate
   
endmodule
`ifdef QUESTA_INTEL_OEM
`pragma questa_oem_00 "EVeqkz9MvDzapiiVw7+udc++m43wu2P9R6Bkf/lfBn9ZttFzW71hzuu9P3yzPlvUUu1GESHEht8oUjkuxH5nYF5m2Y4yEaZOsor1W+qakklkcNM5gczDB8G/zUljAitcohcjlH9xX4F5r3RrLLQB1HrtXmnxKKrsVs2RsxKt4plRYJGUCxRjs6twKgr6lps1q22taZT7+7dZh7dYE0uKJfWB1PYeKR+rbOxvrAyMNm3HRP669h4e40UGyQSmTgYw2cfdljNSKWm+e85+uUmrYb7ks40d95f32V/kNHxQ60Z2sgrLbN82EuwqRNCnBLceiw2KyJp1V6lFQfCeK/+4j5xx0J+YaCdrqWJaoHweHsGm1MzuNdJ29PzLVC1Daiwk0FO/SxEe43FbBCtor/DUhyOHcPWY5GviHXJTLOT/VvziOsd1mVPMCv2shs73BPOB2W7hlv5vI6tpIbpnRMaoAFmDABM9d3oZLnAzha5IqtSsZ+lOKd0z3kX4PbxyoIRj0TuF9/KOAP+ZO1/syjlZqM+haNQcO3RhdIeb7khdaeO0vau2e5t91/FAsb6JZBVnNaml890Rcqia/Maoz2YKSqPxjuyi5JEyc0bgMJEHf4Ao5UROTOu7apgZOTV7S1oqaveZuMv15cB8dv03AJlgE3J+okELao3UnDK7Eo3n5h7xGJ7HxJ2CpHRDKxyzTCugfXaZ7K+yJcv8bM4+HYAz3Ed8Kgc6IB4U0QDoBJKTrDsDkY9SJA1l9URiPs7v8ncr52BH1BMfztBPbLXsFXcwcjrxw4HkvPRkanirjX5XD4t9+FWAK/eE/VGbrxaSl4kx3XJ31VWosJDrAv5d8U2KCqhP4iHC2VA6jvDnT7tX8cKt/P6IJJ2DacCM/erNjsXsI5Vqle9G18OP9EEa/BSQ8DRfET6j6UMCn5XnwQ1S4JvtI6RZsw2lTMWlY1p9IwrEzX6tlPCgnunBFgagOC+5f17EInvqWYTEslTZhGwBtz1fUvNW1DxOsHTJVYIoUgwE"
`endif