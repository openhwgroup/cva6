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


module altera_emif_arch_fm_buf_udir_se_i #(
   parameter OCT_CONTROL_WIDTH = 1,
   parameter CALIBRATED_OCT = 1
) (
   input  logic i,
   input  logic oct_termin,
   output logic o
);
   timeunit 1ns;
   timeprecision 1ps;

   generate
      if (CALIBRATED_OCT) 
      begin : cal_oct
         tennm_io_ibuf ibuf(
            .i(i),
            .o(o),
            .term_in(oct_termin),
            .seriesterminationcontrol(),
            .parallelterminationcontrol(),
            .ibar(),
            .dynamicterminationcontrol()
            );    
      end else 
      begin : no_oct
         tennm_io_ibuf ibuf(
            .i(i),
            .o(o),
            .seriesterminationcontrol(),
            .parallelterminationcontrol(),
            .ibar(),
            .dynamicterminationcontrol()
            );
      end
   endgenerate
endmodule

`ifdef QUESTA_INTEL_OEM
`pragma questa_oem_00 "EVeqkz9MvDzapiiVw7+udc++m43wu2P9R6Bkf/lfBn9ZttFzW71hzuu9P3yzPlvUUu1GESHEht8oUjkuxH5nYF5m2Y4yEaZOsor1W+qakklkcNM5gczDB8G/zUljAitcohcjlH9xX4F5r3RrLLQB1HrtXmnxKKrsVs2RsxKt4plRYJGUCxRjs6twKgr6lps1q22taZT7+7dZh7dYE0uKJfWB1PYeKR+rbOxvrAyMNm2FmthPOs++Dvdswo7+h08zwz/9gADvK/6sUMDX7whuEsL9NVEK2plHS/Y6vm2eNMDNCJt2UBZPXA6a5NSlJIh7gHcRInIyrMxFfupxD3mc10hF6Kbm2Gxn3/wIVV3ZMg20NVk9oe8XY6oKn7dl7eZ2KcITCYhCEU6PQp4jjZ02aNXBYrEocXu0/jX247tso6eX/j1Mbuv4a4dnrsv9qO5YETYsIrvgHW2lWD8Wt2oJn8owmXX7TP0SCURrFg+42GVvhx+BdHCAGQpxrcZNU9YuMKmnvZELmnpcFRhhfne3T3Tmz5bacI+qsB8eQJWFLQTmPAo2LOOWAZYTz+vD5Dk7Jg2IBeUgbf2z70wXkgQIuurhtWBWTIiYkqbyHoYrrhLqQ4cCr/MHNtrfYR1BrOaMvpFmQL4WBF/9wr+dvO5BfhO+nqX+hDdRcXyZHkP3+8Ngp3OrcghpyEgb0j54J2iROHwbZgWUc3iPZiv5ifgfo+CguNWfyQh8fneY2SqKXCA6ra7M9UHmFd4pcEhjeEXIAEVKOS9oDbele+0BG3HYVZs/LpjLxI2BLbhWJawaGo8tPRTzk/fBoWf/5kUff4sLPqZnn1PoubkJ0ungaleVHQYuihAVhmVW6D/Bp0pUgM3kJZd5W4sd6UNyyGA/s+rK8OtsuMEIMMBJICe5XKCWbsZ3a9Sg2tkhJjm/5OHsoOY6HoFhPedykVA5O1d8pGiQuWtC+GsRlK8Z3UeOzNnL/f5BWXabOU6VfVuMbzPZ7tDjGILH47m18xtD6c5E5J3Q"
`endif