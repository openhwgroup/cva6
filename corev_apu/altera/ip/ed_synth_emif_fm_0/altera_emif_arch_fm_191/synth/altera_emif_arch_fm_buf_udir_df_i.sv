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


module altera_emif_arch_fm_buf_udir_df_i # (
   parameter OCT_CONTROL_WIDTH = 1,
   parameter CALIBRATED_OCT = 1
) (
   input  logic i,
   input  logic ibar,
   output logic o,
   input  logic oct_termin
);
   timeunit 1ns;
   timeprecision 1ps;
   
   generate
      if (CALIBRATED_OCT) 
      begin : cal_oct   
         tennm_io_ibuf  # (
            .differential_mode ("true")
         ) ibuf (
            .i(i),
            .ibar(ibar),
            .o(o),
            .term_in(oct_termin),
            .seriesterminationcontrol(),
            .parallelterminationcontrol(),
            .dynamicterminationcontrol()
            );
      end else 
      begin : no_oct
         tennm_io_ibuf  # (
            .differential_mode ("true")
         ) ibuf (
            .i(i),
            .ibar(ibar),
            .o(o),
            .seriesterminationcontrol(),
            .parallelterminationcontrol(),
            .dynamicterminationcontrol()
            );      
      end
   endgenerate      
endmodule

`ifdef QUESTA_INTEL_OEM
`pragma questa_oem_00 "EVeqkz9MvDzapiiVw7+udc++m43wu2P9R6Bkf/lfBn9ZttFzW71hzuu9P3yzPlvUUu1GESHEht8oUjkuxH5nYF5m2Y4yEaZOsor1W+qakklkcNM5gczDB8G/zUljAitcohcjlH9xX4F5r3RrLLQB1HrtXmnxKKrsVs2RsxKt4plRYJGUCxRjs6twKgr6lps1q22taZT7+7dZh7dYE0uKJfWB1PYeKR+rbOxvrAyMNm2SUhvjw++wGb07D+cuKvWVU+o2EWQJ70nDOdTTx9xPz4E2lZBeYmAYpWQi2sRSoicAukT+2yLYNmPgSyDisR0jYO7W+L/nGmGGzAY8qPic6n+wwsdWnlxDCwCL3+rKM0LonRdNSrbVc5+zCMKVA+dawIhT8tGueE19yDaqo2avP8vIAzDPMLtmKJWo9DrlZ+NQbwQsZNPy7aZByBlOwTW9egnw4wyOA5REBYZog3zmAykF5rZQ4kO+hf8+E3YmzEbZyAnxpZUQBYpUuCunt/G5s/vBRz5lfuBh1FTkcKRM4rp6xVwrJOouNDeP24a5ka/Sj45l+Evd1raiohhEwSJ2DVkrQczZO/QU3r840v+8m+elqGrMYLajz8jLrB6wMwbzUR4Ut9gzIB1fcBMOqW7oA1AdGeabEAwUYeBcqcqB8GC26lcGzbpHHPYLrIDykv0OyhDnmYKVK5Op+2ncVNd3zzbssD29v8UnohAYtwKXDEgM252o+GFHyVX9U8T3wsqRQRWOOShrHnxjRINvdFe4Vs+Ww1MzEAu7NIBhdKDV9MTBQg6CWnZBWqbHpedZq4ZajmfK+GMSaO0E8c0WbJFowdPXinBNDdW0ltR0jxOw4dneXEwEhGvJDZr1bxYI2UCFlkJOHY6fDvQL/vAvw/iHt1uZuWplT3gNPrN0Nd51JwzLfMoxtSPIMTU+eDQBmpPxWSyyqufG/zccEuTq4yxWDqvG3e7MA/IlDgTxNlmWxNfHvYgEoZ4UxS+bvh4M4zYiFyd4tsvC0UqkGm7gqy3x"
`endif