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


module altera_emif_arch_fm_buf_udir_df_o #(
   parameter OCT_CONTROL_WIDTH = 1,
   parameter CALIBRATED_OCT = 1
) (
   input  logic i,
   input  logic ibar,
   output logic o,
   output logic obar,
   input  logic oein,
   input  logic oeinb,
   input  logic oct_termin
);
   timeunit 1ns;
   timeprecision 1ps;

   localparam DCCEN = "true";

   logic pdiff_out_o;
   logic pdiff_out_obar;

   logic pdiff_out_oe;
   logic pdiff_out_oebar;

   tennm_pseudo_diff_out # (
      .feedthrough("true")
   ) pdiff_out (
      .i(i),
      .ibar(ibar),
      .o(pdiff_out_o),
      .obar(pdiff_out_obar),
      .oein(oein),
      .oebin(oeinb),
      .oeout(pdiff_out_oe),
      .oebout(pdiff_out_oebar),
      .dtcin(),
      .dtcbarin(),
      .dtc(),
      .dtcbar()
   );

   generate
      if (CALIBRATED_OCT)
      begin : cal_oct
         tennm_io_obuf # (
            .dccen(DCCEN)
         ) obuf (
            .i(pdiff_out_o),
            .o(o),
            .oe(pdiff_out_oe),
            .term_in(oct_termin),
            .seriesterminationcontrol(),
            .parallelterminationcontrol(),
            .dynamicterminationcontrol(),
            .obar(),
            .devoe()
         );

         tennm_io_obuf # (
            .dccen(DCCEN)
         ) obuf_bar (
            .i(pdiff_out_obar),
            .o(obar),
            .oe(pdiff_out_oebar),
            .term_in(oct_termin),
            .seriesterminationcontrol(),
            .parallelterminationcontrol(),
            .dynamicterminationcontrol(),
            .obar(),
            .devoe()
         );
      end else
      begin : no_oct
         tennm_io_obuf # (
            .dccen(DCCEN)
         ) obuf (
            .i(pdiff_out_o),
            .o(o),
            .oe(pdiff_out_oe),
            .seriesterminationcontrol(),
            .parallelterminationcontrol(),
            .dynamicterminationcontrol(),
            .obar(),
            .devoe()
         );

         tennm_io_obuf # (
            .dccen(DCCEN)
         ) obuf_bar (
            .i(pdiff_out_obar),
            .o(obar),
            .oe(pdiff_out_oebar),
            .seriesterminationcontrol(),
            .parallelterminationcontrol(),
            .dynamicterminationcontrol(),
            .obar(),
            .devoe()
         );
      end
   endgenerate

endmodule
`ifdef QUESTA_INTEL_OEM
`pragma questa_oem_00 "EVeqkz9MvDzapiiVw7+udc++m43wu2P9R6Bkf/lfBn9ZttFzW71hzuu9P3yzPlvUUu1GESHEht8oUjkuxH5nYF5m2Y4yEaZOsor1W+qakklkcNM5gczDB8G/zUljAitcohcjlH9xX4F5r3RrLLQB1HrtXmnxKKrsVs2RsxKt4plRYJGUCxRjs6twKgr6lps1q22taZT7+7dZh7dYE0uKJfWB1PYeKR+rbOxvrAyMNm2iyaudw3CXs5bnDhNz55tBPhJE7/EqCIrx3CP+FC5DOSLzcm6keCWrcljkpG5uNx9t3CMiivc9hetJr2FTBnGDixn7EhRAngy0TjjXTaT68INZnZ+9yqAjCBzqyMb4pyxK053BpRPfcJwP3pKBrQ/AoyqdQ/XTdT/AqBfXk0yCfVV7Za8TIP3rEBF34QkBbkRVLcNNvVwOzsVVkdY0IT8LdqLKYMX45sgszZwX0gK5OCKS5dSliUyRAyqoeNMiuBoHxFeMGMtJ2csCzwBeGA3LaqZRdIhl/WairZm36kh8Zm8H0vNKhnPGbNxUqPd0old/nTVudZVad11PmuRA8aFK+M4kIYDAQNLrMGMliBVds4fPvDqk0mljaRTR5f24GNho5q1VTDJhQcocxhoWQ3j1Q71DZZqtu7BC8+QFj/UVlmDloq+Z/9/GQ0xBm41bpxFuElY9CORWIpd7j+i5fWFgU83O04pa7oy/hmtejYQgjkAg2LEPxPxd43ohTPMYhmzl2zot1TvbWsQ2uYLYpAUy0f5Ui4lutq+6PHCSJ+NWR8UgzmYfazy+heBMB59tKmZAikE4eWGyjaihWivyBy4+6Ez4InrAIm7xsKRJPmUfSB1akTdHuV0x+Z+C2YYUYdSxnmjH+I6dcQc7Ha/8BJvwTt81VY6bTkFvmZU8a7I+edRnniRcMfLDiR2QmjuGicyhpvq5ZkjAAToYSkSIYKKOYSl1iUyG8wNgC/0AF/t8+OYVnzr6askUBZDqY8v0xbTDemoEyiB0Gs9Q0GoVJAL4"
`endif