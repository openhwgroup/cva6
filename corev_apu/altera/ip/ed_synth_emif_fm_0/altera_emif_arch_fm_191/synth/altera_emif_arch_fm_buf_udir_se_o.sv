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


module altera_emif_arch_fm_buf_udir_se_o #(
   parameter OCT_CONTROL_WIDTH = 1,
   parameter CALIBRATED_OCT = 1
) (
   input  logic i,
   output logic o,
   input  logic oe,
   input  logic oct_termin
);
   timeunit 1ns;
   timeprecision 1ps;

   generate
      if (CALIBRATED_OCT) 
      begin : cal_oct
         tennm_io_obuf obuf (
            .i(i),
            .o(o),
            .term_in(oct_termin),
            .seriesterminationcontrol(),
            .parallelterminationcontrol(),
            .obar(),
            .oe(oe),
            .dynamicterminationcontrol(),
            .devoe()
            );    
      end else 
      begin : no_oct
         tennm_io_obuf obuf (
            .i(i),
            .o(o),
            .seriesterminationcontrol(),
            .parallelterminationcontrol(),
            .obar(),
            .oe(oe),
            .dynamicterminationcontrol(),
            .devoe()
            );    
      end
   endgenerate
endmodule

`ifdef QUESTA_INTEL_OEM
`pragma questa_oem_00 "EVeqkz9MvDzapiiVw7+udc++m43wu2P9R6Bkf/lfBn9ZttFzW71hzuu9P3yzPlvUUu1GESHEht8oUjkuxH5nYF5m2Y4yEaZOsor1W+qakklkcNM5gczDB8G/zUljAitcohcjlH9xX4F5r3RrLLQB1HrtXmnxKKrsVs2RsxKt4plRYJGUCxRjs6twKgr6lps1q22taZT7+7dZh7dYE0uKJfWB1PYeKR+rbOxvrAyMNm0tDDu14dsl4TOuKMl087O8gOU7F660uXBhz5+pbY9/eMzX4u3w+gtxPLCnxFqRDACfsgc8ZIJ5YgseD0Rfaj2UEVy6N1dIoQhXCYVMzK6NUTR1AyxTLIOwwNSYVmfPjfxkpm2eleyU9kZEQcYWQ457Ww/TaQlo552Eqzbp+y6PAo8kLS9R13ZI+01b2nNKBRXVGGtXbFjS1OuPH1RPyg3GEOvV5w3XAHVSMPqM8o3hzzhw9USZ/FA+VgVGV2b/QTQBfsmr9tK8eOUav8mwUALFeDEgxeewKwjYBaj9ywmk1C4IuLrJFPUnmHJ4emonoKtvA8Tt9mZ+xh14Kvg+RXfJkgP+TM4Fd6YjYZelWVRmI9jDnrDY6/KfbHCZvsrkVXulso6obQaBz6qPQ0vQ2ac0hgKa0Zkst+4N6i9ANrvO6koZp9g6wuvl2o50IP8eQDRr6m9mOQ+otZa0OrlaZEY7/9vOD83qCFNfVR3jjQ8o256sLF6WrpdbyzsZ6Ph0hjKkX7pGRkjc/+qJVVKnRiPJSPHbWM++ikwEKIHeOhqwtxXRbrkdCRNmsdKxlv2ZPGM3OKY9Mm8jJWly6A9/TkkZGDATi7TpvJLxHQKSxdSfGJWx4NRWwMVohKigBFHuwvU1RhW9DiGMLB4Qvk3kL9Bs90MqgbIU4rKdKH7Y108LvcjGNzI92qIWrw/pwCzJ3id88Ahwm5Rbke8ZuVvMCR85rSlFM1rOAFP32hws9wmbj3RZAa7rc5z0uzg2/IZMQZOsweCxE8a4IoctwgMU394t"
`endif