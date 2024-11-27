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


module altera_emif_arch_fm_buf_udir_cp_i # (
   parameter OCT_CONTROL_WIDTH = 1,
   parameter CALIBRATED_OCT = 1
) (
   input  logic i,
   input  logic ibar,
   output logic o,
   output logic obar,
   input  logic oct_termin
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
            .ibar(),
            .seriesterminationcontrol(),
            .parallelterminationcontrol(),
            .dynamicterminationcontrol()
            );
            
         tennm_io_ibuf ibuf_bar(
            .i(ibar),
            .o(obar),
            .term_in(oct_termin),
            .ibar(),
            .seriesterminationcontrol(),
            .parallelterminationcontrol(),
            .dynamicterminationcontrol()
            );
      end else 
      begin : no_oct
         tennm_io_ibuf ibuf(
            .i(i),
            .o(o),
            .ibar(),
            .seriesterminationcontrol(),
            .parallelterminationcontrol(),
            .dynamicterminationcontrol()
            );
            
         tennm_io_ibuf ibuf_bar(
            .i(ibar),
            .o(obar),
            .ibar(),
            .seriesterminationcontrol(),
            .parallelterminationcontrol(),
            .dynamicterminationcontrol()
            );      
      end
   endgenerate
endmodule

`ifdef QUESTA_INTEL_OEM
`pragma questa_oem_00 "O/UL8p4fjkdiniiI1fb4ptOFsAdF7Y3Hxp7T6jxKv0MGrEyaXaFTwgtlHVroTr2ly77oTzeBnz/H2ugF2Lm64wLDISiNxLkGwFrph7cf8l5oezq71gySptz6a1i1+sH+uTBP/IhfWlKmvqzXkENOz1PT/J8+EwAOHl+z3hJ5W8p9iA7X2pLUvopxcSXzYyZFe7Y+SdxGDVeHq8Bixu/tMkSijiUVBAWYj9rL+Bb7bFGrrtD9+q4PfGdZLc+RGofgiqNMaJtMWNavu7kldkyWpKcD2mO1ggSWLmbB2Z2SOdGgMOj9yjWYSsdNPCQqsQ/C5ewFThFBZ9nwtD8qIFcYxxd9rhvY58KkEe0mZyJ4vsFxzICJMjVrR/CgutXHe4YSBzeLYanptnEehaODS0H1Ycqkl5ul7IuuhEwfEiZi+A9qm8LcAUVYIb34HgIdEcNZPr/r6BylNP1Nk+eFXiUluOWHYvjTBtvcSDTGHH8Oz8tyvC0AGL8SLHz1GVKojopKJ8vXMHAf0XudIhfGUBlnuzd02KhHizurdKgVIRpY03t7M4CY/qYcqm51Ov/wfApTiosoXE/9zT9UDD6z+nDY0ROqZly+RUDh767KxFWiSGMyORJ+Ll75TLIfVyWNOHUk/iFj2h2Z+wIzJ+/Le8QXOQXPK+6Vh4OO0jwS0thyG2ibFupvzHEtJnlMjN69LTN5b154KDBdwgXKkwvHFwjkuJ/XkKMHlTWGy/6jg2uuRfmb0w3AwQNIBSkELL3kSie5Txocz7rhakkPBTvtOXVOkXLDZ89VZhVN31VQArOe+3CXdJpew5o60w0aVe3Dc/ZgaPNw4XevXHvW43u2tIHhE7fzCql9aqM+ErlvA6horhD72KssjrOlCJb1zUqtNaK8eSyVLvLseaPI9GW+waE1/wh35200ZoEb9CRO5bAluWQtlyDS65trX0Rc9XDuY54OdCJKHpzv6tc9MnBzQ9qNzyODm34LTGqZfAsQN5wcMGgI+CM3nCmUwwwEsmoU88sU"
`endif