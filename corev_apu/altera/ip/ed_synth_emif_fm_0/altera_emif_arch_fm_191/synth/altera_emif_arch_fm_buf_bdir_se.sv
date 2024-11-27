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


module altera_emif_arch_fm_buf_bdir_se #(
   parameter OCT_CONTROL_WIDTH = 1,
   parameter HPRX_CTLE_EN = "off",
   parameter HPRX_OFFSET_CAL = "false",
   parameter CALIBRATED_OCT = 1
) (
   inout  tri   io,
   output logic ibuf_o,
   input  logic obuf_i,
   input  logic obuf_oe,
   input  logic obuf_dtc,
   input  logic oct_termin
);
   timeunit 1ns;
   timeprecision 1ps;
   
   generate
      if (CALIBRATED_OCT) 
      begin : cal_oct
         tennm_io_ibuf # (
            .hprx_ctle_en (HPRX_CTLE_EN),
            .hprx_offset_cal (HPRX_OFFSET_CAL)
         ) ibuf (
            .i(io),
            .o(ibuf_o),
            .term_in(oct_termin),
            .seriesterminationcontrol(),
            .parallelterminationcontrol(),
            .dynamicterminationcontrol(),
            .ibar()
            );
            
         tennm_io_obuf obuf (
            .i(obuf_i),
            .o(io),
            .oe(obuf_oe),
            .term_in(oct_termin),
            .dynamicterminationcontrol(obuf_dtc),
            .seriesterminationcontrol(),
            .parallelterminationcontrol(),
            .obar(),
            .devoe()
            );
      end else 
      begin : no_oct
         tennm_io_ibuf # (
            .hprx_ctle_en (HPRX_CTLE_EN),
            .hprx_offset_cal (HPRX_OFFSET_CAL)
         ) ibuf (
            .i(io),
            .o(ibuf_o),
            .seriesterminationcontrol(),
            .parallelterminationcontrol(),
            .dynamicterminationcontrol(),
            .ibar()
         );
            
         tennm_io_obuf obuf (
            .i(obuf_i),
            .o(io),
            .oe(obuf_oe),
            .dynamicterminationcontrol(),
            .seriesterminationcontrol(),
            .parallelterminationcontrol(),
            .obar(),
            .devoe()
            );      
      end
   endgenerate            
endmodule

`ifdef QUESTA_INTEL_OEM
`pragma questa_oem_00 "O/UL8p4fjkdiniiI1fb4ptOFsAdF7Y3Hxp7T6jxKv0MGrEyaXaFTwgtlHVroTr2ly77oTzeBnz/H2ugF2Lm64wLDISiNxLkGwFrph7cf8l5oezq71gySptz6a1i1+sH+uTBP/IhfWlKmvqzXkENOz1PT/J8+EwAOHl+z3hJ5W8p9iA7X2pLUvopxcSXzYyZFe7Y+SdxGDVeHq8Bixu/tMkSijiUVBAWYj9rL+Bb7bFHJ77jCjl2qih2EzD3gNKqiwaKup7hP2dRq7UROjsDVZ30rRw4diZ+JZGo3VQ3SwX32eBGN93oxDhZ9E79D4qG+AQw9gHDwoKNDrqCpWGUxEj85vZi7kHpE9ztbJabjcqANFKeKgPHo0ahI0s/L+M5+udKVtBmpqz9NiTc3hM78+Z6/O3q/BxuPF5LmPb8DOJB9s6qL3tpA2W4elHPBhCuHzjlkTEYMxlgzaIbgujGLt0kpVGAOGtc1ZD2b7MK1O5E6PuWRHY2M374JF0DBXiXnJupJyMYTdPRAErVQR0avuytHspGunfLeH/KYDzKropWFqYpAlx3yNDRSfl9JCgLUWV338UJtMdev92TuRV9MLDpKGbhUhNXoikvoxQOxoWBtLfIFd1wAy3WrAplZbr3C0Aoj0JuMKhkAoeNuTfHePlTuWbM73wbtcw5/CIaHDunIklgZZ23DRMjn0gHwZJjZ5lcf6b+/78rAPQBknj+chUO+LZQtyshQ5FbeU/INwQxMdsvBZllPg99X//GePjzgQX8TUtHirjMGoLWJmz0GzroxxUEgyy3Wx8DhBGYmkDKCbekLC2/bC9yNi/VvLykACv8y/tjgKQQnElEU2/KKgqovLJiTTjmKGYvczr851zigocF71cYz6omqtl2uTQ2OFlNnLgSz7KDJePy6W6g4ifRd0gsC/Njy8f/H/TpmMzoO4asAlEp5QWF99P5OtYfmlmcADEZM0mxGyOooRfpkDIkAQI/vnbzAntjbCWEMW6NoNxKilPtXSLJ+WGj1U1ts"
`endif