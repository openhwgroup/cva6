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





`timescale 1 ps / 1 ps

module fmiohmc_ecc_cb
#(parameter DAT='d 8) (

  input  wire [DAT-1:0] di,     
  output wire           dout    
  );

  assign dout = ^di;
endmodule

`ifdef QUESTA_INTEL_OEM
`pragma questa_oem_00 "sfv4CgBD2gRw66FfSic/D/DxyUF4ju6abSGjNZTz+XJ5wNcp1RmzgamT61rscvjMkkNKCYCGE4Hkry++3eL2fSJkmOtrYLQextJ2AFr2kX/6sa63SwNG1Dg8CndZgqHpcPsbI8J/52/6EA/5eQJiUNmwpEDzzugi2WpUBRBy4gGrSJ7A8zUzUrkHlWNSHE1mVOTkuXrL/BUqA6hBwwkS7qZD/J3TRyAu6L9p+9tB0EBb+GwNRZYJnVDIiruXV09Fs7UBAg5nhC5sN9VFWsWgS9dfRDj2wBpGRfwyj8zHzy6X6u5C5UJAFRGc7jFDI6rnoQmqYWZi06FmQQPfMI0O6Hfz3/iyjufPmNLu4SQ6xqT7cf66w17yqjnijDB1P83cIZrRkNAl4kPvU1s/MMcPWatQLZwcEwy3iQlNiCZy3KqnTom5EnueV5I2PEW7CoQU0Di1SA9Rjwtzb8PrbXF0Jtaf0mCyvb6vop9RgKk8HtUsXWWeaQ+fw+OeZmMGeOHFWw8oFc1ihkFba7xawoQQvlosZ8A6UvdZ9ggV0ILFlWiuFdaz3JBzXm1kNp2oCegZWeCDKZDueE4Ke+zzf6hrhNAs1M6upgpLco7jWnXKnf86KzwOGCpcSmT9MZIzuEl6Kel3NlJg2CengBGBV+9GadH65qKGjeXF1U4Nrff+0tRxKjCg2ySL4XmqbCZ1FiIPBZZn70+U7h7peCmGPGdcIjFeWzIbnGHV2xmoZTrBYRV4dvYECp6AsUGCQh6/EeM2wxjD6wSVxH4mNN/GtALbga4QacKyy0CDUXg20wVnYP5lRg2sHzAwTrIvg7h2aWQ0nu8Id0+JngU/uajgHHlF0P8Saf+IJJz7uWiOMsISVgIcRWTtA7+qPni3HHok/Cjqx9MmF7yHL3SHVMRR8gIkOCrXu2NgpKSAMrJAj7aVAU4WWrccsG8lR4SLYu4VH1/fnABmGTC4TNgJWLPN4qGLt+kBexTMYMWHXFq3/9HOyQhfUVBcHw/wSQBP5QecqdB6"
`endif