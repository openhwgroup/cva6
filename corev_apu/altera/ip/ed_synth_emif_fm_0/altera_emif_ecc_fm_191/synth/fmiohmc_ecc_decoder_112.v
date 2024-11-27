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

module fmiohmc_ecc_decoder_112 #
( parameter
    DI      = 106,
    ADDR    = 34,
    DOUT    = 98
)
(
    data,
    err_corrected,
    err_detected,
    err_fatal,
    err_sbe,
    err_addr_detected,
    err_addr,
    q
);

localparam PARITY = 8;
localparam CODE = 8;

input  [DI   - 1 : 0]   data;
output                  err_corrected;
output                  err_detected;
output                  err_fatal;
output                  err_sbe;
output                  err_addr_detected;
output [ADDR - 1 : 0]   err_addr;
output [DOUT - 1 : 0]   q;

wire err_dbe; 


wire [111 : 0] data_e;
wire [111 : 0] data_i;

generate
if(DOUT==112)
   assign data_e = data[DOUT-1:0];
else
   assign data_e = {{(112 - DOUT){1'b0}},data[DOUT-1:0]};
endgenerate

assign data_i = {data_e[111:PARITY],~data_e[PARITY-1],data_e[PARITY-2:1],~data_e[0]};

wire [PARITY - 1 : 0] parity_i;
assign parity_i = data[DI-1:DOUT];

wire [PARITY - 1 : 0] sb;

fmiohmc_ecc_pcm_112 ecc_pcm (
    .di(data_i),
    .sb(parity_i),
    .dout(sb)
);



wire [111:0] sv;

fmiohmc_ecc_sv_112 svec (.di(sb), .dout(sv));

assign q                   = data[DOUT-1:0] ^ sv[DOUT-1:0];

assign err_sbe             = |sb && ^sb;        
assign err_dbe             = |sb && ~^sb;        

assign err_detected        = err_sbe || err_dbe;    
assign err_corrected       = err_sbe;            
assign err_fatal           = err_dbe;            
assign err_addr_detected   = err_sbe && |sv[DOUT-1:DOUT-ADDR];
assign err_addr            = data[DOUT-1:DOUT-ADDR] ^ sv[DOUT-1:DOUT-ADDR];

endmodule
`ifdef QUESTA_INTEL_OEM
`pragma questa_oem_00 "sfv4CgBD2gRw66FfSic/D/DxyUF4ju6abSGjNZTz+XJ5wNcp1RmzgamT61rscvjMkkNKCYCGE4Hkry++3eL2fSJkmOtrYLQextJ2AFr2kX/6sa63SwNG1Dg8CndZgqHpcPsbI8J/52/6EA/5eQJiUNmwpEDzzugi2WpUBRBy4gGrSJ7A8zUzUrkHlWNSHE1mVOTkuXrL/BUqA6hBwwkS7qZD/J3TRyAu6L9p+9tB0EASexZBB37JqpNvLi4Wkp3MH+KkbcPA6dqOmY6A030D8x94gM/DpI2Q/D+lnCQc1HrwxZTGBhq1FkNH792u4KtulOdyoE69LiqHBnt3c9Zc77Y3gFKt6wovI7XsxQiA0WDqXE+ro+a9ScqcgB2jNkOhmcOVcGSsf4nJJSNG1exD+Qxu7013yzDNPGBQWc0BC5sfbQapEhFDOMgiD78RZo+qCra8hm8F2o8uXQgWq01YjCiKCkJWJzHObZ+7lve/AniYNScx//OlHmBto/YdV1Ea+2EDgfOv6O+oZA+fVE1XOh4JoQ//Ew+HUqWxYjz/cd0MBHO75+wdlQU8SD/VrQ8LrKqVAM1cMwk1lEKxWHS8EERT0mDxHEuSGEqQ9Bq+vLd7Ewaj5SQqynifCKf7WE2aY+RKlPmTgIJf5WZXkqNUUxcta+KjO6cXN4TbDjb+Pyb6NuEFH7i7uPPXFT8fwH1Z0y4FBgNNUchynY2xmflPBrHF3NOZiBv8QmGTgar/d5HB1h4Ll1RzKwlN1Bg+IX5uBeSwt8DAWLN5THW4x4be6rhvLzduJt1d2kNs5zx114H1LQQnOYfmssnGRUsThxyWL5XyRzH2vofon6GKL6VHKJNQVW6ieOnmeC5L8poCGne2Zy5XZC5PQONsAX84yCtyNACFRaUMe073Gn5bRxszwjj8QknP8CnwDTLxTRZtITHe0aVBavOSqRaSjGCuyP2JjPN+VFHEJiQWQ3eMNfsOzaYHXqkLOJ4UwcVihvVP9ISApQwJ1ilqy3B8JmnJeJ/I"
`endif