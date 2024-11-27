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

module fmiohmc_ecc_encoder_112 
#( parameter
   DI          = 98,
   DOUT        = 106
)

(
   data,
   q
);

localparam PARITY = 8;

input	   [DI-1:0]  data;
output	[DOUT-1:0]  q;

wire [111:0] data_e;
wire [111:0] data_i;
generate
   if(DI==112)
      assign data_e     = data;
   else
      assign data_e     = {{(112-DI){1'b0}},data};
endgenerate
assign data_i     = {data_e[111:PARITY],~data_e[PARITY-1],data_e[PARITY-2:1],~data_e[0]};

wire [PARITY-1:0] sb;

fmiohmc_ecc_pcm_112 ecc_pcm (
   .di(data_i),
   .sb({PARITY{1'b0}}),
   .dout(sb)
);

assign q          = {sb,data[DI-1:0]};

endmodule
`ifdef QUESTA_INTEL_OEM
`pragma questa_oem_00 "sfv4CgBD2gRw66FfSic/D/DxyUF4ju6abSGjNZTz+XJ5wNcp1RmzgamT61rscvjMkkNKCYCGE4Hkry++3eL2fSJkmOtrYLQextJ2AFr2kX/6sa63SwNG1Dg8CndZgqHpcPsbI8J/52/6EA/5eQJiUNmwpEDzzugi2WpUBRBy4gGrSJ7A8zUzUrkHlWNSHE1mVOTkuXrL/BUqA6hBwwkS7qZD/J3TRyAu6L9p+9tB0EBvpnDJH3Gywd1hOtha9cNq6jTHNq1cG4iMFvZe5LZTx4C9k5in2kJ+b3axV7BL5A/eTPHrlSzF4zLvLBzOfE/WS+1SsRyLgUHzrcKkv0eBHxl2f6H+eXcMrOqaJXPASKbBVHLS2lC0e5WiM+GGZRh2o7O8hpOWfTvqf6fNoe5CG86kQSfiMvMipftTWImgpBPn8FdSNnX6uVLUpLAjAdyBg6kENT8cG5uy2/nw0JWbzHjVvI25TZnRV0At/Pta5ysaJGeq6aNC2pn1KmhzM7CJzduSefvnaxyz+qxDYdFD4rBcDMDDa6rginkgzKkZfO3mb505yC/4GFcpyD/ZrWViToZsbhiP8wAIi4ONDTkKNoyo7hg0NKG2ls5NwGJLM8GdTLTaZlsFDRNr9+TFWHBVXCsIxGYgi43ar1fX0/QBSBPpf4tyW9mT0uCyIAcY8JhtDgyubOazqTNntKgZB/0N2RcibFteqqD6FgYFpV9BJNqNN9hCO28SKGW7vHdTbj3J8lp2mXgk5enXtrVyJPLEk5KZng6hya1LhrcHfdqJzZPlvFpqw5Al/3i49pSfavpj+BVbtlpVaHMz4TVGwhOmsuVwY/bfJYJ85CbaHMciv7QKI0WyRrnFlMn0sEpepkBLJ+5dcNRWqkrgsa81+o/LdLSsOx0cwDBp9VAmkEE9g79iwIsTDSuDXNgEoGUSvtQhhs0uOpwF/1VAazmOYhto4xdi8k+S7pqRpGNaLdBAIR9BDsW6QXlRi7hWr7GvpqCjiUF6EyDkRma9uFffhqyJ"
`endif