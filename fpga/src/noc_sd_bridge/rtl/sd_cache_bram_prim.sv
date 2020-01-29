// Copyright 1986-2018 Xilinx, Inc. All Rights Reserved.
// --------------------------------------------------------------------------------

module sd_cache_bram(clka, ena, wea, addra, dina, douta);
  input clka;
  input ena;
  input [7:0]wea;
  input [8:0]addra;
  input [63:0]dina;
  output [63:0]douta;

   genvar r;

  generate for (r = 0; r < 8; r=r+1)
    RAMB16_S9
    RAMB16_S9_inst
      (
       .CLK    ( clka                     ),     // Port A Clock
       .DO     ( douta[r*8 +: 8]          ),     // Port A 1-bit Data Output
       .DOP    (                          ),
       .ADDR   ( {2'b0,addra}             ),     // Port A 14-bit Address Input
       .DI     ( dina[r*8 +: 8]           ),     // Port A 1-bit Data Input
       .DIP    ( 1'b0                     ),
       .EN     ( ena                      ),     // Port A RAM Enable Input
       .SSR    ( 1'b0                     ),     // Port A Synchronous Set/Reset Input
       .WE     ( wea[r]                   )      // Port A Write Enable Input
       );
  endgenerate

endmodule
