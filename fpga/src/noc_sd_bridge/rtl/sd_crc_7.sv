// ==========================================================================
// CRC Generation Unit - Linear Feedback Shift Register implementation
// (c) Kay Gorontzi, GHSi.de, distributed under the terms of LGPL
// ==========================================================================
module sd_crc_7(BITVAL, ENABLE, BITSTRB, CLEAR, CRC);
   input        BITVAL;                            // Next input bit
   input        ENABLE;                            // Enable calculation
   input        BITSTRB;                           // Current bit valid (Clock)
   input        CLEAR;                             // Init CRC value
   output [6:0] CRC;                               // Current output CRC value

   reg    [6:0] CRC;                               // We need output registers
   wire         inv;
   
   assign inv = BITVAL ^ CRC[6];                   // XOR required?
   
   always @(posedge BITSTRB or posedge CLEAR) begin
      if (CLEAR) begin
         CRC <= 0;                                  // Init before calculation
         end
      else begin
         if (ENABLE == 1) begin
             CRC[6] <= CRC[5];
             CRC[5] <= CRC[4];
             CRC[4] <= CRC[3];
             CRC[3] <= CRC[2] ^ inv;
             CRC[2] <= CRC[1];
             CRC[1] <= CRC[0];
             CRC[0] <= inv;
             end
         end
      end
   
endmodule