// ==========================================================================
// CRC Generation Unit - Linear Feedback Shift Register implementation
// (c) Kay Gorontzi, GHSi.de, distributed under the terms of LGPL
// ==========================================================================
module sd_crc_16(BITVAL, ENABLE, BITSTRB, CLEAR, CRC);
   input        BITVAL;                            // Next input bit
   input        ENABLE;                            // Enable calculation
   input        BITSTRB;                           // Current bit valid (Clock)
   input        CLEAR;                             // Init CRC value
   output [15:0] CRC;                               // Current output CRC value

   reg    [15:0] CRC;                               // We need output registers
   wire         inv;
   
   assign inv = BITVAL ^ CRC[15];                   // XOR required?
   
   always @(posedge BITSTRB or posedge CLEAR) begin
      if (CLEAR) begin
         CRC <= 0;                                  // Init before calculation
         end
      else begin
         if (ENABLE == 1) begin
             CRC[15] <= CRC[14];
             CRC[14] <= CRC[13];
             CRC[13] <= CRC[12];
             CRC[12] <= CRC[11] ^ inv;
             CRC[11] <= CRC[10];
             CRC[10] <= CRC[9];
             CRC[9] <= CRC[8];
             CRC[8] <= CRC[7];
             CRC[7] <= CRC[6];
             CRC[6] <= CRC[5];
             CRC[5] <= CRC[4] ^ inv;
             CRC[4] <= CRC[3];
             CRC[3] <= CRC[2];
             CRC[2] <= CRC[1];
             CRC[1] <= CRC[0];
             CRC[0] <= inv;
             end
         end
      end
   
endmodule