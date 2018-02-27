//////////////////////////////////////////////////////////////////////
////                                                              ////
//// WISHBONE SD Card Controller IP Core                          ////
////                                                              ////
//// sd_clock_divider.v                                           ////
////                                                              ////
//// This file is part of the WISHBONE SD Card                    ////
//// Controller IP Core project                                   ////
//// http://opencores.org/project,sd_card_controller              ////
////                                                              ////
//// Description                                                  ////
//// Control of sd card clock rate                                ////
////                                                              ////
//// Author(s):                                                   ////
////     - Marek Czerski, ma.czerski@gmail.com                    ////
////                                                              ////
//////////////////////////////////////////////////////////////////////
////                                                              ////
//// Copyright (C) 2013 Authors                                   ////
////                                                              ////
//// Based on original work by                                    ////
////     Adam Edvardsson (adam.edvardsson@orsoc.se)               ////
////                                                              ////
////     Copyright (C) 2009 Authors                               ////
////                                                              ////
//// This source file may be used and distributed without         ////
//// restriction provided that this copyright statement is not    ////
//// removed from the file and that any derivative work contains  ////
//// the original copyright notice and the associated disclaimer. ////
////                                                              ////
//// This source file is free software; you can redistribute it   ////
//// and/or modify it under the terms of the GNU Lesser General   ////
//// Public License as published by the Free Software Foundation; ////
//// either version 2.1 of the License, or (at your option) any   ////
//// later version.                                               ////
////                                                              ////
//// This source is distributed in the hope that it will be       ////
//// useful, but WITHOUT ANY WARRANTY; without even the implied   ////
//// warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR      ////
//// PURPOSE. See the GNU Lesser General Public License for more  ////
//// details.                                                     ////
////                                                              ////
//// You should have received a copy of the GNU Lesser General    ////
//// Public License along with this source; if not, download it   ////
//// from http://www.opencores.org/lgpl.shtml                     ////
////                                                              ////
//////////////////////////////////////////////////////////////////////

module sd_clock_divider (
                         input       CLK,
                         input [7:0] DIVIDER,
                         input       RST,
                         output      SD_CLK
                         );

   reg [7:0]                         ClockDiv;
   reg                               SD_CLK_O;

   BUFG SD_CLK_buf_inst (
                    .O(SD_CLK), // 1-bit output: Clock output
                    .I(SD_CLK_O)  // 1-bit input: Clock input
                    );

   always @(posedge CLK or posedge RST)
     begin
        if (RST) begin
           ClockDiv <= 8'b0000_0000;
           SD_CLK_O <= 0;
        end
        else if (ClockDiv == DIVIDER) begin
           ClockDiv <= 0;
           SD_CLK_O <= ~SD_CLK_O;
        end else begin
           ClockDiv <= ClockDiv + 8'h1;
           SD_CLK_O <= SD_CLK_O;
        end
     end

endmodule


