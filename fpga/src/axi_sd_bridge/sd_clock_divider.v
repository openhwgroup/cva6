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
           input CLK,
           input [7:0] DIVIDER,
           input RST,
           output SD_CLK
       );

    reg fast_clk,   slow_clk;
    reg [7:0]   counter;

    always @(posedge CLK or posedge RST) begin
        if (RST) begin
            counter     <=  8'd0;
            fast_clk    <=  1'b0;
            slow_clk    <=  1'b0;
        end
        else begin
            fast_clk    <=  ~fast_clk;
            
            if (counter ==  8'd99) begin
                counter     <=  8'd0;
                slow_clk    <=  ~slow_clk;
            end
            else begin
                counter     <=  counter +   1;
            end
        end
    end

    BUFGMUX sd_clk_bufgmux(
        .I0(slow_clk),
        .I1(fast_clk),
        .S(DIVIDER == 0),
        .O(SD_CLK)
        );

endmodule


