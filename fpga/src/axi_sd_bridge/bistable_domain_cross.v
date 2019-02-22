//////////////////////////////////////////////////////////////////////
////                                                              ////
//// WISHBONE SD Card Controller IP Core                          ////
////                                                              ////
//// bistable_domain_cross.v                                      ////
////                                                              ////
//// This file is part of the WISHBONE SD Card                    ////
//// Controller IP Core project                                   ////
//// http://opencores.org/project,sd_card_controller              ////
////                                                              ////
//// Description                                                  ////
//// Clock synchronisation beetween two clock domains.            ////
//// Assumption is that input signal duration has to be at least  ////
//// one clk_b clock period.                                      //// 
////                                                              ////
//// Author(s):                                                   ////
////     - Marek Czerski, ma.czerski@gmail.com                    ////
////                                                              ////
//////////////////////////////////////////////////////////////////////
////                                                              ////
//// Copyright (C) 2013 Authors                                   ////
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

module bistable_domain_cross(
    rst,
    clk_a,
    in,
    clk_b,
    out
);
parameter width = 1;
input rst;
input clk_a;
input [width-1:0] in;
input clk_b;
output [width-1:0] out;

// We use a two-stages shift-register to synchronize in to the clk_b clock domain
reg [width-1:0] sync_clk_b [1:0];
always @(posedge clk_b or posedge rst)
begin
    if (rst == 1) begin
        sync_clk_b[0] <= 0;
        sync_clk_b[1] <= 0;
    end else begin
        sync_clk_b[0] <= in;
        sync_clk_b[1] <= sync_clk_b[0];
    end
end

assign out = sync_clk_b[1];  // new signal synchronized to (=ready to be used in) clk_b domain

endmodule 
