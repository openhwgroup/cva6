//////////////////////////////////////////////////////////////////////
////                                                              ////
//// WISHBONE SD Card Controller IP Core                          ////
////                                                              ////
//// monostable_domain_cross.v                                    ////
////                                                              ////
//// This file is part of the WISHBONE SD Card                    ////
//// Controller IP Core project                                   ////
//// http://opencores.org/project,sd_card_controller              ////
////                                                              ////
//// Description                                                  ////
//// Clock synchronisation beetween two clock domains.            ////
//// Assumption is that input signal duration is always           //// 
//// one clk_a clock period. If that is true output signal        ////
//// duration is always one clk_b clock period.                   ////
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

module monostable_domain_cross(
    input rst,
    input clk_a,
    input in, 
    input clk_b,
    output out
);

// this changes level when the in is seen in clk_a
reg toggle_clk_a;
always @(posedge clk_a or posedge rst)
begin
    if (rst)
        toggle_clk_a <= 0;
    else
        toggle_clk_a <= toggle_clk_a ^ in;
end

// which can then be sync-ed to clk_b
(* ASYNC_REG="TRUE" *) reg sync_clk_b0, sync_clk_b1, sync_clk_b2;
always @(posedge clk_b or posedge rst)
begin
    if (rst) begin
        sync_clk_b2 <= 0;
        sync_clk_b1 <= 0;
        sync_clk_b0 <= 0;
    end
    else begin
        sync_clk_b2 <= sync_clk_b1;
        sync_clk_b1 <= sync_clk_b0;
        sync_clk_b0 <= toggle_clk_a;
    end
end

// and recreate the flag in clk_b
assign out = (sync_clk_b2 ^ sync_clk_b1);

endmodule 
