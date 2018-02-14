`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 04.02.2018 14:12:22
// Design Name: 
// Module Name: infer_ram
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////

// See LICENSE for license details.

module infer_ram #(RAM_SIZE=16, BYTE_WIDTH=8) // RAM_SIZE is in words
(
input ram_clk, ram_en,
input [BYTE_WIDTH-1:0] ram_we,
input [RAM_SIZE-1:0] ram_addr,
input [BYTE_WIDTH*8-1:0] ram_wrdata,
output [BYTE_WIDTH*8-1:0] ram_rddata);

   localparam RAM_LINE          = 2 ** RAM_SIZE;   
   integer                initvar;

   reg [BYTE_WIDTH*8-1:0] ram [0 : RAM_LINE-1];
   reg [RAM_SIZE-1:0]    ram_addr_delay;
   
   initial
     begin
      ram_addr_delay = {RAM_SIZE{1'b0}};
      for (initvar = 0; initvar < RAM_LINE; initvar = initvar+1)
        ram[initvar] = {BYTE_WIDTH {8'b0}};
     end
   
   always @(posedge ram_clk)
    begin
     if(ram_en) begin
        ram_addr_delay <= ram_addr;
        foreach (ram_we[i])
          if(ram_we[i]) ram[ram_addr][i*8 +:8] <= ram_wrdata[i*8 +: 8];
     end
    end

   assign ram_rddata = ram[ram_addr_delay];

   initial $readmemh("cnvmem64.hex", ram);
   
endmodule
