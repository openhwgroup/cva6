
module infer_ram #(RAM_SIZE=16, BYTE_WIDTH=8) // RAM_SIZE is in words
(
input ram_clk, ram_en,
input [BYTE_WIDTH-1:0] ram_we,
input [RAM_SIZE-1:0] ram_addr,
input [BYTE_WIDTH*8-1:0] ram_wrdata,
output [BYTE_WIDTH*8-1:0] ram_rddata);

// Expand the byte mask to a bit mask

localparam BIT_WIDTH = BYTE_WIDTH*8;
 
logic [BIT_WIDTH-1:0] wmask;
   
   always @(ram_we)
      begin
         wmask = {BIT_WIDTH{1'b0}};
         foreach (ram_we[i]) if (ram_we[i])
                wmask |= 8'hFF << i*8;
      end
   
sram #(.DATA_WIDTH(BYTE_WIDTH*8),
          .NUM_WORDS(1<<RAM_SIZE))
          sram_0
          (
           .clk_i(ram_clk),
           .req_i(ram_en),
           .we_i(|ram_we),
           .addr_i(ram_addr),
           .wdata_i(ram_wrdata),
           .be_i(ram_we ? wmask : {BIT_WIDTH{1'b1}}),
           .rdata_o(ram_rddata));
          
endmodule // infer_ram
