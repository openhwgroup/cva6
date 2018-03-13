module axi_ram_wrap_nasti #(
    AXI_ID_WIDTH = 10,               // id width
    AXI_ADDR_WIDTH = 64,             // address width
    AXI_DATA_WIDTH = 64,             // width of data
    AXI_USER_WIDTH = 1,              // width of user field, must > 0, let synthesizer trim it if not in use
    MEM_ADDR_WIDTH = 13
    )
(
AXI_BUS.Slave slave,
input clk_i, rst_ni,
output wire [AXI_DATA_WIDTH/8-1 : 0] bram_we_a,
output wire [MEM_ADDR_WIDTH-1 : 0] bram_addr_a,
output wire [AXI_DATA_WIDTH-1 : 0] bram_wrdata_a,
input  wire [AXI_DATA_WIDTH-1 : 0] bram_rddata_a,
output wire          bram_rst_a, bram_clk_a, bram_en_a
);

nasti_channel
     #(
       .ID_WIDTH    ( AXI_ID_WIDTH      ),
       .USER_WIDTH  ( AXI_USER_WIDTH    ),
       .ADDR_WIDTH  ( AXI_ADDR_WIDTH    ),
       .DATA_WIDTH  ( AXI_DATA_WIDTH    ))
   slave0_nasti();

nasti_converter #(
    .ID_WIDTH(AXI_ID_WIDTH),               // id width
    .ADDR_WIDTH(AXI_ADDR_WIDTH),             // address width
    .DATA_WIDTH(AXI_DATA_WIDTH),             // width of data
    .USER_WIDTH(AXI_USER_WIDTH)              // width of user field, must > 0, let synthesizer trim it if not in use
    ) cnvi(.incoming_if(slave), .outgoing_nasti(slave0_nasti));

nasti_bram_ctrl # (
   .ADDR_WIDTH(AXI_ADDR_WIDTH),
   .DATA_WIDTH(AXI_DATA_WIDTH),
   .BRAM_ADDR_WIDTH(MEM_ADDR_WIDTH),
   .ID_WIDTH(AXI_ID_WIDTH)
) (
   .s_nasti_aclk(clk_i),
   .s_nasti_aresetn(rst_ni),
   .s_nasti(slave0_nasti),
   .bram_clk(bram_clk_a),
   .bram_rst(bram_rst_a),
   .bram_en(bram_en_a),
   .bram_we(bram_we_a),
   .bram_addr(bram_addr_a),
   .bram_wrdata(bram_wrdata_a),
   .bram_rddata(bram_rddata_a)
);
    
endmodule
