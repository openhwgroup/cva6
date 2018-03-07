module axi_ram_wrap  #(
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

`ifdef NASTI_BRAM

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

`else
`ifdef BRAM_OPEN
axi_bram_ctrl_ariane
   #(
     .AXI4_ID_WIDTH      ( AXI_ID_WIDTH      ),
     .AXI4_ADDRESS_WIDTH ( AXI_ADDR_WIDTH    ),
     .AXI4_RDATA_WIDTH   ( AXI_DATA_WIDTH    ),
     .AXI4_WDATA_WIDTH   ( AXI_DATA_WIDTH    ),
     .AXI4_USER_WIDTH    ( AXI_USER_WIDTH    ),
     .MEM_ADDR_WIDTH     ( MEM_ADDR_WIDTH    )
 ) ram_ctrl (
 .s_axi_aclk(clk_i),                // input wire s_aclk
 .s_axi_aresetn(rst_ni),           // input wire s_aresetn
 .s_axi_awid(slave.aw_id),
 .s_axi_awaddr(slave.aw_addr),
 .s_axi_awlen(slave.aw_len),
 .s_axi_awsize(slave.aw_size),
 .s_axi_awburst(slave.aw_burst),
 .s_axi_awlock(slave.aw_lock),
 .s_axi_awcache(slave.aw_cache),
 .s_axi_awprot(slave.aw_prot),
 .s_axi_awregion(slave.aw_region),
 .s_axi_awqos(slave.aw_qos),
 .s_axi_awuser(slave.aw_user),
 .s_axi_awvalid(slave.aw_valid),
 .s_axi_awready(slave.aw_ready),
 .s_axi_wdata(slave.w_data),
 .s_axi_wstrb(slave.w_strb),
 .s_axi_wlast(slave.w_last),
 .s_axi_wuser(slave.w_user),
 .s_axi_wvalid(slave.w_valid),
 .s_axi_wready(slave.w_ready),
 .s_axi_bid(slave.b_id),
 .s_axi_bresp(slave.b_resp),
 .s_axi_buser(slave.b_user),
 .s_axi_bvalid(slave.b_valid),
 .s_axi_bready(slave.b_ready),
 .s_axi_arid(slave.ar_id),
 .s_axi_araddr(slave.ar_addr),
 .s_axi_arlen(slave.ar_len),
 .s_axi_arsize(slave.ar_size),
 .s_axi_arburst(slave.ar_burst),
 .s_axi_arlock(slave.ar_lock),
 .s_axi_arcache(slave.ar_cache),
 .s_axi_arprot(slave.ar_prot),
 .s_axi_arregion(slave.ar_region),
 .s_axi_arqos(slave.ar_qos),
 .s_axi_aruser(slave.ar_user),
 .s_axi_arvalid(slave.ar_valid),
 .s_axi_arready(slave.ar_ready),
 .s_axi_rid(slave.r_id),
 .s_axi_rdata(slave.r_data),
 .s_axi_rresp(slave.r_resp),
 .s_axi_rlast(slave.r_last),
 .s_axi_ruser(slave.r_user),
 .s_axi_rvalid(slave.r_valid),
 .s_axi_rready(slave.r_ready),
 .bram_rst_a(bram_rst_a),        // output wire bram_rst_a
 .bram_clk_a(bram_clk_a),        // output wire bram_clk_a
 .bram_en_a(bram_en_a),          // output wire bram_en_a
 .bram_we_a(bram_we_a),          // output wire [7 : 0] bram_we_a
 .bram_addr_a(bram_addr_a),      // output wire [12 : 0] bram_addr_a
 .bram_wrdata_a(bram_wrdata_a),  // output wire [63 : 0] bram_wrdata_a
 .bram_rddata_a(bram_rddata_a)  // input wire [63 : 0] bram_rddata_a
);
`else
axi_bram_ctrl_boot ram_ctrl (
  .s_axi_aclk(clk_i),                // input wire s_aclk
  .s_axi_aresetn(rst_ni),           // input wire s_aresetn
  .s_axi_awid(slave.aw_id),
  .s_axi_awaddr(slave.aw_addr),
  .s_axi_awlen(slave.aw_len),
  .s_axi_awsize(slave.aw_size),
  .s_axi_awburst(slave.aw_burst),
  .s_axi_awlock(slave.aw_lock),
  .s_axi_awcache(slave.aw_cache),
  .s_axi_awprot(slave.aw_prot),
//  .s_axi_awregion(slave.aw_region),
//  .s_axi_awqos(slave.aw_qos),
//  .s_axi_awuser(slave.aw_user),
  .s_axi_awvalid(slave.aw_valid),
  .s_axi_awready(slave.aw_ready),
  .s_axi_wdata(slave.w_data),
  .s_axi_wstrb(slave.w_strb),
  .s_axi_wlast(slave.w_last),
//  .s_axi_wuser(slave.w_user),
  .s_axi_wvalid(slave.w_valid),
  .s_axi_wready(slave.w_ready),
  .s_axi_bid(slave.b_id),
  .s_axi_bresp(slave.b_resp),
//  .s_axi_buser(slave.b_user),
  .s_axi_bvalid(slave.b_valid),
  .s_axi_bready(slave.b_ready),
  .s_axi_arid(slave.ar_id),
  .s_axi_araddr(slave.ar_addr),
  .s_axi_arlen(slave.ar_len),
  .s_axi_arsize(slave.ar_size),
  .s_axi_arburst(slave.ar_burst),
  .s_axi_arlock(slave.ar_lock),
  .s_axi_arcache(slave.ar_cache),
  .s_axi_arprot(slave.ar_prot),
//  .s_axi_arregion(slave.ar_region),
//  .s_axi_arqos(slave.ar_qos),
//  .s_axi_aruser(slave.ar_user),
  .s_axi_arvalid(slave.ar_valid),
  .s_axi_arready(slave.ar_ready),
  .s_axi_rid(slave.r_id),
  .s_axi_rdata(slave.r_data),
  .s_axi_rresp(slave.r_resp),
  .s_axi_rlast(slave.r_last),
//  .s_axi_ruser(slave.r_user),
  .s_axi_rvalid(slave.r_valid),
  .s_axi_rready(slave.r_ready),
  .bram_rst_a(bram_rst_a),        // output wire bram_rst_a
  .bram_clk_a(bram_clk_a),        // output wire bram_clk_a
  .bram_en_a(bram_en_a),          // output wire bram_en_a
  .bram_we_a(bram_we_a),          // output wire [7 : 0] bram_we_a
  .bram_addr_a(bram_addr_a),      // output wire [12 : 0] bram_addr_a
  .bram_wrdata_a(bram_wrdata_a),  // output wire [63 : 0] bram_wrdata_a
  .bram_rddata_a(bram_rddata_a)  // input wire [63 : 0] bram_rddata_a
);
`endif
`endif
    
endmodule
