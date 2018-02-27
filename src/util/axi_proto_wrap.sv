module axi_proto_wrap  #(
    ID_WIDTH = 4,               // id width
    ADDR_WIDTH = 64,             // address width
    DATA_WIDTH = 64,             // width of data
    USER_WIDTH = 1               // width of user field, must > 0, let synthesizer trim it if not in use
    )
(
AXI_BUS.Slave proto_if,
input clk, aresetn,
output pc_asserted,
output [96 : 0] pc_status
);

axi_protocol_checker_0 pc1 (
  .pc_status(pc_status),              // output wire [96 : 0] pc_status
  .pc_asserted(pc_asserted),          // output wire pc_asserted
  .system_resetn(aresetn),            // input wire system_resetn
  .aclk(clk),                         // input wire aclk
  .aresetn(aresetn),                  // input wire aresetn
  .pc_axi_awid(proto_if.aw_id),
  .pc_axi_awaddr(proto_if.aw_addr),
  .pc_axi_awlen(proto_if.aw_len),
  .pc_axi_awsize(proto_if.aw_size),
  .pc_axi_awburst(proto_if.aw_burst),
  .pc_axi_awlock(proto_if.aw_lock),
  .pc_axi_awcache(proto_if.aw_cache),
  .pc_axi_awprot(proto_if.aw_prot),
  .pc_axi_awregion(proto_if.aw_region),
  .pc_axi_awqos(proto_if.aw_qos),
  .pc_axi_awuser(proto_if.aw_user),
  .pc_axi_awvalid(proto_if.aw_valid),
  .pc_axi_awready(proto_if.aw_ready),
  .pc_axi_wdata(proto_if.w_data),
  .pc_axi_wstrb(proto_if.w_strb),
  .pc_axi_wlast(proto_if.w_last),
  .pc_axi_wuser(proto_if.w_user),
  .pc_axi_wvalid(proto_if.w_valid),
  .pc_axi_wready(proto_if.w_ready),
  .pc_axi_bid(proto_if.b_id),
  .pc_axi_bresp(proto_if.b_resp),
  .pc_axi_buser(proto_if.b_user),
  .pc_axi_bvalid(proto_if.b_valid),
  .pc_axi_bready(proto_if.b_ready),
  .pc_axi_arid(proto_if.ar_id),
  .pc_axi_araddr(proto_if.ar_addr),
  .pc_axi_arlen(proto_if.ar_len),
  .pc_axi_arsize(proto_if.ar_size),
  .pc_axi_arburst(proto_if.ar_burst),
  .pc_axi_arlock(proto_if.ar_lock),
  .pc_axi_arcache(proto_if.ar_cache),
  .pc_axi_arprot(proto_if.ar_prot),
  .pc_axi_arregion(proto_if.ar_region),
  .pc_axi_arqos(proto_if.ar_qos),
  .pc_axi_aruser(proto_if.ar_user),
  .pc_axi_arvalid(proto_if.ar_valid),
  .pc_axi_arready(proto_if.ar_ready),
  .pc_axi_rid(proto_if.r_id),
  .pc_axi_rdata(proto_if.r_data),
  .pc_axi_rresp(proto_if.r_resp),
  .pc_axi_rlast(proto_if.r_last),
  .pc_axi_ruser(proto_if.r_user),
  .pc_axi_rvalid(proto_if.r_valid),
  .pc_axi_rready(proto_if.r_ready)
);
   
endmodule // nasti_converter
