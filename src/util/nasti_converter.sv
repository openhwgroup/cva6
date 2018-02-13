module nasti_converter  #(
    ID_WIDTH = 10,               // id width
    ADDR_WIDTH = 64,             // address width
    DATA_WIDTH = 64,             // width of data
    USER_WIDTH = 6               // width of user field, must > 0, let synthesizer trim it if not in use
    )
(
                      AXI_BUS.Slave incoming_if,
                      nasti_channel.master outgoing_nasti                       
                       );

slave_adapter
  #(
    .ID_WIDTH(ID_WIDTH),                 // id width
    .ADDR_WIDTH(ADDR_WIDTH),             // address width
    .DATA_WIDTH(DATA_WIDTH),             // width of data
    .USER_WIDTH(USER_WIDTH)              // width of user field, must > 0, let synthesizer trim it if not in use
    )
 sadapt(
  .s_axi_awid(incoming_if.aw_id),
  .s_axi_awaddr(incoming_if.aw_addr),
  .s_axi_awlen(incoming_if.aw_len),
  .s_axi_awsize(incoming_if.aw_size),
  .s_axi_awburst(incoming_if.aw_burst),
  .s_axi_awlock(incoming_if.aw_lock),
  .s_axi_awcache(incoming_if.aw_cache),
  .s_axi_awprot(incoming_if.aw_prot),
  .s_axi_awregion(incoming_if.aw_region),
  .s_axi_awqos(incoming_if.aw_qos),
  .s_axi_awuser(incoming_if.aw_user),
  .s_axi_awvalid(incoming_if.aw_valid),
  .s_axi_awready(incoming_if.aw_ready),
  .s_axi_wdata(incoming_if.w_data),
  .s_axi_wstrb(incoming_if.w_strb),
  .s_axi_wlast(incoming_if.w_last),
  .s_axi_wuser(incoming_if.w_user),
  .s_axi_wvalid(incoming_if.w_valid),
  .s_axi_wready(incoming_if.w_ready),
  .s_axi_bid(incoming_if.b_id),
  .s_axi_bresp(incoming_if.b_resp),
  .s_axi_buser(incoming_if.b_user),
  .s_axi_bvalid(incoming_if.b_valid),
  .s_axi_bready(incoming_if.b_ready),
  .s_axi_arid(incoming_if.ar_id),
  .s_axi_araddr(incoming_if.ar_addr),
  .s_axi_arlen(incoming_if.ar_len),
  .s_axi_arsize(incoming_if.ar_size),
  .s_axi_arburst(incoming_if.ar_burst),
  .s_axi_arlock(incoming_if.ar_lock),
  .s_axi_arcache(incoming_if.ar_cache),
  .s_axi_arprot(incoming_if.ar_prot),
  .s_axi_arregion(incoming_if.ar_region),
  .s_axi_arqos(incoming_if.ar_qos),
  .s_axi_aruser(incoming_if.ar_user),
  .s_axi_arvalid(incoming_if.ar_valid),
  .s_axi_arready(incoming_if.ar_ready),
  .s_axi_rid(incoming_if.r_id),
  .s_axi_rdata(incoming_if.r_data),
  .s_axi_rresp(incoming_if.r_resp),
  .s_axi_rlast(incoming_if.r_last),
  .s_axi_ruser(incoming_if.r_user),
  .s_axi_rvalid(incoming_if.r_valid),
  .s_axi_rready(incoming_if.r_ready),
      .m_axi_awid           ( outgoing_nasti.aw_id      ),
      .m_axi_awaddr         ( outgoing_nasti.aw_addr    ),
      .m_axi_awlen          ( outgoing_nasti.aw_len     ),
      .m_axi_awsize         ( outgoing_nasti.aw_size    ),
      .m_axi_awburst        ( outgoing_nasti.aw_burst   ),
      .m_axi_awlock         ( outgoing_nasti.aw_lock    ),
      .m_axi_awcache        ( outgoing_nasti.aw_cache   ),
      .m_axi_awprot         ( outgoing_nasti.aw_prot    ),
      .m_axi_awqos          ( outgoing_nasti.aw_qos     ),
      .m_axi_awuser         ( outgoing_nasti.aw_user    ),
      .m_axi_awregion       ( outgoing_nasti.aw_region  ),
      .m_axi_awvalid        ( outgoing_nasti.aw_valid   ),
      .m_axi_awready        ( outgoing_nasti.aw_ready   ),
      .m_axi_wdata          ( outgoing_nasti.w_data     ),
      .m_axi_wstrb          ( outgoing_nasti.w_strb     ),
      .m_axi_wlast          ( outgoing_nasti.w_last     ),
      .m_axi_wvalid         ( outgoing_nasti.w_valid    ),
      .m_axi_wready         ( outgoing_nasti.w_ready    ),
      .m_axi_bid            ( outgoing_nasti.b_id       ),
      .m_axi_bresp          ( outgoing_nasti.b_resp     ),
      .m_axi_bvalid         ( outgoing_nasti.b_valid    ),
      .m_axi_bready         ( outgoing_nasti.b_ready    ),
      .m_axi_arid           ( outgoing_nasti.ar_id      ),
      .m_axi_araddr         ( outgoing_nasti.ar_addr    ),
      .m_axi_arlen          ( outgoing_nasti.ar_len     ),
      .m_axi_arsize         ( outgoing_nasti.ar_size    ),
      .m_axi_arburst        ( outgoing_nasti.ar_burst   ),
      .m_axi_arlock         ( outgoing_nasti.ar_lock    ),
      .m_axi_arcache        ( outgoing_nasti.ar_cache   ),
      .m_axi_arprot         ( outgoing_nasti.ar_prot    ),
      .m_axi_arqos          ( outgoing_nasti.ar_qos     ),
      .m_axi_aruser         ( outgoing_nasti.ar_user    ),
      .m_axi_arregion       ( outgoing_nasti.ar_region  ),
      .m_axi_arvalid        ( outgoing_nasti.ar_valid   ),
      .m_axi_arready        ( outgoing_nasti.ar_ready   ),
      .m_axi_rid            ( outgoing_nasti.r_id       ),
      .m_axi_rdata          ( outgoing_nasti.r_data     ),
      .m_axi_rresp          ( outgoing_nasti.r_resp     ),
      .m_axi_rlast          ( outgoing_nasti.r_last     ),
      .m_axi_rvalid         ( outgoing_nasti.r_valid    ),
      .m_axi_rready         ( outgoing_nasti.r_ready    )
                      );
   
endmodule // nasti_converter
