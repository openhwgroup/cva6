module if_converter  #(
    ID_WIDTH = 10,               // id width
    ADDR_WIDTH = 64,             // address width
    DATA_WIDTH = 64,             // width of data
    USER_WIDTH = 6              // width of user field, must > 0, let synthesizer trim it if not in use
    )
   (
                      nasti_channel.slave incoming_nasti,
                      AXI_BUS.Master outgoing_if
                       );

slave_adapter  #(
    .ID_WIDTH(ID_WIDTH),                 // id width
    .ADDR_WIDTH(ADDR_WIDTH),             // address width
    .DATA_WIDTH(DATA_WIDTH),             // width of data
    .USER_WIDTH(USER_WIDTH)              // width of user field, must > 0, let synthesizer trim it if not in use
    )
 sadapt(
  .s_axi_awid(incoming_nasti.aw_id),
  .s_axi_awaddr(incoming_nasti.aw_addr),
  .s_axi_awlen(incoming_nasti.aw_len),
  .s_axi_awsize(incoming_nasti.aw_size),
  .s_axi_awburst(incoming_nasti.aw_burst),
  .s_axi_awlock(incoming_nasti.aw_lock),
  .s_axi_awcache(incoming_nasti.aw_cache),
  .s_axi_awprot(incoming_nasti.aw_prot),
  .s_axi_awregion(incoming_nasti.aw_region),
  .s_axi_awqos(incoming_nasti.aw_qos),
  .s_axi_awuser(incoming_nasti.aw_user),
  .s_axi_awvalid(incoming_nasti.aw_valid),
  .s_axi_awready(incoming_nasti.aw_ready),
  .s_axi_wdata(incoming_nasti.w_data),
  .s_axi_wstrb(incoming_nasti.w_strb),
  .s_axi_wlast(incoming_nasti.w_last),
  .s_axi_wuser(incoming_nasti.w_user),
  .s_axi_wvalid(incoming_nasti.w_valid),
  .s_axi_wready(incoming_nasti.w_ready),
  .s_axi_bid(incoming_nasti.b_id),
  .s_axi_bresp(incoming_nasti.b_resp),
  .s_axi_buser(incoming_nasti.b_user),
  .s_axi_bvalid(incoming_nasti.b_valid),
  .s_axi_bready(incoming_nasti.b_ready),
  .s_axi_arid(incoming_nasti.ar_id),
  .s_axi_araddr(incoming_nasti.ar_addr),
  .s_axi_arlen(incoming_nasti.ar_len),
  .s_axi_arsize(incoming_nasti.ar_size),
  .s_axi_arburst(incoming_nasti.ar_burst),
  .s_axi_arlock(incoming_nasti.ar_lock),
  .s_axi_arcache(incoming_nasti.ar_cache),
  .s_axi_arprot(incoming_nasti.ar_prot),
  .s_axi_arregion(incoming_nasti.ar_region),
  .s_axi_arqos(incoming_nasti.ar_qos),
  .s_axi_aruser(incoming_nasti.ar_user),
  .s_axi_arvalid(incoming_nasti.ar_valid),
  .s_axi_arready(incoming_nasti.ar_ready),
  .s_axi_rid(incoming_nasti.r_id),
  .s_axi_rdata(incoming_nasti.r_data),
  .s_axi_rresp(incoming_nasti.r_resp),
  .s_axi_rlast(incoming_nasti.r_last),
  .s_axi_ruser(incoming_nasti.r_user),
  .s_axi_rvalid(incoming_nasti.r_valid),
  .s_axi_rready(incoming_nasti.r_ready),
      .m_axi_awid           ( outgoing_if.aw_id      ),
      .m_axi_awaddr         ( outgoing_if.aw_addr    ),
      .m_axi_awlen          ( outgoing_if.aw_len     ),
      .m_axi_awsize         ( outgoing_if.aw_size    ),
      .m_axi_awburst        ( outgoing_if.aw_burst   ),
      .m_axi_awlock         ( outgoing_if.aw_lock    ),
      .m_axi_awcache        ( outgoing_if.aw_cache   ),
      .m_axi_awprot         ( outgoing_if.aw_prot    ),
      .m_axi_awqos          ( outgoing_if.aw_qos     ),
      .m_axi_awuser         ( outgoing_if.aw_user    ),
      .m_axi_awregion       ( outgoing_if.aw_region  ),
      .m_axi_awvalid        ( outgoing_if.aw_valid   ),
      .m_axi_awready        ( outgoing_if.aw_ready   ),
      .m_axi_wdata          ( outgoing_if.w_data     ),
      .m_axi_wstrb          ( outgoing_if.w_strb     ),
      .m_axi_wlast          ( outgoing_if.w_last     ),
      .m_axi_wvalid         ( outgoing_if.w_valid    ),
      .m_axi_wready         ( outgoing_if.w_ready    ),
      .m_axi_bid            ( outgoing_if.b_id       ),
      .m_axi_bresp          ( outgoing_if.b_resp     ),
      .m_axi_bvalid         ( outgoing_if.b_valid    ),
      .m_axi_bready         ( outgoing_if.b_ready    ),
      .m_axi_arid           ( outgoing_if.ar_id      ),
      .m_axi_araddr         ( outgoing_if.ar_addr    ),
      .m_axi_arlen          ( outgoing_if.ar_len     ),
      .m_axi_arsize         ( outgoing_if.ar_size    ),
      .m_axi_arburst        ( outgoing_if.ar_burst   ),
      .m_axi_arlock         ( outgoing_if.ar_lock    ),
      .m_axi_arcache        ( outgoing_if.ar_cache   ),
      .m_axi_arprot         ( outgoing_if.ar_prot    ),
      .m_axi_arqos          ( outgoing_if.ar_qos     ),
      .m_axi_aruser         ( outgoing_if.ar_user    ),
      .m_axi_arregion       ( outgoing_if.ar_region  ),
      .m_axi_arvalid        ( outgoing_if.ar_valid   ),
      .m_axi_arready        ( outgoing_if.ar_ready   ),
      .m_axi_rid            ( outgoing_if.r_id       ),
      .m_axi_rdata          ( outgoing_if.r_data     ),
      .m_axi_rresp          ( outgoing_if.r_resp     ),
      .m_axi_rlast          ( outgoing_if.r_last     ),
      .m_axi_rvalid         ( outgoing_if.r_valid    ),
      .m_axi_rready         ( outgoing_if.r_ready    )
                      );
   
endmodule // if_converter
