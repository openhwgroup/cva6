	cva6_intel_axi_bridge_0 #(
		.USE_PIPELINE              (INTEGER_VALUE_FOR_USE_PIPELINE),
		.USE_M0_AWID               (INTEGER_VALUE_FOR_USE_M0_AWID),
		.USE_M0_AWREGION           (INTEGER_VALUE_FOR_USE_M0_AWREGION),
		.USE_M0_AWLEN              (INTEGER_VALUE_FOR_USE_M0_AWLEN),
		.USE_M0_AWSIZE             (INTEGER_VALUE_FOR_USE_M0_AWSIZE),
		.USE_M0_AWBURST            (INTEGER_VALUE_FOR_USE_M0_AWBURST),
		.USE_M0_AWLOCK             (INTEGER_VALUE_FOR_USE_M0_AWLOCK),
		.USE_M0_AWCACHE            (INTEGER_VALUE_FOR_USE_M0_AWCACHE),
		.USE_M0_AWQOS              (INTEGER_VALUE_FOR_USE_M0_AWQOS),
		.USE_S0_AWREGION           (INTEGER_VALUE_FOR_USE_S0_AWREGION),
		.USE_S0_AWLOCK             (INTEGER_VALUE_FOR_USE_S0_AWLOCK),
		.USE_S0_AWCACHE            (INTEGER_VALUE_FOR_USE_S0_AWCACHE),
		.USE_S0_AWQOS              (INTEGER_VALUE_FOR_USE_S0_AWQOS),
		.USE_S0_AWPROT             (INTEGER_VALUE_FOR_USE_S0_AWPROT),
		.USE_M0_WSTRB              (INTEGER_VALUE_FOR_USE_M0_WSTRB),
		.USE_S0_WLAST              (INTEGER_VALUE_FOR_USE_S0_WLAST),
		.USE_M0_BID                (INTEGER_VALUE_FOR_USE_M0_BID),
		.USE_M0_BRESP              (INTEGER_VALUE_FOR_USE_M0_BRESP),
		.USE_S0_BRESP              (INTEGER_VALUE_FOR_USE_S0_BRESP),
		.USE_M0_ARID               (INTEGER_VALUE_FOR_USE_M0_ARID),
		.USE_M0_ARREGION           (INTEGER_VALUE_FOR_USE_M0_ARREGION),
		.USE_M0_ARLEN              (INTEGER_VALUE_FOR_USE_M0_ARLEN),
		.USE_M0_ARSIZE             (INTEGER_VALUE_FOR_USE_M0_ARSIZE),
		.USE_M0_ARBURST            (INTEGER_VALUE_FOR_USE_M0_ARBURST),
		.USE_M0_ARLOCK             (INTEGER_VALUE_FOR_USE_M0_ARLOCK),
		.USE_M0_ARCACHE            (INTEGER_VALUE_FOR_USE_M0_ARCACHE),
		.USE_M0_ARQOS              (INTEGER_VALUE_FOR_USE_M0_ARQOS),
		.USE_S0_ARREGION           (INTEGER_VALUE_FOR_USE_S0_ARREGION),
		.USE_S0_ARLOCK             (INTEGER_VALUE_FOR_USE_S0_ARLOCK),
		.USE_S0_ARCACHE            (INTEGER_VALUE_FOR_USE_S0_ARCACHE),
		.USE_S0_ARQOS              (INTEGER_VALUE_FOR_USE_S0_ARQOS),
		.USE_S0_ARPROT             (INTEGER_VALUE_FOR_USE_S0_ARPROT),
		.USE_M0_RID                (INTEGER_VALUE_FOR_USE_M0_RID),
		.USE_M0_RRESP              (INTEGER_VALUE_FOR_USE_M0_RRESP),
		.USE_M0_RLAST              (INTEGER_VALUE_FOR_USE_M0_RLAST),
		.USE_S0_RRESP              (INTEGER_VALUE_FOR_USE_S0_RRESP),
		.M0_ID_WIDTH               (INTEGER_VALUE_FOR_M0_ID_WIDTH),
		.S0_ID_WIDTH               (INTEGER_VALUE_FOR_S0_ID_WIDTH),
		.DATA_WIDTH                (INTEGER_VALUE_FOR_DATA_WIDTH),
		.WRITE_ADDR_USER_WIDTH     (INTEGER_VALUE_FOR_WRITE_ADDR_USER_WIDTH),
		.READ_ADDR_USER_WIDTH      (INTEGER_VALUE_FOR_READ_ADDR_USER_WIDTH),
		.WRITE_DATA_USER_WIDTH     (INTEGER_VALUE_FOR_WRITE_DATA_USER_WIDTH),
		.WRITE_RESP_USER_WIDTH     (INTEGER_VALUE_FOR_WRITE_RESP_USER_WIDTH),
		.READ_DATA_USER_WIDTH      (INTEGER_VALUE_FOR_READ_DATA_USER_WIDTH),
		.ADDR_WIDTH                (INTEGER_VALUE_FOR_ADDR_WIDTH),
		.USE_S0_AWUSER             (INTEGER_VALUE_FOR_USE_S0_AWUSER),
		.USE_S0_ARUSER             (INTEGER_VALUE_FOR_USE_S0_ARUSER),
		.USE_S0_WUSER              (INTEGER_VALUE_FOR_USE_S0_WUSER),
		.USE_S0_RUSER              (INTEGER_VALUE_FOR_USE_S0_RUSER),
		.USE_S0_BUSER              (INTEGER_VALUE_FOR_USE_S0_BUSER),
		.USE_M0_AWUSER             (INTEGER_VALUE_FOR_USE_M0_AWUSER),
		.USE_M0_ARUSER             (INTEGER_VALUE_FOR_USE_M0_ARUSER),
		.USE_M0_WUSER              (INTEGER_VALUE_FOR_USE_M0_WUSER),
		.USE_M0_RUSER              (INTEGER_VALUE_FOR_USE_M0_RUSER),
		.USE_M0_BUSER              (INTEGER_VALUE_FOR_USE_M0_BUSER),
		.AXI_VERSION               (STRING_VALUE_FOR_AXI_VERSION),
		.ACE_LITE_SUPPORT          (INTEGER_VALUE_FOR_ACE_LITE_SUPPORT),
		.SYNC_RESET                (INTEGER_VALUE_FOR_SYNC_RESET),
		.BACKPRESSURE_DURING_RESET (INTEGER_VALUE_FOR_BACKPRESSURE_DURING_RESET)
	) u0 (
		.aclk       (_connected_to_aclk_),       //   input,   width = 1,       clk.clk
		.aresetn    (_connected_to_aresetn_),    //   input,   width = 1, clk_reset.reset_n
		.s0_awid    (_connected_to_s0_awid_),    //   input,   width = 8,        s0.awid
		.s0_awaddr  (_connected_to_s0_awaddr_),  //   input,  width = 64,          .awaddr
		.s0_awlen   (_connected_to_s0_awlen_),   //   input,   width = 8,          .awlen
		.s0_awsize  (_connected_to_s0_awsize_),  //   input,   width = 3,          .awsize
		.s0_awburst (_connected_to_s0_awburst_), //   input,   width = 2,          .awburst
		.s0_awlock  (_connected_to_s0_awlock_),  //   input,   width = 1,          .awlock
		.s0_awcache (_connected_to_s0_awcache_), //   input,   width = 4,          .awcache
		.s0_awprot  (_connected_to_s0_awprot_),  //   input,   width = 3,          .awprot
		.s0_awvalid (_connected_to_s0_awvalid_), //   input,   width = 1,          .awvalid
		.s0_awready (_connected_to_s0_awready_), //  output,   width = 1,          .awready
		.s0_wdata   (_connected_to_s0_wdata_),   //   input,  width = 64,          .wdata
		.s0_wstrb   (_connected_to_s0_wstrb_),   //   input,   width = 8,          .wstrb
		.s0_wlast   (_connected_to_s0_wlast_),   //   input,   width = 1,          .wlast
		.s0_wvalid  (_connected_to_s0_wvalid_),  //   input,   width = 1,          .wvalid
		.s0_wready  (_connected_to_s0_wready_),  //  output,   width = 1,          .wready
		.s0_bid     (_connected_to_s0_bid_),     //  output,   width = 8,          .bid
		.s0_bresp   (_connected_to_s0_bresp_),   //  output,   width = 2,          .bresp
		.s0_bvalid  (_connected_to_s0_bvalid_),  //  output,   width = 1,          .bvalid
		.s0_bready  (_connected_to_s0_bready_),  //   input,   width = 1,          .bready
		.s0_arid    (_connected_to_s0_arid_),    //   input,   width = 8,          .arid
		.s0_araddr  (_connected_to_s0_araddr_),  //   input,  width = 64,          .araddr
		.s0_arlen   (_connected_to_s0_arlen_),   //   input,   width = 8,          .arlen
		.s0_arsize  (_connected_to_s0_arsize_),  //   input,   width = 3,          .arsize
		.s0_arburst (_connected_to_s0_arburst_), //   input,   width = 2,          .arburst
		.s0_arlock  (_connected_to_s0_arlock_),  //   input,   width = 1,          .arlock
		.s0_arcache (_connected_to_s0_arcache_), //   input,   width = 4,          .arcache
		.s0_arprot  (_connected_to_s0_arprot_),  //   input,   width = 3,          .arprot
		.s0_arvalid (_connected_to_s0_arvalid_), //   input,   width = 1,          .arvalid
		.s0_arready (_connected_to_s0_arready_), //  output,   width = 1,          .arready
		.s0_rid     (_connected_to_s0_rid_),     //  output,   width = 8,          .rid
		.s0_rdata   (_connected_to_s0_rdata_),   //  output,  width = 64,          .rdata
		.s0_rresp   (_connected_to_s0_rresp_),   //  output,   width = 2,          .rresp
		.s0_rlast   (_connected_to_s0_rlast_),   //  output,   width = 1,          .rlast
		.s0_rvalid  (_connected_to_s0_rvalid_),  //  output,   width = 1,          .rvalid
		.s0_rready  (_connected_to_s0_rready_),  //   input,   width = 1,          .rready
		.m0_awid    (_connected_to_m0_awid_),    //  output,   width = 8,        m0.awid
		.m0_awaddr  (_connected_to_m0_awaddr_),  //  output,  width = 64,          .awaddr
		.m0_awlen   (_connected_to_m0_awlen_),   //  output,   width = 8,          .awlen
		.m0_awsize  (_connected_to_m0_awsize_),  //  output,   width = 3,          .awsize
		.m0_awburst (_connected_to_m0_awburst_), //  output,   width = 2,          .awburst
		.m0_awlock  (_connected_to_m0_awlock_),  //  output,   width = 1,          .awlock
		.m0_awcache (_connected_to_m0_awcache_), //  output,   width = 4,          .awcache
		.m0_awprot  (_connected_to_m0_awprot_),  //  output,   width = 3,          .awprot
		.m0_awvalid (_connected_to_m0_awvalid_), //  output,   width = 1,          .awvalid
		.m0_awready (_connected_to_m0_awready_), //   input,   width = 1,          .awready
		.m0_wdata   (_connected_to_m0_wdata_),   //  output,  width = 64,          .wdata
		.m0_wstrb   (_connected_to_m0_wstrb_),   //  output,   width = 8,          .wstrb
		.m0_wlast   (_connected_to_m0_wlast_),   //  output,   width = 1,          .wlast
		.m0_wvalid  (_connected_to_m0_wvalid_),  //  output,   width = 1,          .wvalid
		.m0_wready  (_connected_to_m0_wready_),  //   input,   width = 1,          .wready
		.m0_bid     (_connected_to_m0_bid_),     //   input,   width = 8,          .bid
		.m0_bresp   (_connected_to_m0_bresp_),   //   input,   width = 2,          .bresp
		.m0_bvalid  (_connected_to_m0_bvalid_),  //   input,   width = 1,          .bvalid
		.m0_bready  (_connected_to_m0_bready_),  //  output,   width = 1,          .bready
		.m0_arid    (_connected_to_m0_arid_),    //  output,   width = 8,          .arid
		.m0_araddr  (_connected_to_m0_araddr_),  //  output,  width = 64,          .araddr
		.m0_arlen   (_connected_to_m0_arlen_),   //  output,   width = 8,          .arlen
		.m0_arsize  (_connected_to_m0_arsize_),  //  output,   width = 3,          .arsize
		.m0_arburst (_connected_to_m0_arburst_), //  output,   width = 2,          .arburst
		.m0_arlock  (_connected_to_m0_arlock_),  //  output,   width = 1,          .arlock
		.m0_arcache (_connected_to_m0_arcache_), //  output,   width = 4,          .arcache
		.m0_arprot  (_connected_to_m0_arprot_),  //  output,   width = 3,          .arprot
		.m0_arvalid (_connected_to_m0_arvalid_), //  output,   width = 1,          .arvalid
		.m0_arready (_connected_to_m0_arready_), //   input,   width = 1,          .arready
		.m0_rid     (_connected_to_m0_rid_),     //   input,   width = 8,          .rid
		.m0_rdata   (_connected_to_m0_rdata_),   //   input,  width = 64,          .rdata
		.m0_rresp   (_connected_to_m0_rresp_),   //   input,   width = 2,          .rresp
		.m0_rlast   (_connected_to_m0_rlast_),   //   input,   width = 1,          .rlast
		.m0_rvalid  (_connected_to_m0_rvalid_),  //   input,   width = 1,          .rvalid
		.m0_rready  (_connected_to_m0_rready_)   //  output,   width = 1,          .rready
	);

