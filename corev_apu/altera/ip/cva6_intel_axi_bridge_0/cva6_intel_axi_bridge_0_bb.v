module cva6_intel_axi_bridge_0 #(
		parameter USE_PIPELINE              = 1,
		parameter USE_M0_AWID               = 1,
		parameter USE_M0_AWREGION           = 0,
		parameter USE_M0_AWLEN              = 1,
		parameter USE_M0_AWSIZE             = 1,
		parameter USE_M0_AWBURST            = 1,
		parameter USE_M0_AWLOCK             = 1,
		parameter USE_M0_AWCACHE            = 1,
		parameter USE_M0_AWQOS              = 0,
		parameter USE_S0_AWREGION           = 0,
		parameter USE_S0_AWLOCK             = 1,
		parameter USE_S0_AWCACHE            = 1,
		parameter USE_S0_AWQOS              = 0,
		parameter USE_S0_AWPROT             = 1,
		parameter USE_M0_WSTRB              = 1,
		parameter USE_S0_WLAST              = 1,
		parameter USE_M0_BID                = 1,
		parameter USE_M0_BRESP              = 1,
		parameter USE_S0_BRESP              = 1,
		parameter USE_M0_ARID               = 1,
		parameter USE_M0_ARREGION           = 0,
		parameter USE_M0_ARLEN              = 1,
		parameter USE_M0_ARSIZE             = 1,
		parameter USE_M0_ARBURST            = 1,
		parameter USE_M0_ARLOCK             = 1,
		parameter USE_M0_ARCACHE            = 1,
		parameter USE_M0_ARQOS              = 0,
		parameter USE_S0_ARREGION           = 0,
		parameter USE_S0_ARLOCK             = 1,
		parameter USE_S0_ARCACHE            = 1,
		parameter USE_S0_ARQOS              = 0,
		parameter USE_S0_ARPROT             = 1,
		parameter USE_M0_RID                = 1,
		parameter USE_M0_RRESP              = 1,
		parameter USE_M0_RLAST              = 1,
		parameter USE_S0_RRESP              = 1,
		parameter M0_ID_WIDTH               = 8,
		parameter S0_ID_WIDTH               = 8,
		parameter DATA_WIDTH                = 64,
		parameter WRITE_ADDR_USER_WIDTH     = 32,
		parameter READ_ADDR_USER_WIDTH      = 32,
		parameter WRITE_DATA_USER_WIDTH     = 32,
		parameter WRITE_RESP_USER_WIDTH     = 32,
		parameter READ_DATA_USER_WIDTH      = 32,
		parameter ADDR_WIDTH                = 64,
		parameter USE_S0_AWUSER             = 0,
		parameter USE_S0_ARUSER             = 0,
		parameter USE_S0_WUSER              = 0,
		parameter USE_S0_RUSER              = 0,
		parameter USE_S0_BUSER              = 0,
		parameter USE_M0_AWUSER             = 0,
		parameter USE_M0_ARUSER             = 0,
		parameter USE_M0_WUSER              = 0,
		parameter USE_M0_RUSER              = 0,
		parameter USE_M0_BUSER              = 0,
		parameter AXI_VERSION               = "AXI4",
		parameter ACE_LITE_SUPPORT          = 0,
		parameter SYNC_RESET                = 0,
		parameter BACKPRESSURE_DURING_RESET = 0
	) (
		input  wire        aclk,       //       clk.clk
		input  wire        aresetn,    // clk_reset.reset_n
		input  wire [7:0]  s0_awid,    //        s0.awid
		input  wire [63:0] s0_awaddr,  //          .awaddr
		input  wire [7:0]  s0_awlen,   //          .awlen
		input  wire [2:0]  s0_awsize,  //          .awsize
		input  wire [1:0]  s0_awburst, //          .awburst
		input  wire [0:0]  s0_awlock,  //          .awlock
		input  wire [3:0]  s0_awcache, //          .awcache
		input  wire [2:0]  s0_awprot,  //          .awprot
		input  wire        s0_awvalid, //          .awvalid
		output wire        s0_awready, //          .awready
		input  wire [63:0] s0_wdata,   //          .wdata
		input  wire [7:0]  s0_wstrb,   //          .wstrb
		input  wire        s0_wlast,   //          .wlast
		input  wire        s0_wvalid,  //          .wvalid
		output wire        s0_wready,  //          .wready
		output wire [7:0]  s0_bid,     //          .bid
		output wire [1:0]  s0_bresp,   //          .bresp
		output wire        s0_bvalid,  //          .bvalid
		input  wire        s0_bready,  //          .bready
		input  wire [7:0]  s0_arid,    //          .arid
		input  wire [63:0] s0_araddr,  //          .araddr
		input  wire [7:0]  s0_arlen,   //          .arlen
		input  wire [2:0]  s0_arsize,  //          .arsize
		input  wire [1:0]  s0_arburst, //          .arburst
		input  wire [0:0]  s0_arlock,  //          .arlock
		input  wire [3:0]  s0_arcache, //          .arcache
		input  wire [2:0]  s0_arprot,  //          .arprot
		input  wire        s0_arvalid, //          .arvalid
		output wire        s0_arready, //          .arready
		output wire [7:0]  s0_rid,     //          .rid
		output wire [63:0] s0_rdata,   //          .rdata
		output wire [1:0]  s0_rresp,   //          .rresp
		output wire        s0_rlast,   //          .rlast
		output wire        s0_rvalid,  //          .rvalid
		input  wire        s0_rready,  //          .rready
		output wire [7:0]  m0_awid,    //        m0.awid
		output wire [63:0] m0_awaddr,  //          .awaddr
		output wire [7:0]  m0_awlen,   //          .awlen
		output wire [2:0]  m0_awsize,  //          .awsize
		output wire [1:0]  m0_awburst, //          .awburst
		output wire [0:0]  m0_awlock,  //          .awlock
		output wire [3:0]  m0_awcache, //          .awcache
		output wire [2:0]  m0_awprot,  //          .awprot
		output wire        m0_awvalid, //          .awvalid
		input  wire        m0_awready, //          .awready
		output wire [63:0] m0_wdata,   //          .wdata
		output wire [7:0]  m0_wstrb,   //          .wstrb
		output wire        m0_wlast,   //          .wlast
		output wire        m0_wvalid,  //          .wvalid
		input  wire        m0_wready,  //          .wready
		input  wire [7:0]  m0_bid,     //          .bid
		input  wire [1:0]  m0_bresp,   //          .bresp
		input  wire        m0_bvalid,  //          .bvalid
		output wire        m0_bready,  //          .bready
		output wire [7:0]  m0_arid,    //          .arid
		output wire [63:0] m0_araddr,  //          .araddr
		output wire [7:0]  m0_arlen,   //          .arlen
		output wire [2:0]  m0_arsize,  //          .arsize
		output wire [1:0]  m0_arburst, //          .arburst
		output wire [0:0]  m0_arlock,  //          .arlock
		output wire [3:0]  m0_arcache, //          .arcache
		output wire [2:0]  m0_arprot,  //          .arprot
		output wire        m0_arvalid, //          .arvalid
		input  wire        m0_arready, //          .arready
		input  wire [7:0]  m0_rid,     //          .rid
		input  wire [63:0] m0_rdata,   //          .rdata
		input  wire [1:0]  m0_rresp,   //          .rresp
		input  wire        m0_rlast,   //          .rlast
		input  wire        m0_rvalid,  //          .rvalid
		output wire        m0_rready   //          .rready
	);
endmodule

