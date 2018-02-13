module slave_adaptor
  #(
    ID_WIDTH = 10,               // id width
    ADDR_WIDTH = 64,             // address width
    DATA_WIDTH = 64,             // width of data
    USER_WIDTH = 6,              // width of user field, must > 0, let synthesizer trim it if not in use
    LITE_MODE = 0                // whether work in Lite mode
    )
(
  input [ID_WIDTH-1:0]     s_axi_awid,
  input [ADDR_WIDTH-1:0]   s_axi_awaddr,
  input [7:0]              s_axi_awlen,
  input [2:0]              s_axi_awsize,
  input [1:0]              s_axi_awburst,
  input                    s_axi_awlock,
  input [3:0]              s_axi_awcache,
  input [2:0]              s_axi_awprot,
  input [3:0]              s_axi_awregion,
  input [3:0]              s_axi_awqos,
  input [USER_WIDTH-1:0]   s_axi_awuser,
  input                    s_axi_awvalid,
  output                   s_axi_awready,
  input [DATA_WIDTH-1:0]   s_axi_wdata,
  input [DATA_WIDTH/8-1:0] s_axi_wstrb,
  input                    s_axi_wlast,
  input [USER_WIDTH-1:0]   s_axi_wuser,
  input                    s_axi_wvalid,
  output                   s_axi_wready,
  output [ID_WIDTH-1:0]    s_axi_bid,
  output [1:0]             s_axi_bresp,
  output [USER_WIDTH-1:0]  s_axi_buser,
  output                   s_axi_bvalid,
  input                    s_axi_bready,
  input [ID_WIDTH-1:0]     s_axi_arid,
  input [ADDR_WIDTH-1:0]   s_axi_araddr,
  input [7:0]              s_axi_arlen,
  input [2:0]              s_axi_arsize,
  input [1:0]              s_axi_arburst,
  input                    s_axi_arlock,
  input [3:0]              s_axi_arcache,
  input [2:0]              s_axi_arprot,
  input [3:0]              s_axi_arregion,
  input [3:0]              s_axi_arqos,
  input [USER_WIDTH-1:0]   s_axi_aruser,
  input                    s_axi_arvalid,
  output                   s_axi_arready,
  output [ID_WIDTH-1:0]    s_axi_rid,
  output [DATA_WIDTH-1:0]  s_axi_rdata,
  output [1:0]             s_axi_rresp,
  output                   s_axi_rlast,
  output [USER_WIDTH-1:0]  s_axi_ruser,
  output                   s_axi_rvalid,
  input                    s_axi_rready,

  output [ID_WIDTH-1:0]    m_axi_awid,
  output [ADDR_WIDTH-1:0]  m_axi_awaddr,
  output [7:0]             m_axi_awlen,
  output [2:0]             m_axi_awsize,
  output [1:0]             m_axi_awburst,
  output [0:0]             m_axi_awlock,
  output [3:0]             m_axi_awcache,
  output [2:0]             m_axi_awprot,
  output [3:0]             m_axi_awregion,
  output [3:0]             m_axi_awqos,
  output [USER_WIDTH-1:0]  m_axi_awuser,
  output                   m_axi_awvalid,
  input                    m_axi_awready,
  output [DATA_WIDTH-1:0]  m_axi_wdata,
  output [7:0]             m_axi_wstrb,
  output                   m_axi_wlast,
  output                   m_axi_wvalid,
  input                    m_axi_wready,
  input [ID_WIDTH-1:0]     m_axi_bid,
  input [1:0]              m_axi_bresp,
  input                    m_axi_bvalid,
  output                   m_axi_bready,
  output [ID_WIDTH-1:0]    m_axi_arid,
  output [ADDR_WIDTH-1:0]  m_axi_araddr,
  output [7:0]             m_axi_arlen,
  output [2:0]             m_axi_arsize,
  output [1:0]             m_axi_arburst,
  output [0:0]             m_axi_arlock,
  output [3:0]             m_axi_arcache,
  output [2:0]             m_axi_arprot,
  output [3:0]             m_axi_arregion,
  output [3:0]             m_axi_arqos,
  output [USER_WIDTH-1:0]  m_axi_aruser,
  output                   m_axi_arvalid,
  input                    m_axi_arready,
  input [ID_WIDTH-1:0]     m_axi_rid,
  input [DATA_WIDTH-1:0]   m_axi_rdata,
  input [1:0]              m_axi_rresp,
  input                    m_axi_rlast,
  input                    m_axi_rvalid,
  output                   m_axi_rready);
   
assign s_axi_awready = m_axi_awready;
assign s_axi_wready = m_axi_wready;
assign s_axi_bid = m_axi_bid;
assign s_axi_bresp = m_axi_bresp;
assign s_axi_bvalid = m_axi_bvalid;
assign s_axi_arready = m_axi_arready;
assign s_axi_rid = m_axi_rid;
assign s_axi_rdata = m_axi_rdata;
assign s_axi_rresp = m_axi_rresp;
assign s_axi_rlast = m_axi_rlast;
assign s_axi_rvalid = m_axi_rvalid;
assign m_axi_awid = s_axi_awid;
assign m_axi_awaddr = s_axi_awaddr;
assign m_axi_awlen = s_axi_awlen;
assign m_axi_awsize = s_axi_awsize;
assign m_axi_awburst = s_axi_awburst;
assign m_axi_awlock = s_axi_awlock;
assign m_axi_awcache = s_axi_awcache;
assign m_axi_awprot = s_axi_awprot;
assign m_axi_awregion = s_axi_awregion;
assign m_axi_awqos = s_axi_awqos;
assign m_axi_awuser = s_axi_awuser;
assign m_axi_awvalid = s_axi_awvalid;
assign m_axi_wdata = s_axi_wdata;
assign m_axi_wstrb = s_axi_wstrb;
assign m_axi_wlast = s_axi_wlast;
assign m_axi_wvalid = s_axi_wvalid;
assign m_axi_bready = s_axi_bready;
assign m_axi_arid = s_axi_arid;
assign m_axi_araddr = s_axi_araddr;
assign m_axi_arlen = s_axi_arlen;
assign m_axi_arsize = s_axi_arsize;
assign m_axi_arburst = s_axi_arburst;
assign m_axi_arlock = s_axi_arlock;
assign m_axi_arcache = s_axi_arcache;
assign m_axi_arprot = s_axi_arprot;
assign m_axi_arregion = s_axi_arregion;
assign m_axi_arqos = s_axi_arqos;
assign m_axi_aruser = s_axi_aruser;
assign m_axi_arvalid = s_axi_arvalid;
assign m_axi_rready = s_axi_rready;
   
endmodule
