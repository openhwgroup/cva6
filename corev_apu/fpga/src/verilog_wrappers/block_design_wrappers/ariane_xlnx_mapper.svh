`ifndef ARIANE_XLNX_MAPPER_SVH
`define ARIANE_XLNX_MAPPER_SVH

`define AXI_INTERFACE_MODULE_INPUT(name)    \
    /* AW Channel  */ \
    input wire [AXI_ID_WIDTH - 1 : 0] ``name``_awid, \
    input wire [AXI_ADDR_WIDTH - 1 : 0] ``name``_awaddr, \
    input wire [7:0] ``name``_awlen, \
    input wire [2:0] ``name``_awsize, \
    input wire [1:0] ``name``_awburst, \
    input wire ``name``_awlock, \
    input wire [3:0] ``name``_awcache, \
    input wire [2:0] ``name``_awprot, \
    input wire [3:0] ``name``_awqos, \
    input wire [5:0] ``name``_awatop, \
    input wire [3:0] ``name``_awregion, \
    input wire [AXI_USER_WIDTH-1:0] ``name``_awuser, \
    input wire ``name``_awvalid, \
    output wire  ``name``_awready, \
    /* W Channel */\
    input wire [AXI_DATA_WIDTH - 1 : 0] ``name``_wdata, \
    input wire [AXI_DATA_WIDTH/8 - 1 : 0] ``name``_wstrb, \
    input wire ``name``_wlast, \
    input wire [AXI_USER_WIDTH-1:0] ``name``_wuser, \
    input wire ``name``_wvalid, \
    output wire ``name``_wready, \
    /* B Channel */\
    output wire [AXI_ID_WIDTH - 1 : 0] ``name``_bid, \
    output wire [1 : 0] ``name``_bresp, \
    output wire [AXI_USER_WIDTH-1:0] ``name``_buser, \
    output wire ``name``_bvalid, \
    input wire ``name``_bready, \
    /* AR Channel*/ \
    input wire [AXI_ID_WIDTH - 1 : 0] ``name``_arid, \
    input wire [AXI_ADDR_WIDTH - 1 : 0] ``name``_araddr, \
    input wire [7:0] ``name``_arlen, \
    input wire [2:0] ``name``_arsize, \
    input wire [1:0] ``name``_arburst, \
    input wire ``name``_arlock, \
    input wire [3:0] ``name``_arcache, \
    input wire [2:0] ``name``_arprot, \
    input wire [3:0] ``name``_arqos, \
    input wire [3:0] ``name``_arregion, \
    input wire [AXI_USER_WIDTH-1:0] ``name``_aruser, \
    input wire  ``name``_arvalid, \
    output wire  ``name``_arready, \
    /* R Channel */\
    output wire [AXI_DATA_WIDTH - 1 : 0] ``name``_rdata, \
    output wire [1 : 0] ``name``_rresp, \
    output wire ``name``_rlast, \
    output wire [AXI_ID_WIDTH - 1 : 0] ``name``_rid, \
    output wire [AXI_USER_WIDTH-1:0] ``name``_ruser, \
    output wire ``name``_rvalid, \
    input wire ``name``_rready

`define AXI_INTERFACE_MODULE_OUTPUT(name)    \
    /* AW Channel  */ \
    output wire [AXI_ID_WIDTH - 1 : 0] ``name``_awid, \
    output wire [AXI_ADDR_WIDTH - 1 : 0] ``name``_awaddr, \
    output wire [7:0] ``name``_awlen, \
    output wire [2:0] ``name``_awsize, \
    output wire [1:0] ``name``_awburst, \
    output wire ``name``_awlock, \
    output wire [3:0] ``name``_awcache, \
    output wire [2:0] ``name``_awprot, \
    output wire [3:0] ``name``_awqos, \
    output wire [5:0] ``name``_awatop, \
    output wire [3:0] ``name``_awregion, \
    output wire [AXI_USER_WIDTH-1:0] ``name``_awuser, \
    output wire  ``name``_awvalid, \
    input wire  ``name``_awready, \
    /* W Channel */\
    output wire [AXI_DATA_WIDTH - 1 : 0] ``name``_wdata, \
    output wire [AXI_DATA_WIDTH/8 - 1 : 0] ``name``_wstrb, \
    output wire ``name``_wlast, \
    output wire [AXI_USER_WIDTH-1:0] ``name``_wuser, \
    output wire ``name``_wvalid, \
    input wire ``name``_wready, \
    /* B Channel */\
    input wire [AXI_ID_WIDTH - 1 : 0] ``name``_bid, \
    input wire [1 : 0] ``name``_bresp, \
    input wire [AXI_USER_WIDTH-1:0] ``name``_buser, \
    input wire ``name``_bvalid, \
    output wire ``name``_bready, \
    /* AR Channel*/ \
    output wire [AXI_ID_WIDTH - 1 : 0] ``name``_arid, \
    output wire [AXI_ADDR_WIDTH - 1 : 0] ``name``_araddr, \
    output wire [7:0] ``name``_arlen, \
    output wire [2:0] ``name``_arsize, \
    output wire [1:0] ``name``_arburst, \
    output wire ``name``_arlock, \
    output wire [3:0] ``name``_arcache, \
    output wire [2:0] ``name``_arprot, \
    output wire [3:0] ``name``_arqos, \
    output wire [3:0] ``name``_arregion, \
    output wire [AXI_USER_WIDTH-1:0] ``name``_aruser, \
    output wire  ``name``_arvalid, \
    input wire [AXI_USER_WIDTH-1:0] ``name``_arready, \
    /* R Channel */\
    input wire [AXI_DATA_WIDTH - 1 : 0] ``name``_rdata, \
    input wire [1 : 0] ``name``_rresp, \
    input wire ``name``_rlast, \
    input wire [AXI_ID_WIDTH - 1 : 0] ``name``_rid, \
    input wire [AXI_USER_WIDTH-1:0] ``name``_ruser, \
    input wire ``name``_rvalid, \
    output wire ``name``_rready


`define AXI_INTERFACE_FORWARD(name)    \
    /* AW Channel  */ \
    .``name``_awid(``name``_awid), \
    .``name``_awaddr(``name``_awaddr), \
    .``name``_awlen(``name``_awlen), \
    .``name``_awsize(``name``_awsize), \
    .``name``_awburst(``name``_awburst), \
    .``name``_awlock(``name``_awlock), \
    .``name``_awcache(``name``_awcache), \
    .``name``_awprot(``name``_awprot), \
    .``name``_awqos(``name``_awqos), \
    .``name``_awatop(``name``_awatop), \
    .``name``_awregion(``name``_awregion), \
    .``name``_awuser(``name``_awuser), \
    .``name``_awvalid(``name``_awvalid), \
    .``name``_awready(``name``_awready), \
    /* W Channel */\
    .``name``_wdata(``name``_wdata), \
    .``name``_wstrb(``name``_wstrb), \
    .``name``_wlast(``name``_wlast), \
    .``name``_wuser(``name``_wuser), \
    .``name``_wvalid(``name``_wvalid), \
    .``name``_wready(``name``_wready), \
    /* B Channel */\
    .``name``_bid(``name``_bid), \
    .``name``_bresp(``name``_bresp), \
    .``name``_buser(``name``_buser), \
    .``name``_bvalid(``name``_bvalid), \
    .``name``_bready(``name``_bready), \
    /* AR Channel*/ \
    .``name``_arid(``name``_arid), \
    .``name``_araddr(``name``_araddr), \
    .``name``_arlen(``name``_arlen), \
    .``name``_arsize(``name``_arsize), \
    .``name``_arburst(``name``_arburst), \
    .``name``_arlock(``name``_arlock), \
    .``name``_arcache(``name``_arcache), \
    .``name``_arprot(``name``_arprot), \
    .``name``_arqos(``name``_arqos), \
    .``name``_arregion(``name``_arregion), \
    .``name``_aruser(``name``_aruser), \
    .``name``_arvalid(``name``_arvalid), \
    .``name``_arready(``name``_arready), \
    /* R Channel */\
    .``name``_rid(``name``_rid), \
    .``name``_rdata(``name``_rdata), \
    .``name``_rresp(``name``_rresp), \
    .``name``_rlast(``name``_rlast), \
    .``name``_ruser(``name``_ruser), \
    .``name``_rvalid(``name``_rvalid), \
    .``name``_rready(``name``_rready)

`define ASSIGN_XLNX_MASTER_FROM_XLNX_SLAVE(xlnx_slave_name, xlnx_master_name)    \
    /* AW Channel  */ \
    assign ``xlnx_master_name``_awid = ``xlnx_slave_name``_awid; \
    assign ``xlnx_master_name``_awaddr = ``xlnx_slave_name``_awaddr; \
    assign ``xlnx_master_name``_awlen = ``xlnx_slave_name``_awlen; \
    assign ``xlnx_master_name``_awsize = ``xlnx_slave_name``_awsize; \
    assign ``xlnx_master_name``_awburst = ``xlnx_slave_name``_awburst; \
    assign ``xlnx_master_name``_awlock = ``xlnx_slave_name``_awlock; \
    assign ``xlnx_master_name``_awcache = ``xlnx_slave_name``_awcache; \
    assign ``xlnx_master_name``_awprot = ``xlnx_slave_name``_awprot; \
    assign ``xlnx_master_name``_awqos = ``xlnx_slave_name``_awqos; \
    assign ``xlnx_master_name``_awatop = ``xlnx_slave_name``_awatop; \
    assign ``xlnx_master_name``_awregion = ``xlnx_slave_name``_awregion; \
    assign ``xlnx_master_name``_awuser = ``xlnx_slave_name``_awuser; \
    assign ``xlnx_master_name``_awvalid = ``xlnx_slave_name``_awvalid; \
    assign ``xlnx_slave_name``_awready = ``xlnx_master_name``_awready; \
    /* W Channel */\
    assign ``xlnx_master_name``_wdata = ``xlnx_slave_name``_wdata; \
    assign ``xlnx_master_name``_wstrb = ``xlnx_slave_name``_wstrb; \
    assign ``xlnx_master_name``_wlast = ``xlnx_slave_name``_wlast; \
    assign ``xlnx_master_name``_wuser = ``xlnx_slave_name``_wuser; \
    assign ``xlnx_master_name``_wvalid = ``xlnx_slave_name``_wvalid; \
    assign ``xlnx_slave_name``_wready = ``xlnx_master_name``_wready; \
    /* B Channel */\
    assign ``xlnx_slave_name``_bid = ``xlnx_master_name``_bid; \
    assign ``xlnx_slave_name``_bresp = ``xlnx_master_name``_bresp; \
    assign ``xlnx_slave_name``_buser = ``xlnx_master_name``_buser; \
    assign ``xlnx_slave_name``_bvalid = ``xlnx_master_name``_bvalid; \
    assign ``xlnx_master_name``_bready = ``xlnx_slave_name``_bready; \
    /* AR Channel*/ \
    assign ``xlnx_master_name``_arid = ``xlnx_slave_name``_arid; \
    assign ``xlnx_master_name``_araddr = ``xlnx_slave_name``_araddr; \
    assign ``xlnx_master_name``_arlen = ``xlnx_slave_name``_arlen; \
    assign ``xlnx_master_name``_arsize = ``xlnx_slave_name``_arsize; \
    assign ``xlnx_master_name``_arburst = ``xlnx_slave_name``_arburst; \
    assign ``xlnx_master_name``_arlock = ``xlnx_slave_name``_arlock; \
    assign ``xlnx_master_name``_arcache = ``xlnx_slave_name``_arcache; \
    assign ``xlnx_master_name``_arprot = ``xlnx_slave_name``_arprot; \
    assign ``xlnx_master_name``_arqos = ``xlnx_slave_name``_arqos; \
    assign ``xlnx_master_name``_arregion = ``xlnx_slave_name``_arregion; \
    assign ``xlnx_master_name``_aruser = ``xlnx_slave_name``_aruser; \
    assign ``xlnx_master_name``_arvalid = ``xlnx_slave_name``_arvalid; \
    assign ``xlnx_slave_name``_arready = ``xlnx_master_name``_arready; \
    /* R Channel */\
    assign ``xlnx_slave_name``_rdata = ``xlnx_master_name``_rdata ; \
    assign ``xlnx_slave_name``_rid = ``xlnx_master_name``_rid ; \
    assign ``xlnx_slave_name``_rresp = ``xlnx_master_name``_rresp; \
    assign ``xlnx_slave_name``_rlast = ``xlnx_master_name``_rlast; \
    assign ``xlnx_slave_name``_ruser = ``xlnx_master_name``_ruser; \
    assign ``xlnx_slave_name``_rvalid = ``xlnx_master_name``_rvalid; \
    assign ``xlnx_master_name``_rready = ``xlnx_slave_name``_rready;

`define ASSIGN_ARIANE_INTERFACE_FROM_XLNX_STYLE_INPUTS(xlnx_prefix, ariane_name)    \
    /* AW Channel  */ \
    assign ariane_name.aw_id = ``xlnx_prefix``_awid; \
    assign ariane_name.aw_addr = ``xlnx_prefix``_awaddr; \
    assign ariane_name.aw_len = ``xlnx_prefix``_awlen; \
    assign ariane_name.aw_size = ``xlnx_prefix``_awsize; \
    assign ariane_name.aw_burst = ``xlnx_prefix``_awburst; \
    assign ariane_name.aw_lock = ``xlnx_prefix``_awlock; \
    assign ariane_name.aw_cache = ``xlnx_prefix``_awcache; \
    assign ariane_name.aw_prot = ``xlnx_prefix``_awprot; \
    assign ariane_name.aw_qos = ``xlnx_prefix``_awqos; \
    assign ariane_name.aw_atop = ``xlnx_prefix``_awatop; \
    assign ariane_name.aw_region = ``xlnx_prefix``_awregion; \
    assign ariane_name.aw_user = ``xlnx_prefix``_awuser; \
    assign ariane_name.aw_valid = ``xlnx_prefix``_awvalid; \
    assign  ``xlnx_prefix``_awready = ariane_name.aw_ready; \
    /* W Channel */\
    assign ariane_name.w_data = ``xlnx_prefix``_wdata; \
    assign ariane_name.w_strb = ``xlnx_prefix``_wstrb; \
    assign ariane_name.w_last = ``xlnx_prefix``_wlast; \
    assign ariane_name.w_user = ``xlnx_prefix``_wuser; \
    assign ariane_name.w_valid = ``xlnx_prefix``_wvalid; \
    assign ``xlnx_prefix``_wready = ariane_name.w_ready; \
    /* B Channel */\
    assign ``xlnx_prefix``_bid = ariane_name.b_id ; \
    assign ``xlnx_prefix``_bresp = ariane_name.b_resp; \
    assign ``xlnx_prefix``_buser = ariane_name.b_user; \
    assign ``xlnx_prefix``_bvalid = ariane_name.b_valid; \
    assign ariane_name.b_ready = ``xlnx_prefix``_bready; \
    /* AR Channel*/ \
    assign ariane_name.ar_id = ``xlnx_prefix``_arid; \
    assign ariane_name.ar_addr = ``xlnx_prefix``_araddr; \
    assign ariane_name.ar_len = ``xlnx_prefix``_arlen; \
    assign ariane_name.ar_size = ``xlnx_prefix``_arsize; \
    assign ariane_name.ar_burst = ``xlnx_prefix``_arburst; \
    assign ariane_name.ar_lock = ``xlnx_prefix``_arlock; \
    assign ariane_name.ar_cache = ``xlnx_prefix``_arcache; \
    assign ariane_name.ar_prot = ``xlnx_prefix``_arprot; \
    assign ariane_name.ar_qos = ``xlnx_prefix``_arqos; \
    assign ariane_name.ar_region = ``xlnx_prefix``_arregion; \
    assign ariane_name.ar_user = ``xlnx_prefix``_aruser; \
    assign ariane_name.ar_valid = ``xlnx_prefix``_arvalid; \
    assign ``xlnx_prefix``_arready = ariane_name.ar_ready; \
    /* R Channel */\
    assign ``xlnx_prefix``_rdata = ariane_name.r_data; \
    assign ``xlnx_prefix``_rid= ariane_name.r_id; \
    assign ``xlnx_prefix``_rresp = ariane_name.r_resp; \
    assign ``xlnx_prefix``_rlast = ariane_name.r_last; \
    assign ``xlnx_prefix``_ruser = ariane_name.r_user; \
    assign ``xlnx_prefix``_rvalid = ariane_name.r_valid; \
    assign  ariane_name.r_ready = ``xlnx_prefix``_rready;

`define ASSIGN_XLNX_INTERFACE_FROM_ARIANE_STYLE_INPUTS(xlnx_prefix, ariane_name)    \
    /* AW Channel  */ \
    assign ``xlnx_prefix``_awid = ariane_name.aw_id;  \
    assign ``xlnx_prefix``_awaddr = ariane_name.aw_addr;  \
    assign ``xlnx_prefix``_awlen = ariane_name.aw_len;  \
    assign ``xlnx_prefix``_awsize = ariane_name.aw_size;  \
    assign ``xlnx_prefix``_awburst = ariane_name.aw_burst;  \
    assign ``xlnx_prefix``_awlock = ariane_name.aw_lock;  \
    assign ``xlnx_prefix``_awcache = ariane_name.aw_cache;  \
    assign ``xlnx_prefix``_awprot = ariane_name.aw_prot;  \
    assign ``xlnx_prefix``_awqos = ariane_name.aw_qos;  \
    assign ``xlnx_prefix``_awatop = ariane_name.aw_atop;  \
    assign ``xlnx_prefix``_awregion = ariane_name.aw_region;  \
    assign ``xlnx_prefix``_awuser = ariane_name.aw_user;  \
    assign ``xlnx_prefix``_awvalid = ariane_name.aw_valid;  \
    assign ariane_name.aw_ready = ``xlnx_prefix``_awready ; \
    /* W Channel */\
    assign ``xlnx_prefix``_wdata = ariane_name.w_data;  \
    assign ``xlnx_prefix``_wstrb = ariane_name.w_strb;  \
    assign ``xlnx_prefix``_wlast = ariane_name.w_last;  \
    assign ``xlnx_prefix``_wuser = ariane_name.w_user;  \
    assign ``xlnx_prefix``_wvalid = ariane_name.w_valid;  \
    assign ariane_name.w_ready = ``xlnx_prefix``_wready; \
    /* B Channel */\
    assign ariane_name.b_id = ``xlnx_prefix``_bid;  \
    assign ariane_name.b_resp = ``xlnx_prefix``_bresp;  \
    assign  ariane_name.b_user = ``xlnx_prefix``_buser;  \
    assign ariane_name.b_valid = ``xlnx_prefix``_bvalid;  \
    assign ``xlnx_prefix``_bready = ariane_name.b_ready; \
    /* AR Channel*/ \
    assign ``xlnx_prefix``_arid = ariane_name.ar_id;  \
    assign ``xlnx_prefix``_araddr = ariane_name.ar_addr;  \
    assign ``xlnx_prefix``_arlen = ariane_name.ar_len;  \
    assign ``xlnx_prefix``_arsize = ariane_name.ar_size;  \
    assign ``xlnx_prefix``_arburst = ariane_name.ar_burst;  \
    assign ``xlnx_prefix``_arlock = ariane_name.ar_lock;  \
    assign ``xlnx_prefix``_arcache = ariane_name.ar_cache;  \
    assign ``xlnx_prefix``_arprot = ariane_name.ar_prot;  \
    assign ``xlnx_prefix``_arqos = ariane_name.ar_qos;  \
    assign ``xlnx_prefix``_arregion = ariane_name.ar_region;  \
    assign ``xlnx_prefix``_aruser = ariane_name.ar_user;  \
    assign ``xlnx_prefix``_arvalid = ariane_name.ar_valid;  \
    assign ariane_name.ar_ready = ``xlnx_prefix``_arready; \
    /* R Channel */\
    assign ariane_name.r_data = ``xlnx_prefix``_rdata;  \
    assign ariane_name.r_id = ``xlnx_prefix``_rid;  \
    assign ariane_name.r_resp = ``xlnx_prefix``_rresp;  \
    assign ariane_name.r_last = ``xlnx_prefix``_rlast;  \
    assign ariane_name.r_user = ``xlnx_prefix``_ruser;  \
    assign ariane_name.r_valid = ``xlnx_prefix``_rvalid;  \
    assign ``xlnx_prefix``_rready = ariane_name.r_ready;

`define AXIS_MODULE_INPUT(prefix) \
    input wire ``prefix``_tvalid, \
    output wire ``prefix``_tready, \
    input wire [TDATA_WIDTH-1:0] ``prefix``_tdata, \
    input wire [TDATA_WIDTH / 8-1:0] ``prefix``_tstrb, \
    input wire [TDATA_WIDTH / 8-1:0] ``prefix``_tkeep, \
    input wire ``prefix``_tlast,\
    input wire [TID_WIDTH-1:0] ``prefix``_tid,\
    input wire [TDEST_WIDTH-1:0] ``prefix``_tdest,\
    input wire [TUSER_WIDTH-1:0] ``prefix``_tuser,\
    input wire ``prefix``_twakeup

`define AXIS_MODULE_OUTPUT(prefix) \
    output wire ``prefix``_tvalid, \
    input wire ``prefix``_tready, \
    output wire [TDATA_WIDTH-1:0] ``prefix``_tdata, \
    output wire [TDATA_WIDTH / 8-1:0] ``prefix``_tstrb, \
    output wire [TDATA_WIDTH / 8-1:0] ``prefix``_tkeep, \
    output wire ``prefix``_tlast,\
    output wire [TID_WIDTH-1:0] ``prefix``_tid,\
    output wire [TDEST_WIDTH-1:0] ``prefix``_tdest,\
    output wire [TUSER_WIDTH-1:0] ``prefix``_tuser,\
    output wire ``prefix``_twakeup

`define AXIS_INPUT_FORWARD(prefix) \
    .``prefix``_tvalid(``prefix``_tvalid), \
    .``prefix``_tready(``prefix``_tready), \
    .``prefix``_tdata(``prefix``_tdata), \
    .``prefix``_tstrb(``prefix``_tstrb), \
    .``prefix``_tkeep(``prefix``_tkeep), \
    .``prefix``_tlast(``prefix``_tlast),\
    .``prefix``_tid(``prefix``_tid),\
    .``prefix``_tdest(``prefix``_tdest),\
    .``prefix``_tuser(``prefix``_tuser),\
    .``prefix``_twakeup(``prefix``_twakeup)

`endif
