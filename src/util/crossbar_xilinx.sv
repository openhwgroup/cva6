module crossbar_xilinx(
                       AXI_BUS.Slave bypass_if, data_if, instr_if,
                       AXI_BUS.Master master0_if, master1_if,
                       input clk_i, rst_ni
                       );
  
axi_crossbar_0 crossbar (
  .aclk(clk_i),                      // input wire aclk
  .aresetn(rst_ni),                // input wire aresetn
  .s_axi_awid({bypass_if.aw_id,data_if.aw_id,instr_if.aw_id}),          // input wire [29 : 0] s_axi_awid
  .s_axi_awaddr({bypass_if.aw_addr,data_if.aw_addr,instr_if.aw_addr}),      // input wire [191 : 0] s_axi_awaddr
  .s_axi_awlen({bypass_if.aw_len,data_if.aw_len,instr_if.aw_len}),        // input wire [23 : 0] s_axi_awlen
  .s_axi_awsize({bypass_if.aw_size,data_if.aw_size,instr_if.aw_size}),      // input wire [8 : 0] s_axi_awsize
  .s_axi_awburst({bypass_if.aw_burst,data_if.aw_burst,instr_if.aw_burst}),    // input wire [5 : 0] s_axi_awburst
  .s_axi_awlock({bypass_if.aw_lock,data_if.aw_lock,instr_if.aw_lock}),      // input wire [2 : 0] s_axi_awlock
  .s_axi_awcache({bypass_if.aw_cache,data_if.aw_cache,instr_if.aw_cache}),    // input wire [11 : 0] s_axi_awcache
  .s_axi_awprot({bypass_if.aw_prot,data_if.aw_prot,instr_if.aw_prot}),      // input wire [8 : 0] s_axi_awprot
  .s_axi_awqos({bypass_if.aw_qos,data_if.aw_qos,instr_if.aw_qos}),        // input wire [11 : 0] s_axi_awqos
  .s_axi_awuser({bypass_if.aw_user,data_if.aw_user,instr_if.aw_user}),      // input wire [2 : 0] s_axi_awuser
  .s_axi_awvalid({bypass_if.aw_valid,data_if.aw_valid,instr_if.aw_valid}),    // input wire [2 : 0] s_axi_awvalid
  .s_axi_awready({bypass_if.aw_ready,data_if.aw_ready,instr_if.aw_ready}),    // output wire [2 : 0] s_axi_awready
  .s_axi_wdata({bypass_if.w_data,data_if.w_data,instr_if.w_data}),        // input wire [191 : 0] s_axi_wdata
  .s_axi_wstrb({bypass_if.w_strb,data_if.w_strb,instr_if.w_strb}),        // input wire [23 : 0] s_axi_wstrb
  .s_axi_wlast({bypass_if.w_last,data_if.w_last,instr_if.w_last}),        // input wire [2 : 0] s_axi_wlast
  .s_axi_wuser({bypass_if.w_user,data_if.w_user,instr_if.w_user}),        // input wire [2 : 0] s_axi_wuser
  .s_axi_wvalid({bypass_if.w_valid,data_if.w_valid,instr_if.w_valid}),      // input wire [2 : 0] s_axi_wvalid
  .s_axi_wready({bypass_if.w_ready,data_if.w_ready,instr_if.w_ready}),      // output wire [2 : 0] s_axi_wready
  .s_axi_bid({bypass_if.b_id,data_if.b_id,instr_if.b_id}),            // output wire [29 : 0] s_axi_bid
  .s_axi_bresp({bypass_if.b_resp,data_if.b_resp,instr_if.b_resp}),        // output wire [5 : 0] s_axi_bresp
  .s_axi_buser({bypass_if.b_user,data_if.b_user,instr_if.b_user}),        // output wire [2 : 0] s_axi_buser
  .s_axi_bvalid({bypass_if.b_valid,data_if.b_valid,instr_if.b_valid}),      // output wire [2 : 0] s_axi_bvalid
  .s_axi_bready({bypass_if.b_ready,data_if.b_ready,instr_if.b_ready}),      // input wire [2 : 0] s_axi_bready
  .s_axi_arid({bypass_if.ar_id,data_if.ar_id,instr_if.ar_id}),          // input wire [29 : 0] s_axi_arid
  .s_axi_araddr({bypass_if.ar_addr,data_if.ar_addr,instr_if.ar_addr}),      // input wire [191 : 0] s_axi_araddr
  .s_axi_arlen({bypass_if.ar_len,data_if.ar_len,instr_if.ar_len}),        // input wire [23 : 0] s_axi_arlen
  .s_axi_arsize({bypass_if.ar_size,data_if.ar_size,instr_if.ar_size}),      // input wire [8 : 0] s_axi_arsize
  .s_axi_arburst({bypass_if.ar_burst,data_if.ar_burst,instr_if.ar_burst}),    // input wire [5 : 0] s_axi_arburst
  .s_axi_arlock({bypass_if.ar_lock,data_if.ar_lock,instr_if.ar_lock}),      // input wire [2 : 0] s_axi_arlock
  .s_axi_arcache({bypass_if.ar_cache,data_if.ar_cache,instr_if.ar_cache}),    // input wire [11 : 0] s_axi_arcache
  .s_axi_arprot({bypass_if.ar_prot,data_if.ar_prot,instr_if.ar_prot}),      // input wire [8 : 0] s_axi_arprot
  .s_axi_arqos({bypass_if.ar_qos,data_if.ar_qos,instr_if.ar_qos}),        // input wire [11 : 0] s_axi_arqos
  .s_axi_aruser({bypass_if.ar_user,data_if.ar_user,instr_if.ar_user}),      // input wire [2 : 0] s_axi_aruser
  .s_axi_arvalid({bypass_if.ar_valid,data_if.ar_valid,instr_if.ar_valid}),    // input wire [2 : 0] s_axi_arvalid
  .s_axi_arready({bypass_if.ar_ready,data_if.ar_ready,instr_if.ar_ready}),    // output wire [2 : 0] s_axi_arready
  .s_axi_rid({bypass_if.r_id,data_if.r_id,instr_if.r_id}),            // output wire [29 : 0] s_axi_rid
  .s_axi_rdata({bypass_if.r_data,data_if.r_data,instr_if.r_data}),        // output wire [191 : 0] s_axi_rdata
  .s_axi_rresp({bypass_if.r_resp,data_if.r_resp,instr_if.r_resp}),        // output wire [5 : 0] s_axi_rresp
  .s_axi_rlast({bypass_if.r_last,data_if.r_last,instr_if.r_last}),        // output wire [2 : 0] s_axi_rlast
  .s_axi_ruser({bypass_if.r_user,data_if.r_user,instr_if.r_user}),        // output wire [2 : 0] s_axi_ruser
  .s_axi_rvalid({bypass_if.r_valid,data_if.r_valid,instr_if.r_valid}),      // output wire [2 : 0] s_axi_rvalid
  .s_axi_rready({bypass_if.r_ready,data_if.r_ready,instr_if.r_ready}),      // input wire [2 : 0] s_axi_rready
  .m_axi_awid({master1_if.aw_id,master0_if.aw_id}),          // input wire [29 : 0] s_axi_awid
  .m_axi_awaddr({master1_if.aw_addr,master0_if.aw_addr}),      // input wire [191 : 0] s_axi_awaddr
  .m_axi_awlen({master1_if.aw_len,master0_if.aw_len}),        // input wire [23 : 0] s_axi_awlen
  .m_axi_awsize({master1_if.aw_size,master0_if.aw_size}),      // input wire [8 : 0] s_axi_awsize
  .m_axi_awburst({master1_if.aw_burst,master0_if.aw_burst}),    // input wire [5 : 0] s_axi_awburst
  .m_axi_awlock({master1_if.aw_lock,master0_if.aw_lock}),      // input wire [2 : 0] s_axi_awlock
  .m_axi_awcache({master1_if.aw_cache,master0_if.aw_cache}),    // input wire [11 : 0] s_axi_awcache
  .m_axi_awprot({master1_if.aw_prot,master0_if.aw_prot}),      // input wire [8 : 0] s_axi_awprot
  .m_axi_awqos({master1_if.aw_qos,master0_if.aw_qos}),        // input wire [11 : 0] s_axi_awqos
  .m_axi_awuser({master1_if.aw_user,master0_if.aw_user}),      // input wire [2 : 0] s_axi_awuser
  .m_axi_awvalid({master1_if.aw_valid,master0_if.aw_valid}),    // input wire [2 : 0] s_axi_awvalid
  .m_axi_awready({master1_if.aw_ready,master0_if.aw_ready}),    // output wire [2 : 0] s_axi_awready
  .m_axi_awregion({master1_if.aw_region,master0_if.aw_region}),    // output s_axi_awregion
  .m_axi_wdata({master1_if.w_data,master0_if.w_data}),        // input wire [191 : 0] s_axi_wdata
  .m_axi_wstrb({master1_if.w_strb,master0_if.w_strb}),        // input wire [23 : 0] s_axi_wstrb
  .m_axi_wlast({master1_if.w_last,master0_if.w_last}),        // input wire [2 : 0] s_axi_wlast
  .m_axi_wuser({master1_if.w_user,master0_if.w_user}),        // input wire [2 : 0] s_axi_wuser
  .m_axi_wvalid({master1_if.w_valid,master0_if.w_valid}),      // input wire [2 : 0] s_axi_wvalid
  .m_axi_wready({master1_if.w_ready,master0_if.w_ready}),      // output wire [2 : 0] s_axi_wready
  .m_axi_bid({master1_if.b_id,master0_if.b_id}),            // output wire [29 : 0] s_axi_bid
  .m_axi_bresp({master1_if.b_resp,master0_if.b_resp}),        // output wire [5 : 0] s_axi_bresp
  .m_axi_buser({master1_if.b_user,master0_if.b_user}),        // output wire [2 : 0] s_axi_buser
  .m_axi_bvalid({master1_if.b_valid,master0_if.b_valid}),      // output wire [2 : 0] s_axi_bvalid
  .m_axi_bready({master1_if.b_ready,master0_if.b_ready}),      // input wire [2 : 0] s_axi_bready
  .m_axi_arid({master1_if.ar_id,master0_if.ar_id}),          // input wire [29 : 0] s_axi_arid
  .m_axi_araddr({master1_if.ar_addr,master0_if.ar_addr}),      // input wire [191 : 0] s_axi_araddr
  .m_axi_arlen({master1_if.ar_len,master0_if.ar_len}),        // input wire [23 : 0] s_axi_arlen
  .m_axi_arsize({master1_if.ar_size,master0_if.ar_size}),      // input wire [8 : 0] s_axi_arsize
  .m_axi_arburst({master1_if.ar_burst,master0_if.ar_burst}),    // input wire [5 : 0] s_axi_arburst
  .m_axi_arlock({master1_if.ar_lock,master0_if.ar_lock}),      // input wire [2 : 0] s_axi_arlock
  .m_axi_arcache({master1_if.ar_cache,master0_if.ar_cache}),    // input wire [11 : 0] s_axi_arcache
  .m_axi_arprot({master1_if.ar_prot,master0_if.ar_prot}),      // input wire [8 : 0] s_axi_arprot
  .m_axi_arqos({master1_if.ar_qos,master0_if.ar_qos}),        // input wire [11 : 0] s_axi_arqos
  .m_axi_aruser({master1_if.ar_user,master0_if.ar_user}),      // input wire [2 : 0] s_axi_aruser
  .m_axi_arvalid({master1_if.ar_valid,master0_if.ar_valid}),    // input wire [2 : 0] s_axi_arvalid
  .m_axi_arready({master1_if.ar_ready,master0_if.ar_ready}),    // output wire [2 : 0] s_axi_arready
  .m_axi_arregion({master1_if.ar_region,master0_if.ar_region}),    // output s_axi_arregion
  .m_axi_rid({master1_if.r_id,master0_if.r_id}),            // output wire [29 : 0] s_axi_rid
  .m_axi_rdata({master1_if.r_data,master0_if.r_data}),        // output wire [191 : 0] s_axi_rdata
  .m_axi_rresp({master1_if.r_resp,master0_if.r_resp}),        // output wire [5 : 0] s_axi_rresp
  .m_axi_rlast({master1_if.r_last,master0_if.r_last}),        // output wire [2 : 0] s_axi_rlast
  .m_axi_ruser({master1_if.r_user,master0_if.r_user}),        // output wire [2 : 0] s_axi_ruser
  .m_axi_rvalid({master1_if.r_valid,master0_if.r_valid}),      // output wire [2 : 0] s_axi_rvalid
  .m_axi_rready({master1_if.r_ready,master0_if.r_ready})      // input wire [2 : 0] s_axi_rready
);

endmodule
