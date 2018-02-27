// File mii_to_rmii_0_exdes.vhd translated with vhd2vl v2.0 VHDL to Verilog RTL translator
// Copyright (C) 2001 Vincenzo Liguori - Ocean Logic Pty Ltd - http://www.ocean-logic.com
// Modifications (C) 2006 Mark Gonzales - PMC Sierra Inc
// 
// vhd2vl comes with ABSOLUTELY NO WARRANTY
// ALWAYS RUN A FORMAL VERIFICATION TOOL TO COMPARE VHDL INPUT TO VERILOG OUTPUT 
// 
// This is free software, and you are welcome to redistribute it under certain conditions.
// See the license file license.txt included with the source for details.

//Example design Top
// file: exdes_top.vhd
// 
// (c) Copyright 2008 - 2013 Xilinx, Inc. All rights reserved.
// 
// This file contains confidential and proprietary information
// of Xilinx, Inc. and is protected under U.S. and
// international copyright and other intellectual property
// laws.
// 
// DISCLAIMER
// This disclaimer is not a license and does not grant any
// rights to the materials distributed herewith. Except as
// otherwise provided in a valid license issued to you by
// Xilinx, and to the maximum extent permitted by applicable
// law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
// WITH ALL FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES
// AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
// BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
// INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
// (2) Xilinx shall not be liable (whether in contract or tort,
// including negligence, or under any other theory of
// liability) for any loss or damage of any kind or nature
// related to, arising under or in connection with these
// materials, including for any direct, or any indirect,
// special, incidental, or consequential loss or damage
// (including loss of data, profits, goodwill, or any type of
// loss or damage suffered as a result of any action brought
// by a third party) even if such damage or loss was
// reasonably foreseeable or Xilinx had been advised of the
// possibility of the same.
// 
// CRITICAL APPLICATIONS
// Xilinx products are not designed or intended to be fail-
// safe, or for use in any application requiring fail-safe
// performance, such as life-support or safety devices or
// systems, Class III medical devices, nuclear facilities,
// applications related to the deployment of airbags, or any
// other applications that could lead to death, personal
// injury, or severe property or environmental damage
// (individually and collectively, "Critical
// Applications"). Customer assumes the sole risk and
// liability of any use of Xilinx products in Critical
// Applications, subject only to applicable laws and
// regulations governing limitations on product liability.
// 
// THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
// PART OF THIS FILE AT ALL TIMES.
// 
//----------------------------------------------------------------------------
// User entered comments
//----------------------------------------------------------------------------
// This is a self-desigined TOP Wrapper developed for MII to RMII Example Design
//
//----------------------------------------------------------------------------
`default_nettype none

module mii_to_rmii_0_open(
input wire clk_rmii,
input wire locked,
// SMSC ethernet PHY
output wire eth_rstn,
input wire eth_crsdv,
output wire eth_refclk,
output wire[1:0] eth_txd,
output wire eth_txen,
input wire[1:0] eth_rxd,
input wire eth_rxerr,
output wire eth_mdc,
input wire phy_mdio_i,
output wire phy_mdio_o,
output wire phy_mdio_t,
input wire s_axi_aclk,
input wire s_axi_aresetn,
input wire [7:0]s_axi_awid,
input wire [31:0]s_axi_awaddr,
input wire [7:0]s_axi_awlen,
input wire [2:0]s_axi_awsize,
input wire [1:0]s_axi_awburst,
input wire s_axi_awlock,
input wire [3:0]s_axi_awcache,
input wire [2:0]s_axi_awprot,
input wire s_axi_awvalid,
output wire s_axi_awready,
input wire [31:0]s_axi_wdata,
input wire [3:0]s_axi_wstrb,
input wire s_axi_wlast,
input wire s_axi_wvalid,
output wire s_axi_wready,
output wire [7:0] s_axi_bid,
output wire [1:0]s_axi_bresp,
output wire s_axi_bvalid,
input wire s_axi_bready,
input wire [7:0] s_axi_arid,
input wire [31:0]s_axi_araddr,
input wire [7:0]s_axi_arlen,
input wire [2:0]s_axi_arsize,
input wire [1:0]s_axi_arburst,
input wire s_axi_arlock,
input wire [3:0]s_axi_arcache,
input wire [2:0]s_axi_arprot,
input wire s_axi_arvalid,
output wire s_axi_arready,
output wire [7:0] s_axi_rid,
output wire [31:0]s_axi_rdata,
output wire [1:0]s_axi_rresp,
output wire s_axi_rlast,
output wire s_axi_rvalid,
input wire s_axi_rready,
output wire eth_irq);

   wire     bram_rst_a;
   wire     bram_clk_a;
   wire     bram_en_a;
   wire [3:0] bram_we_a;
   wire [12:0] bram_addr_a;
   wire [31:0] bram_wrdata_a, bram_rddata_a;

   axi_bram_ctrl_1 BramCtl
     (
      .s_axi_aclk(s_axi_aclk),        // input wire s_axi_aclk
      .s_axi_aresetn(s_axi_aresetn),  // input wire s_axi_aresetn
      .s_axi_awid(s_axi_awid),        // input wire [7 : 0] s_axi_awid
      .s_axi_awaddr(s_axi_awaddr[12:0]),    // input wire [12 : 0] s_axi_awaddr
      .s_axi_awlen(s_axi_awlen),      // input wire [7 : 0] s_axi_awlen
      .s_axi_awsize(s_axi_awsize),    // input wire [2 : 0] s_axi_awsize
      .s_axi_awburst(s_axi_awburst),  // input wire [1 : 0] s_axi_awburst
      .s_axi_awlock(s_axi_awlock),    // input wire s_axi_awlock
      .s_axi_awcache(s_axi_awcache),  // input wire [3 : 0] s_axi_awcache
      .s_axi_awprot(s_axi_awprot),    // input wire [2 : 0] s_axi_awprot
      .s_axi_awvalid(s_axi_awvalid),  // input wire s_axi_awvalid
      .s_axi_awready(s_axi_awready),  // output wire s_axi_awready
      .s_axi_wdata(s_axi_wdata),      // input wire [31 : 0] s_axi_wdata
      .s_axi_wstrb(s_axi_wstrb),      // input wire [3 : 0] s_axi_wstrb
      .s_axi_wlast(s_axi_wlast),      // input wire s_axi_wlast
      .s_axi_wvalid(s_axi_wvalid),    // input wire s_axi_wvalid
      .s_axi_wready(s_axi_wready),    // output wire s_axi_wready
      .s_axi_bid(s_axi_bid),          // output wire [7 : 0] s_axi_bid
      .s_axi_bresp(s_axi_bresp),      // output wire [1 : 0] s_axi_bresp
      .s_axi_bvalid(s_axi_bvalid),    // output wire s_axi_bvalid
      .s_axi_bready(s_axi_bready),    // input wire s_axi_bready
      .s_axi_arid(s_axi_arid),        // input wire [7 : 0] s_axi_arid
      .s_axi_araddr(s_axi_araddr[12:0]),    // input wire [12 : 0] s_axi_araddr
      .s_axi_arlen(s_axi_arlen),      // input wire [7 : 0] s_axi_arlen
      .s_axi_arsize(s_axi_arsize),    // input wire [2 : 0] s_axi_arsize
      .s_axi_arburst(s_axi_arburst),  // input wire [1 : 0] s_axi_arburst
      .s_axi_arlock(s_axi_arlock),    // input wire s_axi_arlock
      .s_axi_arcache(s_axi_arcache),  // input wire [3 : 0] s_axi_arcache
      .s_axi_arprot(s_axi_arprot),    // input wire [2 : 0] s_axi_arprot
      .s_axi_arvalid(s_axi_arvalid),  // input wire s_axi_arvalid
      .s_axi_arready(s_axi_arready),  // output wire s_axi_arready
      .s_axi_rid(s_axi_rid),          // output wire [7 : 0] s_axi_rid
      .s_axi_rdata(s_axi_rdata),      // output wire [31 : 0] s_axi_rdata
      .s_axi_rresp(s_axi_rresp),      // output wire [1 : 0] s_axi_rresp
      .s_axi_rlast(s_axi_rlast),      // output wire s_axi_rlast
      .s_axi_rvalid(s_axi_rvalid),    // output wire s_axi_rvalid
      .s_axi_rready(s_axi_rready),    // input wire s_axi_rready
      .bram_rst_a(bram_rst_a),        // output wire bram_rst_a
      .bram_clk_a(bram_clk_a),        // output wire bram_clk_a
      .bram_en_a(bram_en_a),          // output wire bram_en_a
      .bram_we_a(bram_we_a),          // output wire [3 : 0] bram_we_a
      .bram_addr_a(bram_addr_a),      // output wire [14 : 0] bram_addr_a
      .bram_wrdata_a(bram_wrdata_a),  // output wire [31 : 0] bram_wrdata_a
      .bram_rddata_a(bram_rddata_a)   // input wire [31 : 0] bram_rddata_a
      );
   
framing_top open
  (
   .rstn(locked),
   .msoc_clk(s_axi_aclk),
   .clk_rmii(clk_rmii),
   .core_lsu_addr(bram_addr_a),
   .core_lsu_wdata(bram_wrdata_a),
   .core_lsu_be(bram_we_a),
   .ce_d(bram_en_a),
   .we_d(|bram_we_a),
   .framing_sel(bram_en_a),
   .framing_rdata(bram_rddata_a),
   .o_edutrefclk(eth_refclk),
   .i_edutrxd(eth_rxd),
   .i_edutrx_dv(eth_crsdv),
   .i_edutrx_er(eth_rxerr),
   .o_eduttxd(eth_txd),
   .o_eduttx_en(eth_txen),
   .o_edutmdc(eth_mdc),
   .i_edutmdio(phy_mdio_i),
   .o_edutmdio(phy_mdio_o),
   .oe_edutmdio(phy_mdio_t),
   .o_edutrstn(eth_rstn),
   .eth_irq(eth_irq)
);

endmodule
