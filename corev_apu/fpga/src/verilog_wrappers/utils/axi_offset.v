// Copyright 2025 INRIA and Telecom SudParis.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Nicolas Derumigny <nicolas.derumigny@inria.fr>
//
// Date: 25.04.2025
// Description: Wrapper to offset AXI for devices where RAM addressing
// must start at 0.

module ram_offset_to_zero #(
    parameter AXI_ADDR_WIDTH = 32,
    parameter AXI_DATA_WIDTH = 64,
    parameter AXI_ID_WIDTH = 5,
    parameter AXI_USER_WIDTH = 0,
    parameter OFFSET = 'h80000000
) (
    /** Input AXI **/
    /* AW Channel  */
    input wire [AXI_ID_WIDTH - 1 : 0] s_axi_ram_awid,
    input wire [AXI_ADDR_WIDTH - 1 : 0] s_axi_ram_awaddr,
    input wire [7:0] s_axi_ram_awlen,
    input wire [2:0] s_axi_ram_awsize,
    input wire [1:0] s_axi_ram_awburst,
    input wire s_axi_ram_awlock,
    input wire [3:0] s_axi_ram_awcache,
    input wire [2:0] s_axi_ram_awprot,
    input wire [3:0] s_axi_ram_awqos,
    input wire [5:0] s_axi_ram_awatop,
    input wire [3:0] s_axi_ram_awregion,
    input wire [AXI_USER_WIDTH-1:0] s_axi_ram_awuser,
    input wire s_axi_ram_awvalid,
    output wire s_axi_ram_awready,
    /* W Channel */
    input wire [AXI_DATA_WIDTH - 1 : 0] s_axi_ram_wdata,
    input wire [AXI_DATA_WIDTH/8 - 1 : 0] s_axi_ram_wstrb,
    input wire s_axi_ram_wlast,
    input wire [AXI_USER_WIDTH-1:0] s_axi_ram_wuser,
    input wire s_axi_ram_wvalid,
    output wire s_axi_ram_wready,
    /* B Channel */
    output wire [AXI_ID_WIDTH - 1 : 0] s_axi_ram_bid,
    output wire [1 : 0] s_axi_ram_bresp,
    output wire [AXI_USER_WIDTH-1:0] s_axi_ram_buser,
    output wire s_axi_ram_bvalid,
    input wire s_axi_ram_bready,
    /* AR Channel*/
    input wire [AXI_ID_WIDTH - 1 : 0] s_axi_ram_arid,
    input wire [AXI_ADDR_WIDTH - 1 : 0] s_axi_ram_araddr,
    input wire [7:0] s_axi_ram_arlen,
    input wire [2:0] s_axi_ram_arsize,
    input wire [1:0] s_axi_ram_arburst,
    input wire s_axi_ram_arlock,
    input wire [3:0] s_axi_ram_arcache,
    input wire [2:0] s_axi_ram_arprot,
    input wire [3:0] s_axi_ram_arqos,
    input wire [3:0] s_axi_ram_arregion,
    input wire [AXI_USER_WIDTH-1:0] s_axi_ram_aruser,
    input wire s_axi_ram_arvalid,
    output wire s_axi_ram_arready,
    /* R Channel */
    output wire [AXI_DATA_WIDTH - 1 : 0] s_axi_ram_rdata,
    output wire [1 : 0] s_axi_ram_rresp,
    output wire s_axi_ram_rlast,
    output wire [AXI_ID_WIDTH - 1 : 0] s_axi_ram_rid,
    output wire [AXI_USER_WIDTH-1:0] s_axi_ram_ruser,
    output wire s_axi_ram_rvalid,
    input wire s_axi_ram_rready,

    /** Output AXI **/
    /* AW Channel  */
    output wire [AXI_ID_WIDTH - 1 : 0] m_axi_ram_awid,
    output wire [AXI_ADDR_WIDTH - 1 : 0] m_axi_ram_awaddr,
    output wire [7:0] m_axi_ram_awlen,
    output wire [2:0] m_axi_ram_awsize,
    output wire [1:0] m_axi_ram_awburst,
    output wire m_axi_ram_awlock,
    output wire [3:0] m_axi_ram_awcache,
    output wire [2:0] m_axi_ram_awprot,
    output wire [3:0] m_axi_ram_awqos,
    output wire [5:0] m_axi_ram_awatop,
    output wire [3:0] m_axi_ram_awregion,
    output wire [AXI_USER_WIDTH-1:0] m_axi_ram_awuser,
    output wire m_axi_ram_awvalid,
    input wire m_axi_ram_awready,
    /* W Channel */
    output wire [AXI_DATA_WIDTH - 1 : 0] m_axi_ram_wdata,
    output wire [AXI_DATA_WIDTH/8 - 1 : 0] m_axi_ram_wstrb,
    output wire m_axi_ram_wlast,
    output wire [AXI_USER_WIDTH-1:0] m_axi_ram_wuser,
    output wire m_axi_ram_wvalid,
    input wire m_axi_ram_wready,
    /* B Channel */
    input wire [AXI_ID_WIDTH - 1 : 0] m_axi_ram_bid,
    input wire [1 : 0] m_axi_ram_bresp,
    input wire [AXI_USER_WIDTH-1:0] m_axi_ram_buser,
    input wire m_axi_ram_bvalid,
    output wire m_axi_ram_bready,
    /* AR Channel*/
    output wire [AXI_ID_WIDTH - 1 : 0] m_axi_ram_arid,
    output wire [AXI_ADDR_WIDTH - 1 : 0] m_axi_ram_araddr,
    output wire [7:0] m_axi_ram_arlen,
    output wire [2:0] m_axi_ram_arsize,
    output wire [1:0] m_axi_ram_arburst,
    output wire m_axi_ram_arlock,
    output wire [3:0] m_axi_ram_arcache,
    output wire [2:0] m_axi_ram_arprot,
    output wire [3:0] m_axi_ram_arqos,
    output wire [3:0] m_axi_ram_arregion,
    output wire [AXI_USER_WIDTH-1:0] m_axi_ram_aruser,
    output wire m_axi_ram_arvalid,
    input wire [AXI_USER_WIDTH-1:0] m_axi_ram_arready,
    /* R Channel */
    input wire [AXI_DATA_WIDTH - 1 : 0] m_axi_ram_rdata,
    input wire [1 : 0] m_axi_ram_rresp,
    input wire m_axi_ram_rlast,
    input wire [AXI_ID_WIDTH - 1 : 0] m_axi_ram_rid,
    input wire [AXI_USER_WIDTH-1:0] m_axi_ram_ruser,
    input wire m_axi_ram_rvalid,
    output wire m_axi_ram_rready,

    /*Clock, unused but avoid Vivado errors*/
    input wire aclk
);
  /* AW Channel  */
  assign m_axi_ram_awid = s_axi_ram_awid;
  assign m_axi_ram_awaddr = s_axi_ram_awaddr - OFFSET;
  assign m_axi_ram_awlen = s_axi_ram_awlen;
  assign m_axi_ram_awsize = s_axi_ram_awsize;
  assign m_axi_ram_awburst = s_axi_ram_awburst;
  assign m_axi_ram_awlock = s_axi_ram_awlock;
  assign m_axi_ram_awcache = s_axi_ram_awcache;
  assign m_axi_ram_awprot = s_axi_ram_awprot;
  assign m_axi_ram_awqos = s_axi_ram_awqos;
  assign m_axi_ram_awatop = s_axi_ram_awatop;
  assign m_axi_ram_awregion = s_axi_ram_awregion;
  assign m_axi_ram_awuser = s_axi_ram_awuser;
  assign m_axi_ram_awvalid = s_axi_ram_awvalid;
  assign s_axi_ram_awready = m_axi_ram_awready;
  /* W Channel */
  assign m_axi_ram_wdata = s_axi_ram_wdata;
  assign m_axi_ram_wstrb = s_axi_ram_wstrb;
  assign m_axi_ram_wlast = s_axi_ram_wlast;
  assign m_axi_ram_wuser = s_axi_ram_wuser;
  assign m_axi_ram_wvalid = s_axi_ram_wvalid;
  assign s_axi_ram_wready = m_axi_ram_wready;
  /* B Channel */
  assign s_axi_ram_bid = m_axi_ram_bid;
  assign s_axi_ram_bresp = m_axi_ram_bresp;
  assign s_axi_ram_buser = m_axi_ram_buser;
  assign s_axi_ram_bvalid = m_axi_ram_bvalid;
  assign m_axi_ram_bready = s_axi_ram_bready;
  /* AR Channel*/
  assign m_axi_ram_arid = s_axi_ram_arid;
  assign m_axi_ram_araddr = s_axi_ram_araddr - OFFSET;
  assign m_axi_ram_arlen = s_axi_ram_arlen;
  assign m_axi_ram_arsize = s_axi_ram_arsize;
  assign m_axi_ram_arburst = s_axi_ram_arburst;
  assign m_axi_ram_arlock = s_axi_ram_arlock;
  assign m_axi_ram_arcache = s_axi_ram_arcache;
  assign m_axi_ram_arprot = s_axi_ram_arprot;
  assign m_axi_ram_arqos = s_axi_ram_arqos;
  assign m_axi_ram_arregion = s_axi_ram_arregion;
  assign m_axi_ram_aruser = s_axi_ram_aruser;
  assign m_axi_ram_arvalid = s_axi_ram_arvalid;
  assign s_axi_ram_arready = m_axi_ram_arready;
  /* R Channel */
  assign s_axi_ram_rdata = m_axi_ram_rdata;
  assign s_axi_ram_rid = m_axi_ram_rid;
  assign s_axi_ram_rresp = m_axi_ram_rresp;
  assign s_axi_ram_rlast = m_axi_ram_rlast;
  assign s_axi_ram_ruser = m_axi_ram_ruser;
  assign s_axi_ram_rvalid = m_axi_ram_rvalid;
  assign m_axi_ram_rready = s_axi_ram_rready;
endmodule
