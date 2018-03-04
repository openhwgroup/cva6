// Copyright 2014-2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the “License”); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an “AS IS” BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// `timescale 1ns/1ps
// `define SOD 0.5

`default_nettype none
  
module   axi_bram_ctrl_ariane
#(
    parameter AXI4_ADDRESS_WIDTH = 32,
    parameter AXI4_RDATA_WIDTH   = 64,
    parameter AXI4_WDATA_WIDTH   = 64,
    parameter AXI4_ID_WIDTH      = 16,
    parameter AXI4_USER_WIDTH    = 10,
    parameter AXI_NUMBYTES       = AXI4_WDATA_WIDTH/8,
    parameter MEM_ADDR_WIDTH     = 13,
    parameter BUFF_DEPTH_SLAVE   = 4
)
(

    input logic                                     s_axi_aclk,
    input logic                                     s_axi_aresetn,
    // ---------------------------------------------------------
    // AXI TARG Port Declarations ------------------------------
    // ---------------------------------------------------------
    //AXI write address bus -------------- // USED// -----------
    input  logic [AXI4_ID_WIDTH-1:0]                s_axi_awid,
    input  logic [AXI4_ADDRESS_WIDTH-1:0]           s_axi_awaddr,
    input  logic [ 7:0]                             s_axi_awlen,
    input  logic [ 2:0]                             s_axi_awsize,
    input  logic [ 1:0]                             s_axi_awburst,
    input  logic                                    s_axi_awlock,
    input  logic [ 3:0]                             s_axi_awcache,
    input  logic [ 2:0]                             s_axi_awprot,
    input  logic [ 3:0]                             s_axi_awregion,
    input  logic [ AXI4_USER_WIDTH-1:0]             s_axi_awuser,
    input  logic [ 3:0]                             s_axi_awqos,
    input  logic                                    s_axi_awvalid,
    output logic                                    s_axi_awready,
    // ---------------------------------------------------------

    //AXI write data bus -------------- // USED// --------------
    input  logic [AXI_NUMBYTES-1:0][7:0]            s_axi_wdata,
    input  logic [AXI_NUMBYTES-1:0]                 s_axi_wstrb,
    input  logic                                    s_axi_wlast,
    input  logic [AXI4_USER_WIDTH-1:0]              s_axi_wuser,
    input  logic                                    s_axi_wvalid,
    output logic                                    s_axi_wready,
    // ---------------------------------------------------------

    //AXI write response bus -------------- // USED// ----------
    output logic   [AXI4_ID_WIDTH-1:0]              s_axi_bid,
    output logic   [ 1:0]                           s_axi_bresp,
    output logic                                    s_axi_bvalid,
    output logic   [AXI4_USER_WIDTH-1:0]            s_axi_buser,
    input  logic                                    s_axi_bready,
    // ---------------------------------------------------------

    //AXI read address bus -------------------------------------
    input  logic [AXI4_ID_WIDTH-1:0]                s_axi_arid,
    input  logic [AXI4_ADDRESS_WIDTH-1:0]           s_axi_araddr,
    input  logic [ 7:0]                             s_axi_arlen,
    input  logic [ 2:0]                             s_axi_arsize,
    input  logic [ 1:0]                             s_axi_arburst,
    input  logic                                    s_axi_arlock,
    input  logic [ 3:0]                             s_axi_arcache,
    input  logic [ 2:0]                             s_axi_arprot,
    input  logic [ 3:0]                             s_axi_arregion,
    input  logic [ AXI4_USER_WIDTH-1:0]             s_axi_aruser,
    input  logic [ 3:0]                             s_axi_arqos,
    input  logic                                    s_axi_arvalid,
    output logic                                    s_axi_arready,
    // ---------------------------------------------------------

    //AXI read data bus ----------------------------------------
    output  logic [AXI4_ID_WIDTH-1:0]               s_axi_rid,
    output  logic [AXI4_RDATA_WIDTH-1:0]            s_axi_rdata,
    output  logic [ 1:0]                            s_axi_rresp,
    output  logic                                   s_axi_rlast,
    output  logic [AXI4_USER_WIDTH-1:0]             s_axi_ruser,
    output  logic                                   s_axi_rvalid,
    input   logic                                   s_axi_rready,
    // ---------------------------------------------------------

    output logic                                    bram_rst_a  ,
    output logic                                    bram_clk_a  ,
    output logic                                    bram_en_a  ,
    output logic  [MEM_ADDR_WIDTH-1:0]              bram_addr_a ,
    output logic  [AXI4_WDATA_WIDTH-1:0]            bram_wrdata_a ,
    output logic  [AXI_NUMBYTES-1:0]                bram_we_a ,
    input  logic  [AXI4_RDATA_WIDTH-1:0]            bram_rddata_a

);

   logic [AXI_NUMBYTES-1:0]                         bram_bank_en;
   logic                                            bram_chip_enb, bram_write_enb;
   
assign bram_rst_a = 1'b0;
assign bram_clk_a = s_axi_aclk;
assign bram_en_a = !bram_chip_enb;
assign bram_we_a = bram_write_enb ? 'b0 : bram_bank_en;

    axi_mem_if
    #(
        .AXI4_ADDRESS_WIDTH(AXI4_ADDRESS_WIDTH),
        .AXI4_RDATA_WIDTH(AXI4_RDATA_WIDTH),
        .AXI4_WDATA_WIDTH(AXI4_WDATA_WIDTH),
        .AXI4_ID_WIDTH(AXI4_ID_WIDTH),
        .AXI4_USER_WIDTH(AXI4_USER_WIDTH),
        .BUFF_DEPTH_SLAVE(BUFF_DEPTH_SLAVE)
    )
    axi_mem_if_i
    (
        .ACLK       ( s_axi_aclk              ),
        .ARESETn    ( s_axi_aresetn           ),

        .AWVALID_i  ( s_axi_awvalid           ),
        .AWADDR_i   ( s_axi_awaddr            ),
        .AWPROT_i   ( s_axi_awprot            ),
        .AWREGION_i ( s_axi_awregion          ),
        .AWLEN_i    ( s_axi_awlen             ),
        .AWSIZE_i   ( s_axi_awsize            ),
        .AWBURST_i  ( s_axi_awburst           ),
        .AWLOCK_i   ( s_axi_awlock            ),
        .AWCACHE_i  ( s_axi_awcache           ),
        .AWQOS_i    ( s_axi_awqos             ),
        .AWID_i     ( s_axi_awid              ),
        .AWUSER_i   ( s_axi_awuser            ),
        .AWREADY_o  ( s_axi_awready           ),

        .ARVALID_i  ( s_axi_arvalid           ),
        .ARADDR_i   ( s_axi_araddr            ),
        .ARPROT_i   ( s_axi_arprot            ),
        .ARREGION_i ( s_axi_arregion          ),
        .ARLEN_i    ( s_axi_arlen             ),
        .ARSIZE_i   ( s_axi_arsize            ),
        .ARBURST_i  ( s_axi_arburst           ),
        .ARLOCK_i   ( s_axi_arlock            ),
        .ARCACHE_i  ( s_axi_arcache           ),
        .ARQOS_i    ( s_axi_arqos             ),
        .ARID_i     ( s_axi_arid              ),
        .ARUSER_i   ( s_axi_aruser            ),
        .ARREADY_o  ( s_axi_arready           ),

        .RVALID_o   ( s_axi_rvalid            ),
        .RDATA_o    ( s_axi_rdata             ),
        .RRESP_o    ( s_axi_rresp             ),
        .RLAST_o    ( s_axi_rlast             ),
        .RID_o      ( s_axi_rid               ),
        .RUSER_o    ( s_axi_ruser             ),
        .RREADY_i   ( s_axi_rready            ),

        .WVALID_i   ( s_axi_wvalid            ),
        .WDATA_i    ( s_axi_wdata             ),
        .WSTRB_i    ( s_axi_wstrb             ),
        .WLAST_i    ( s_axi_wlast             ),
        .WUSER_i    ( s_axi_wuser             ),
        .WREADY_o   ( s_axi_wready            ),

        .BVALID_o   ( s_axi_bvalid            ),
        .BRESP_o    ( s_axi_bresp             ),
        .BID_o      ( s_axi_bid               ),
        .BUSER_o    ( s_axi_buser             ),
        .BREADY_i   ( s_axi_bready            ),

        .CEN        ( bram_chip_enb           ),
        .WEN        ( bram_write_enb          ),
        .A          ( bram_addr_a             ),
        .D          ( bram_wrdata_a           ),
        .BE         ( bram_bank_en            ),
        .Q          ( bram_rddata_a           ),

        .test_en_i  ( 1'b0                    )
    );

 endmodule
