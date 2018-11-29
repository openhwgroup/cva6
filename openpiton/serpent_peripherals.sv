// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Michael Schaffner <schaffner@iis.ee.ethz.ch>, ETH Zurich
// Date: 14.11.2018
// Description: Ariane chipset for OpenPiton that includes the bootrom (with DTB),
// debug module, clint and plic.
//
// Note that direct system bus accesses are not yet possible due to a missing
// AXI-lite br_master <-> NOC converter module.
//
// The address bases for the individual peripherals are defined in the
// devices.xml file in OpenPiton, and should be set to
//
// Debug    40'h90_0000_0000 <length 0x1000>
// Boot Rom 40'h90_0001_0000 <length 0x10000>
// CLINT    40'h90_0200_0000 <length 0x1000000>
// PLIC     40'h90_0300_0000 <length 0x1000000>
//

module serpent_peripherals #(
    parameter int unsigned DataWidth      = 64,
    parameter int unsigned NumHarts       =  1,
    parameter int unsigned NumSources     =  1,
    parameter bit          SwapEndianess  =  0
) (
    input                               clk_i,
    input                               rst_ni,
    input                               testmode_i,
    // connections to OpenPiton NoC filters
    // Debug/JTAG
    input  [DataWidth-1:0]              buf_ariane_debug_noc2_data_i,
    input                               buf_ariane_debug_noc2_valid_i,
    output                              ariane_debug_buf_noc2_ready_o,
    output [DataWidth-1:0]              ariane_debug_buf_noc3_data_o,
    output                              ariane_debug_buf_noc3_valid_o,
    input                               buf_ariane_debug_noc3_ready_i,
    // Bootrom
    input  [DataWidth-1:0]              buf_ariane_bootrom_noc2_data_i,
    input                               buf_ariane_bootrom_noc2_valid_i,
    output                              ariane_bootrom_buf_noc2_ready_o,
    output [DataWidth-1:0]              ariane_bootrom_buf_noc3_data_o,
    output                              ariane_bootrom_buf_noc3_valid_o,
    input                               buf_ariane_bootrom_noc3_ready_i,
    // CLINT
    input  [DataWidth-1:0]              buf_ariane_clint_noc2_data_i,
    input                               buf_ariane_clint_noc2_valid_i,
    output                              ariane_clint_buf_noc2_ready_o,
    output [DataWidth-1:0]              ariane_clint_buf_noc3_data_o,
    output                              ariane_clint_buf_noc3_valid_o,
    input                               buf_ariane_clint_noc3_ready_i,
    // PLIC
    input [DataWidth-1:0]               buf_ariane_plic_noc2_data_i,
    input                               buf_ariane_plic_noc2_valid_i,
    output                              ariane_plic_buf_noc2_ready_o,
    output [DataWidth-1:0]              ariane_plic_buf_noc3_data_o,
    output                              ariane_plic_buf_noc3_valid_o,
    input                               buf_ariane_plic_noc3_ready_i,
    // Debug sigs to cores
    output                              ndmreset_o,    // non-debug module reset
    output                              dmactive_o,    // debug module is active
    output [NumHarts-1:0]               debug_req_o,   // async debug request
    input  [NumHarts-1:0]               unavailable_i, // communicate whether the hart is unavailable (e.g.: power down)
    // JTAG
    input                               tck_i,
    input                               tms_i,
    input                               trst_ni,
    input                               td_i,
    output                              td_o,
    output                              tdo_oe_o,
    // CLINT
    input                               rtc_i,        // Real-time clock in (usually 32.768 kHz)
    output [NumHarts-1:0]               timer_irq_o,  // Timer interrupts
    output [NumHarts-1:0]               ipi_o,        // software interrupt (a.k.a inter-process-interrupt)
    // PLIC
    // TODO
    input  [NumSources-1:0]             irq_sources_i,
    output [NumHarts-1:0][1:0]          irq_o         // level sensitive IR lines, mip & sip (async)
);

  localparam int unsigned AxiIdWidth    =  0;
  localparam int unsigned AxiAddrWidth  = 64;
  localparam int unsigned AxiDataWidth  = 64;
  localparam int unsigned AxiUserWidth  =  0;

  /////////////////////////////
  // Debug module and JTAG
  /////////////////////////////

  logic        jtag_req_valid;
  logic        debug_req_ready;
  logic        jtag_resp_ready;
  logic        jtag_resp_valid;

  dm::dmi_req_t  jtag_dmi_req;
  dm::dmi_resp_t debug_resp;

  dmi_jtag i_dmi_jtag (
    .clk_i                               ,
    .rst_ni                              ,
    .testmode_i                          ,
    .dmi_req_o        ( jtag_dmi_req    ),
    .dmi_req_valid_o  ( jtag_req_valid  ),
    .dmi_req_ready_i  ( debug_req_ready ),
    .dmi_resp_i       ( debug_resp      ),
    .dmi_resp_ready_o ( jtag_resp_ready ),
    .dmi_resp_valid_i ( jtag_resp_valid ),
    .dmi_rst_no       (                 ), // not connected
    .tck_i                               ,
    .tms_i                               ,
    .trst_ni                             ,
    .td_i                                ,
    .td_o                                ,
    .tdo_oe_o
  );

  ariane_axi::req_t    dm_axi_m_req,  dm_axi_s_req;
  ariane_axi::resp_t   dm_axi_m_resp, dm_axi_s_resp;

  // debug module
  dm_top #(
    // current implementation only supports 1 hart
    .NrHarts              ( NumHarts             ),
    .AxiIdWidth           ( AxiIdWidth           ),
    .AxiAddrWidth         ( AxiAddrWidth         ),
    .AxiDataWidth         ( AxiDataWidth         ),
    .AxiUserWidth         ( AxiUserWidth         )
  ) i_dm_top (
    .clk_i                                        ,
    .rst_ni                                       , // PoR
    .testmode_i                                   ,
    .ndmreset_o                                   ,
    .dmactive_o                                   , // active debug session
    .debug_req_o                                  ,
    .unavailable_i                                ,
    .axi_s_req_i          ( dm_axi_s_req         ),
    .axi_s_resp_o         ( dm_axi_s_resp        ),
    .axi_m_req_o          ( dm_axi_m_req         ),
    .axi_m_resp_i         ( dm_axi_m_resp        ),
    .dmi_rst_ni           ( rst_ni               ),
    .dmi_req_valid_i      ( jtag_req_valid       ),
    .dmi_req_ready_o      ( debug_req_ready      ),
    .dmi_req_i            ( jtag_dmi_req         ),
    .dmi_resp_valid_o     ( jtag_resp_valid      ),
    .dmi_resp_ready_i     ( jtag_resp_ready      ),
    .dmi_resp_o           ( debug_resp           )
  );

  noc_axilite_bridge #(
    .SLAVE_RESP_BYTEWIDTH   ( 8             ),
    .SWAP_ENDIANESS         ( SwapEndianess )
  ) i_debug_axilite_bridge (
    .clk                    ( clk_i                         ),
    .rst                    ( ~rst_ni                       ),
    // to/from NOC
    .splitter_bridge_val    ( buf_ariane_debug_noc2_valid_i ),
    .splitter_bridge_data   ( buf_ariane_debug_noc2_data_i  ),
    .bridge_splitter_rdy    ( ariane_debug_buf_noc2_ready_o ),
    .bridge_splitter_val    ( ariane_debug_buf_noc3_valid_o ),
    .bridge_splitter_data   ( ariane_debug_buf_noc3_data_o  ),
    .splitter_bridge_rdy    ( buf_ariane_debug_noc3_ready_i ),
    //axi lite signals
    //write address channel
    .m_axi_awaddr           ( dm_axi_s_req.aw.addr          ),
    .m_axi_awvalid          ( dm_axi_s_req.aw_valid         ),
    .m_axi_awready          ( dm_axi_s_resp.aw_ready        ),
    //write data channel
    .m_axi_wdata            ( dm_axi_s_req.w.data           ),
    .m_axi_wstrb            ( dm_axi_s_req.w.strb           ),
    .m_axi_wvalid           ( dm_axi_s_req.w_valid          ),
    .m_axi_wready           ( dm_axi_s_resp.w_ready         ),
    //read address channel
    .m_axi_araddr           ( dm_axi_s_req.ar.addr          ),
    .m_axi_arvalid          ( dm_axi_s_req.ar_valid         ),
    .m_axi_arready          ( dm_axi_s_resp.ar_ready        ),
    //read data channel
    .m_axi_rdata            ( dm_axi_s_resp.r.data          ),
    .m_axi_rresp            ( dm_axi_s_resp.r.resp          ),
    .m_axi_rvalid           ( dm_axi_s_resp.r_valid         ),
    .m_axi_rready           ( dm_axi_s_req.r_ready          ),
    //write response channel
    .m_axi_bresp            ( dm_axi_s_resp.b.resp          ),
    .m_axi_bvalid           ( dm_axi_s_resp.b_valid         ),
    .m_axi_bready           ( dm_axi_s_req.b_ready          )
  );

  // tie off system bus accesses (not supported yet due to
  // missing AXI-lite br_master <-> NOC converter)
  assign dm_axi_m_resp = '0;

  // tie off signals not used by AXI-lite
  assign dm_axi_s_req.aw.id     = '0;
  assign dm_axi_s_req.aw.len    = '0;
  assign dm_axi_s_req.aw.size   = 2'b11;// 8byte
  assign dm_axi_s_req.aw.burst  = '0;
  assign dm_axi_s_req.aw.lock   = '0;
  assign dm_axi_s_req.aw.cache  = '0;
  assign dm_axi_s_req.aw.prot   = '0;
  assign dm_axi_s_req.aw.qos    = '0;
  assign dm_axi_s_req.aw.region = '0;
  assign dm_axi_s_req.aw.atop   = '0;
  assign dm_axi_s_req.w.last    = 1'b1;
  assign dm_axi_s_req.ar.id     = '0;
  assign dm_axi_s_req.ar.len    = '0;
  assign dm_axi_s_req.ar.size   = 2'b11;// 8byte
  assign dm_axi_s_req.ar.burst  = '0;
  assign dm_axi_s_req.ar.lock   = '0;
  assign dm_axi_s_req.ar.cache  = '0;
  assign dm_axi_s_req.ar.prot   = '0;
  assign dm_axi_s_req.ar.qos    = '0;
  assign dm_axi_s_req.ar.region = '0;
  // assign dm_axi_s_resp.r.id     = '0;
  // assign dm_axi_s_resp.r.last   = 1'b1;
  // assign dm_axi_s_resp.b.id     = '0;

  /////////////////////////////
  // Bootrom
  /////////////////////////////

  logic                    rom_req;
  logic [AxiAddrWidth-1:0] rom_addr;
  logic [AxiDataWidth-1:0] rom_rdata;

  AXI_BUS #(
    .AXI_ID_WIDTH   ( AxiIdWidth   ),
    .AXI_ADDR_WIDTH ( AxiAddrWidth ),
    .AXI_DATA_WIDTH ( AxiDataWidth ),
    .AXI_USER_WIDTH ( AxiUserWidth )
  ) br_master();

  axi2mem #(
    .AXI_ID_WIDTH   ( AxiIdWidth    ),
    .AXI_ADDR_WIDTH ( AxiAddrWidth  ),
    .AXI_DATA_WIDTH ( AxiDataWidth  ),
    .AXI_USER_WIDTH ( AxiUserWidth  )
  ) i_axi2rom (
    .clk_i                ,
    .rst_ni               ,
    .slave  ( br_master  ),
    .req_o  ( rom_req    ),
    .we_o   (            ),
    .addr_o ( rom_addr   ),
    .be_o   (            ),
    .data_o (            ),
    .data_i ( rom_rdata  )
  );

  bootrom i_bootrom (
    .clk_i                   ,
    .req_i      ( rom_req   ),
    .addr_i     ( rom_addr  ),
    .rdata_o    ( rom_rdata )
  );

  noc_axilite_bridge #(
    .SLAVE_RESP_BYTEWIDTH   ( 8             ),
    .SWAP_ENDIANESS         ( SwapEndianess )
  ) i_bootrom_axilite_bridge (
    .clk                    ( clk_i                           ),
    .rst                    ( ~rst_ni                         ),
    // to/from NOC
    .splitter_bridge_val    ( buf_ariane_bootrom_noc2_valid_i ),
    .splitter_bridge_data   ( buf_ariane_bootrom_noc2_data_i  ),
    .bridge_splitter_rdy    ( ariane_bootrom_buf_noc2_ready_o ),
    .bridge_splitter_val    ( ariane_bootrom_buf_noc3_valid_o ),
    .bridge_splitter_data   ( ariane_bootrom_buf_noc3_data_o  ),
    .splitter_bridge_rdy    ( buf_ariane_bootrom_noc3_ready_i ),
    //axi lite signals
    //write address channel
    .m_axi_awaddr           ( br_master.aw_addr               ),
    .m_axi_awvalid          ( br_master.aw_valid              ),
    .m_axi_awready          ( br_master.aw_ready              ),
    //write data channel
    .m_axi_wdata            ( br_master.w_data                ),
    .m_axi_wstrb            ( br_master.w_strb                ),
    .m_axi_wvalid           ( br_master.w_valid               ),
    .m_axi_wready           ( br_master.w_ready               ),
    //read address channel
    .m_axi_araddr           ( br_master.ar_addr               ),
    .m_axi_arvalid          ( br_master.ar_valid              ),
    .m_axi_arready          ( br_master.ar_ready              ),
    //read data channel
    .m_axi_rdata            ( br_master.r_data                ),
    .m_axi_rresp            ( br_master.r_resp                ),
    .m_axi_rvalid           ( br_master.r_valid               ),
    .m_axi_rready           ( br_master.r_ready               ),
    //write response channel
    .m_axi_bresp            ( br_master.b_resp                ),
    .m_axi_bvalid           ( br_master.b_valid               ),
    .m_axi_bready           ( br_master.b_ready               )
  );

  // tie off signals not used by AXI-lite
  assign br_master.aw_id     = '0;
  assign br_master.aw_len    = '0;
  assign br_master.aw_size   = 2'b11;// 8byte
  assign br_master.aw_burst  = '0;
  assign br_master.aw_lock   = '0;
  assign br_master.aw_cache  = '0;
  assign br_master.aw_prot   = '0;
  assign br_master.aw_qos    = '0;
  assign br_master.aw_region = '0;
  assign br_master.w_last    = 1'b1;
  assign br_master.ar_id     = '0;
  assign br_master.ar_len    = '0;
  assign br_master.ar_size   = 2'b11;// 8byte
  assign br_master.ar_burst  = '0;
  assign br_master.ar_lock   = '0;
  assign br_master.ar_cache  = '0;
  assign br_master.ar_prot   = '0;
  assign br_master.ar_qos    = '0;
  assign br_master.ar_region = '0;
  // assign br_master.r_id      = '0;
  // assign br_master.r_last    = 1'b1;
  // assign br_master.b_id      = '0;

  /////////////////////////////
  // CLINT
  /////////////////////////////

  ariane_axi::req_t    clint_axi_req;
  ariane_axi::resp_t   clint_axi_resp;

  clint #(
      .AXI_ADDR_WIDTH ( AxiAddrWidth ),
      .AXI_DATA_WIDTH ( AxiDataWidth ),
      .AXI_ID_WIDTH   ( AxiIdWidth   ),
      .NR_CORES       ( NumHarts     )
  ) i_clint (
      .clk_i                         ,
      .rst_ni                        ,
      .testmode_i                    ,
      .axi_req_i   ( clint_axi_req  ),
      .axi_resp_o  ( clint_axi_resp ),
      .rtc_i                         ,
      .timer_irq_o                   ,
      .ipi_o
  );

  noc_axilite_bridge #(
    .SLAVE_RESP_BYTEWIDTH   ( 8             ),
    .SWAP_ENDIANESS         ( SwapEndianess )
  ) i_clint_axilite_bridge (
    .clk                    ( clk_i                         ),
    .rst                    ( ~rst_ni                       ),
    // to/from NOC
    .splitter_bridge_val    ( buf_ariane_clint_noc2_valid_i ),
    .splitter_bridge_data   ( buf_ariane_clint_noc2_data_i  ),
    .bridge_splitter_rdy    ( ariane_clint_buf_noc2_ready_o ),
    .bridge_splitter_val    ( ariane_clint_buf_noc3_valid_o ),
    .bridge_splitter_data   ( ariane_clint_buf_noc3_data_o  ),
    .splitter_bridge_rdy    ( buf_ariane_clint_noc3_ready_i ),
    //axi lite signals
    //write address channel
    .m_axi_awaddr           ( clint_axi_req.aw.addr         ),
    .m_axi_awvalid          ( clint_axi_req.aw_valid        ),
    .m_axi_awready          ( clint_axi_resp.aw_ready       ),
    //write data channel
    .m_axi_wdata            ( clint_axi_req.w.data          ),
    .m_axi_wstrb            ( clint_axi_req.w.strb          ),
    .m_axi_wvalid           ( clint_axi_req.w_valid         ),
    .m_axi_wready           ( clint_axi_resp.w_ready        ),
    //read address channel
    .m_axi_araddr           ( clint_axi_req.ar.addr         ),
    .m_axi_arvalid          ( clint_axi_req.ar_valid        ),
    .m_axi_arready          ( clint_axi_resp.ar_ready       ),
    //read data channel
    .m_axi_rdata            ( clint_axi_resp.r.data         ),
    .m_axi_rresp            ( clint_axi_resp.r.resp         ),
    .m_axi_rvalid           ( clint_axi_resp.r_valid        ),
    .m_axi_rready           ( clint_axi_req.r_ready         ),
    //write response channel
    .m_axi_bresp            ( clint_axi_resp.b.resp         ),
    .m_axi_bvalid           ( clint_axi_resp.b_valid        ),
    .m_axi_bready           ( clint_axi_req.b_ready         )
  );

  // tie off signals not used by AXI-lite
  assign clint_axi_req.aw.id     = '0;
  assign clint_axi_req.aw.len    = '0;
  assign clint_axi_req.aw.size   = 2'b11;// 8byte
  assign clint_axi_req.aw.burst  = '0;
  assign clint_axi_req.aw.lock   = '0;
  assign clint_axi_req.aw.cache  = '0;
  assign clint_axi_req.aw.prot   = '0;
  assign clint_axi_req.aw.qos    = '0;
  assign clint_axi_req.aw.region = '0;
  assign clint_axi_req.aw.atop   = '0;
  assign clint_axi_req.w.last    = 1'b1;
  assign clint_axi_req.ar.id     = '0;
  assign clint_axi_req.ar.len    = '0;
  assign clint_axi_req.ar.size   = 2'b11;// 8byte
  assign clint_axi_req.ar.burst  = '0;
  assign clint_axi_req.ar.lock   = '0;
  assign clint_axi_req.ar.cache  = '0;
  assign clint_axi_req.ar.prot   = '0;
  assign clint_axi_req.ar.qos    = '0;
  assign clint_axi_req.ar.region = '0;


  /////////////////////////////
  // PLIC
  /////////////////////////////

  AXI_BUS #(
    .AXI_ID_WIDTH   ( AxiIdWidth   ),
    .AXI_ADDR_WIDTH ( AxiAddrWidth ),
    .AXI_DATA_WIDTH ( AxiDataWidth ),
    .AXI_USER_WIDTH ( AxiUserWidth )
  ) plic_master();

  noc_axilite_bridge #(
   .SLAVE_RESP_BYTEWIDTH   ( 8             ),
   .SWAP_ENDIANESS         ( SwapEndianess )
  ) i_plic_axilite_bridge (
    .clk                    ( clk_i                        ),
    .rst                    ( ~rst_ni                      ),
    // to/from NOC
    .splitter_bridge_val    ( buf_ariane_plic_noc2_valid_i ),
    .splitter_bridge_data   ( buf_ariane_plic_noc2_data_i  ),
    .bridge_splitter_rdy    ( ariane_plic_buf_noc2_ready_o ),
    .bridge_splitter_val    ( ariane_plic_buf_noc3_valid_o ),
    .bridge_splitter_data   ( ariane_plic_buf_noc3_data_o  ),
    .splitter_bridge_rdy    ( buf_ariane_plic_noc3_ready_i ),
    //axi lite signals
    //write address channel
    //write address channel
    .m_axi_awaddr           ( plic_master.aw_addr               ),
    .m_axi_awvalid          ( plic_master.aw_valid              ),
    .m_axi_awready          ( plic_master.aw_ready              ),
    //write data channel
    .m_axi_wdata            ( plic_master.w_data                ),
    .m_axi_wstrb            ( plic_master.w_strb                ),
    .m_axi_wvalid           ( plic_master.w_valid               ),
    .m_axi_wready           ( plic_master.w_ready               ),
    //read address channel
    .m_axi_araddr           ( plic_master.ar_addr               ),
    .m_axi_arvalid          ( plic_master.ar_valid              ),
    .m_axi_arready          ( plic_master.ar_ready              ),
    //read data channel
    .m_axi_rdata            ( plic_master.r_data                ),
    .m_axi_rresp            ( plic_master.r_resp                ),
    .m_axi_rvalid           ( plic_master.r_valid               ),
    .m_axi_rready           ( plic_master.r_ready               ),
    //write response channel
    .m_axi_bresp            ( plic_master.b_resp                ),
    .m_axi_bvalid           ( plic_master.b_valid               ),
    .m_axi_bready           ( plic_master.b_ready               )
  );

  // tie off signals not used by AXI-lite
  assign plic_master.aw_id     = '0;
  assign plic_master.aw_len    = '0;
  assign plic_master.aw_size   = 2'b11;// 8byte
  assign plic_master.aw_burst  = '0;
  assign plic_master.aw_lock   = '0;
  assign plic_master.aw_cache  = '0;
  assign plic_master.aw_prot   = '0;
  assign plic_master.aw_qos    = '0;
  assign plic_master.aw_region = '0;
  assign plic_master.w_last    = 1'b1;
  assign plic_master.ar_id     = '0;
  assign plic_master.ar_len    = '0;
  assign plic_master.ar_size   = 2'b11;// 8byte
  assign plic_master.ar_burst  = '0;
  assign plic_master.ar_lock   = '0;
  assign plic_master.ar_cache  = '0;
  assign plic_master.ar_prot   = '0;
  assign plic_master.ar_qos    = '0;
  assign plic_master.ar_region = '0;

    REG_BUS #(
        .ADDR_WIDTH ( 32 ),
        .DATA_WIDTH ( 32 )
    ) reg_bus (clk_i);

    logic         plic_penable;
    logic         plic_pwrite;
    logic [31:0]  plic_paddr;
    logic         plic_psel;
    logic [31:0]  plic_pwdata;
    logic [31:0]  plic_prdata;
    logic         plic_pready;
    logic         plic_pslverr;

    axi2apb_64_32 #(
        .AXI4_ADDRESS_WIDTH ( AxiAddrWidth ),
        .AXI4_RDATA_WIDTH   ( AxiDataWidth ),
        .AXI4_WDATA_WIDTH   ( AxiDataWidth ),
        .AXI4_ID_WIDTH      ( AxiIdWidth   ),
        .AXI4_USER_WIDTH    ( AxiUserWidth ),
        .BUFF_DEPTH_SLAVE   ( 2            ),
        .APB_ADDR_WIDTH     ( 32           )
    ) i_axi2apb_64_32_plic (
        .ACLK      ( clk_i                 ),
        .ARESETn   ( rst_ni                ),
        .test_en_i ( testmode_i            ),
        .AWID_i    ( plic_master.aw_id     ),
        .AWADDR_i  ( plic_master.aw_addr   ),
        .AWLEN_i   ( plic_master.aw_len    ),
        .AWSIZE_i  ( plic_master.aw_size   ),
        .AWBURST_i ( plic_master.aw_burst  ),
        .AWLOCK_i  ( plic_master.aw_lock   ),
        .AWCACHE_i ( plic_master.aw_cache  ),
        .AWPROT_i  ( plic_master.aw_prot   ),
        .AWREGION_i( plic_master.aw_region ),
        .AWUSER_i  ( plic_master.aw_user   ),
        .AWQOS_i   ( plic_master.aw_qos    ),
        .AWVALID_i ( plic_master.aw_valid  ),
        .AWREADY_o ( plic_master.aw_ready  ),
        .WDATA_i   ( plic_master.w_data    ),
        .WSTRB_i   ( plic_master.w_strb    ),
        .WLAST_i   ( plic_master.w_last    ),
        .WUSER_i   ( plic_master.w_user    ),
        .WVALID_i  ( plic_master.w_valid   ),
        .WREADY_o  ( plic_master.w_ready   ),
        .BID_o     ( plic_master.b_id      ),
        .BRESP_o   ( plic_master.b_resp    ),
        .BVALID_o  ( plic_master.b_valid   ),
        .BUSER_o   ( plic_master.b_user    ),
        .BREADY_i  ( plic_master.b_ready   ),
        .ARID_i    ( plic_master.ar_id     ),
        .ARADDR_i  ( plic_master.ar_addr   ),
        .ARLEN_i   ( plic_master.ar_len    ),
        .ARSIZE_i  ( plic_master.ar_size   ),
        .ARBURST_i ( plic_master.ar_burst  ),
        .ARLOCK_i  ( plic_master.ar_lock   ),
        .ARCACHE_i ( plic_master.ar_cache  ),
        .ARPROT_i  ( plic_master.ar_prot   ),
        .ARREGION_i( plic_master.ar_region ),
        .ARUSER_i  ( plic_master.ar_user   ),
        .ARQOS_i   ( plic_master.ar_qos    ),
        .ARVALID_i ( plic_master.ar_valid  ),
        .ARREADY_o ( plic_master.ar_ready  ),
        .RID_o     ( plic_master.r_id      ),
        .RDATA_o   ( plic_master.r_data    ),
        .RRESP_o   ( plic_master.r_resp    ),
        .RLAST_o   ( plic_master.r_last    ),
        .RUSER_o   ( plic_master.r_user    ),
        .RVALID_o  ( plic_master.r_valid   ),
        .RREADY_i  ( plic_master.r_ready   ),
        .PENABLE   ( plic_penable   ),
        .PWRITE    ( plic_pwrite    ),
        .PADDR     ( plic_paddr     ),
        .PSEL      ( plic_psel      ),
        .PWDATA    ( plic_pwdata    ),
        .PRDATA    ( plic_prdata    ),
        .PREADY    ( plic_pready    ),
        .PSLVERR   ( plic_pslverr   )
    );

    apb_to_reg i_apb_to_reg (
        .clk_i                     ,
        .rst_ni                    ,
        .penable_i ( plic_penable ),
        .pwrite_i  ( plic_pwrite  ),
        .paddr_i   ( plic_paddr   ),
        .psel_i    ( plic_psel    ),
        .pwdata_i  ( plic_pwdata  ),
        .prdata_o  ( plic_prdata  ),
        .pready_o  ( plic_pready  ),
        .pslverr_o ( plic_pslverr ),
        .reg_o     ( reg_bus      )
    );

    plic #(
        .ADDR_WIDTH         ( 32                     ),
        .DATA_WIDTH         ( 32                     ),
        .ID_BITWIDTH        ( 3                      ), // TODO (zarubaf): Find propper width
        .PARAMETER_BITWIDTH ( 3                      ), // TODO (zarubaf): Find propper width
        .NUM_TARGETS        ( 2*NumHarts             ),
        .NUM_SOURCES        ( NumSources             )
    ) i_plic (
        .clk_i                                        ,
        .rst_ni                                       ,
        .irq_sources_i                                ,
        .eip_targets_o      ( irq_o                  ),
        .external_bus_io    ( reg_bus                )
);



endmodule

