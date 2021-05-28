// Copyright 2014-2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the “License”); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an “AS IS” BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

module axi_node_intf_wrap #(
    parameter NB_MASTER      = 4,
    parameter NB_SLAVE       = 4,
    parameter NB_REGION      = 1,
    parameter AXI_ADDR_WIDTH = 32,
    parameter AXI_DATA_WIDTH = 32,
    parameter AXI_ID_WIDTH   = 10,
    parameter AXI_USER_WIDTH = 0
  )(
    // Clock and Reset
    input logic clk,
    input logic rst_n,
    input logic test_en_i,

    AXI_BUS.Slave slave[NB_SLAVE-1:0],

    AXI_BUS.Master master[NB_MASTER-1:0],

    // Memory map
    input  logic [NB_REGION-1:0][NB_MASTER-1:0][AXI_ADDR_WIDTH-1:0]  start_addr_i,
    input  logic [NB_REGION-1:0][NB_MASTER-1:0][AXI_ADDR_WIDTH-1:0]  end_addr_i,
    input  logic [NB_REGION-1:0][NB_MASTER-1:0]                      valid_rule_i
  );

  localparam AXI_STRB_WIDTH = AXI_DATA_WIDTH/8;

  // AXI ID WIDTHs for master and slave IPS
  localparam AXI_ID_WIDTH_TARG =   AXI_ID_WIDTH;
  localparam AXI_ID_WIDTH_INIT =   AXI_ID_WIDTH_TARG + $clog2(NB_SLAVE);


  // Signals to slave periperhals
  logic [NB_MASTER-1:0][AXI_ID_WIDTH_INIT-1:0] s_master_aw_id;
  logic [NB_MASTER-1:0][AXI_ADDR_WIDTH-1:0]    s_master_aw_addr;
  logic [NB_MASTER-1:0][7:0]                   s_master_aw_len;
  logic [NB_MASTER-1:0][2:0]                   s_master_aw_size;
  logic [NB_MASTER-1:0][1:0]                   s_master_aw_burst;
  logic [NB_MASTER-1:0]                        s_master_aw_lock;
  logic [NB_MASTER-1:0][3:0]                   s_master_aw_cache;
  logic [NB_MASTER-1:0][2:0]                   s_master_aw_prot;
  logic [NB_MASTER-1:0][3:0]                   s_master_aw_region;
  logic [NB_MASTER-1:0][5:0]                   s_master_aw_atop;
  logic [NB_MASTER-1:0][AXI_USER_WIDTH-1:0]    s_master_aw_user;
  logic [NB_MASTER-1:0][3:0]                   s_master_aw_qos;
  logic [NB_MASTER-1:0]                        s_master_aw_valid;
  logic [NB_MASTER-1:0]                        s_master_aw_ready;

  logic [NB_MASTER-1:0][AXI_ID_WIDTH_INIT-1:0] s_master_ar_id;
  logic [NB_MASTER-1:0][AXI_ADDR_WIDTH-1:0]    s_master_ar_addr;
  logic [NB_MASTER-1:0][7:0]                   s_master_ar_len;
  logic [NB_MASTER-1:0][2:0]                   s_master_ar_size;
  logic [NB_MASTER-1:0][1:0]                   s_master_ar_burst;
  logic [NB_MASTER-1:0]                        s_master_ar_lock;
  logic [NB_MASTER-1:0][3:0]                   s_master_ar_cache;
  logic [NB_MASTER-1:0][2:0]                   s_master_ar_prot;
  logic [NB_MASTER-1:0][3:0]                   s_master_ar_region;
  logic [NB_MASTER-1:0][AXI_USER_WIDTH-1:0]    s_master_ar_user;
  logic [NB_MASTER-1:0][3:0]                   s_master_ar_qos;
  logic [NB_MASTER-1:0]                        s_master_ar_valid;
  logic [NB_MASTER-1:0]                        s_master_ar_ready;

  logic [NB_MASTER-1:0][AXI_DATA_WIDTH-1:0]    s_master_w_data;
  logic [NB_MASTER-1:0][AXI_STRB_WIDTH-1:0]    s_master_w_strb;
  logic [NB_MASTER-1:0]                        s_master_w_last;
  logic [NB_MASTER-1:0][AXI_USER_WIDTH-1:0]    s_master_w_user;
  logic [NB_MASTER-1:0]                        s_master_w_valid;
  logic [NB_MASTER-1:0]                        s_master_w_ready;

  logic [NB_MASTER-1:0][AXI_ID_WIDTH_INIT-1:0] s_master_b_id;
  logic [NB_MASTER-1:0][1:0]                   s_master_b_resp;
  logic [NB_MASTER-1:0]                        s_master_b_valid;
  logic [NB_MASTER-1:0][AXI_USER_WIDTH-1:0]    s_master_b_user;
  logic [NB_MASTER-1:0]                        s_master_b_ready;

  logic [NB_MASTER-1:0][AXI_ID_WIDTH_INIT-1:0] s_master_r_id;
  logic [NB_MASTER-1:0][AXI_DATA_WIDTH-1:0]    s_master_r_data;
  logic [NB_MASTER-1:0][1:0]                   s_master_r_resp;
  logic [NB_MASTER-1:0]                        s_master_r_last;
  logic [NB_MASTER-1:0][AXI_USER_WIDTH-1:0]    s_master_r_user;
  logic [NB_MASTER-1:0]                        s_master_r_valid;
  logic [NB_MASTER-1:0]                        s_master_r_ready;

  // Signals from AXI masters
  logic [NB_SLAVE-1:0][AXI_ID_WIDTH_TARG-1:0] s_slave_aw_id;
  logic [NB_SLAVE-1:0][AXI_ADDR_WIDTH-1:0]    s_slave_aw_addr;
  logic [NB_SLAVE-1:0][7:0]                   s_slave_aw_len;
  logic [NB_SLAVE-1:0][2:0]                   s_slave_aw_size;
  logic [NB_SLAVE-1:0][1:0]                   s_slave_aw_burst;
  logic [NB_SLAVE-1:0]                        s_slave_aw_lock;
  logic [NB_SLAVE-1:0][3:0]                   s_slave_aw_cache;
  logic [NB_SLAVE-1:0][2:0]                   s_slave_aw_prot;
  logic [NB_SLAVE-1:0][3:0]                   s_slave_aw_region;
  logic [NB_SLAVE-1:0][5:0]                   s_slave_aw_atop;
  logic [NB_SLAVE-1:0][AXI_USER_WIDTH-1:0]    s_slave_aw_user;
  logic [NB_SLAVE-1:0][3:0]                   s_slave_aw_qos;
  logic [NB_SLAVE-1:0]                        s_slave_aw_valid;
  logic [NB_SLAVE-1:0]                        s_slave_aw_ready;

  logic [NB_SLAVE-1:0][AXI_ID_WIDTH_TARG-1:0] s_slave_ar_id;
  logic [NB_SLAVE-1:0][AXI_ADDR_WIDTH-1:0]    s_slave_ar_addr;
  logic [NB_SLAVE-1:0][7:0]                   s_slave_ar_len;
  logic [NB_SLAVE-1:0][2:0]                   s_slave_ar_size;
  logic [NB_SLAVE-1:0][1:0]                   s_slave_ar_burst;
  logic [NB_SLAVE-1:0]                        s_slave_ar_lock;
  logic [NB_SLAVE-1:0][3:0]                   s_slave_ar_cache;
  logic [NB_SLAVE-1:0][2:0]                   s_slave_ar_prot;
  logic [NB_SLAVE-1:0][3:0]                   s_slave_ar_region;
  logic [NB_SLAVE-1:0][AXI_USER_WIDTH-1:0]    s_slave_ar_user;
  logic [NB_SLAVE-1:0][3:0]                   s_slave_ar_qos;
  logic [NB_SLAVE-1:0]                        s_slave_ar_valid;
  logic [NB_SLAVE-1:0]                        s_slave_ar_ready;

  logic [NB_SLAVE-1:0][AXI_DATA_WIDTH-1:0]    s_slave_w_data;
  logic [NB_SLAVE-1:0][AXI_STRB_WIDTH-1:0]    s_slave_w_strb;
  logic [NB_SLAVE-1:0]                        s_slave_w_last;
  logic [NB_SLAVE-1:0][AXI_USER_WIDTH-1:0]    s_slave_w_user;
  logic [NB_SLAVE-1:0]                        s_slave_w_valid;
  logic [NB_SLAVE-1:0]                        s_slave_w_ready;

  logic [NB_SLAVE-1:0][AXI_ID_WIDTH_TARG-1:0] s_slave_b_id;
  logic [NB_SLAVE-1:0][1:0]                   s_slave_b_resp;
  logic [NB_SLAVE-1:0]                        s_slave_b_valid;
  logic [NB_SLAVE-1:0][AXI_USER_WIDTH-1:0]    s_slave_b_user;
  logic [NB_SLAVE-1:0]                        s_slave_b_ready;

  logic [NB_SLAVE-1:0][AXI_ID_WIDTH_TARG-1:0] s_slave_r_id;
  logic [NB_SLAVE-1:0][AXI_DATA_WIDTH-1:0]    s_slave_r_data;
  logic [NB_SLAVE-1:0][1:0]                   s_slave_r_resp;
  logic [NB_SLAVE-1:0]                        s_slave_r_last;
  logic [NB_SLAVE-1:0][AXI_USER_WIDTH-1:0]    s_slave_r_user;
  logic [NB_SLAVE-1:0]                        s_slave_r_valid;
  logic [NB_SLAVE-1:0]                        s_slave_r_ready;

  generate
    genvar i;
    for(i = 0; i < NB_MASTER; i++)
    begin
      assign                        master[i].aw_id[AXI_ID_WIDTH_INIT-1:0] = s_master_aw_id[i];
      assign                        master[i].aw_addr                      = s_master_aw_addr[i];
      assign                        master[i].aw_len                       = s_master_aw_len[i];
      assign                        master[i].aw_size                      = s_master_aw_size[i];
      assign                        master[i].aw_burst                     = s_master_aw_burst[i];
      assign                        master[i].aw_lock                      = s_master_aw_lock[i];
      assign                        master[i].aw_cache                     = s_master_aw_cache[i];
      assign                        master[i].aw_prot                      = s_master_aw_prot[i];
      assign                        master[i].aw_region                    = s_master_aw_region[i];
      assign                        master[i].aw_atop                      = s_master_aw_atop[i];
      assign                        master[i].aw_user                      = s_master_aw_user[i];
      assign                        master[i].aw_qos                       = s_master_aw_qos[i];
      assign                        master[i].aw_valid                     = s_master_aw_valid[i];
      assign s_master_aw_ready[i] = master[i].aw_ready;

      assign                        master[i].ar_id[AXI_ID_WIDTH_INIT-1:0] = s_master_ar_id[i];
      assign                        master[i].ar_addr                      = s_master_ar_addr[i];
      assign                        master[i].ar_len                       = s_master_ar_len[i];
      assign                        master[i].ar_size                      = s_master_ar_size[i];
      assign                        master[i].ar_burst                     = s_master_ar_burst[i];
      assign                        master[i].ar_lock                      = s_master_ar_lock[i];
      assign                        master[i].ar_cache                     = s_master_ar_cache[i];
      assign                        master[i].ar_prot                      = s_master_ar_prot[i];
      assign                        master[i].ar_region                    = s_master_ar_region[i];
      assign                        master[i].ar_user                      = s_master_ar_user[i];
      assign                        master[i].ar_qos                       = s_master_ar_qos[i];
      assign                        master[i].ar_valid                     = s_master_ar_valid[i];
      assign s_master_ar_ready[i] = master[i].ar_ready;

      assign                        master[i].w_data  = s_master_w_data[i];
      assign                        master[i].w_strb  = s_master_w_strb[i];
      assign                        master[i].w_last  = s_master_w_last[i];
      assign                        master[i].w_user  = s_master_w_user[i];
      assign                        master[i].w_valid = s_master_w_valid[i];
      assign s_master_w_ready[i]  = master[i].w_ready;

      assign s_master_b_id[i]     = master[i].b_id[AXI_ID_WIDTH_INIT-1:0];
      assign s_master_b_resp[i]   = master[i].b_resp;
      assign s_master_b_valid[i]  = master[i].b_valid;
      assign s_master_b_user[i]   = master[i].b_user;
      assign                        master[i].b_ready = s_master_b_ready[i];

      assign s_master_r_id[i]     = master[i].r_id[AXI_ID_WIDTH_INIT-1:0];
      assign s_master_r_data[i]   = master[i].r_data;
      assign s_master_r_resp[i]   = master[i].r_resp;
      assign s_master_r_last[i]   = master[i].r_last;
      assign s_master_r_user[i]   = master[i].r_user;
      assign s_master_r_valid[i]  = master[i].r_valid;
      assign                        master[i].r_ready = s_master_r_ready[i];
    end
  endgenerate

  generate
    genvar j;
    for(j = 0; j < NB_SLAVE; j++)
    begin
      assign s_slave_aw_id[j]     = slave[j].aw_id[AXI_ID_WIDTH_TARG-1:0];
      assign s_slave_aw_addr[j]   = slave[j].aw_addr;
      assign s_slave_aw_len[j]    = slave[j].aw_len;
      assign s_slave_aw_size[j]   = slave[j].aw_size;
      assign s_slave_aw_burst[j]  = slave[j].aw_burst;
      assign s_slave_aw_lock[j]   = slave[j].aw_lock;
      assign s_slave_aw_cache[j]  = slave[j].aw_cache;
      assign s_slave_aw_prot[j]   = slave[j].aw_prot;
      assign s_slave_aw_region[j] = slave[j].aw_region;
      assign s_slave_aw_atop[j]   = slave[j].aw_atop;
      assign s_slave_aw_user[j]   = slave[j].aw_user;
      assign s_slave_aw_qos[j]    = slave[j].aw_qos;
      assign s_slave_aw_valid[j]  = slave[j].aw_valid;
      assign                        slave[j].aw_ready = s_slave_aw_ready[j];

      assign s_slave_ar_id[j]     = slave[j].ar_id[AXI_ID_WIDTH_TARG-1:0];
      assign s_slave_ar_addr[j]   = slave[j].ar_addr;
      assign s_slave_ar_len[j]    = slave[j].ar_len;
      assign s_slave_ar_size[j]   = slave[j].ar_size;
      assign s_slave_ar_burst[j]  = slave[j].ar_burst;
      assign s_slave_ar_lock[j]   = slave[j].ar_lock;
      assign s_slave_ar_cache[j]  = slave[j].ar_cache;
      assign s_slave_ar_prot[j]   = slave[j].ar_prot;
      assign s_slave_ar_region[j] = slave[j].ar_region;
      assign s_slave_ar_user[j]   = slave[j].ar_user;
      assign s_slave_ar_qos[j]    = slave[j].ar_qos;
      assign s_slave_ar_valid[j]  = slave[j].ar_valid;
      assign                        slave[j].ar_ready = s_slave_ar_ready[j];

      assign s_slave_w_data[j]    = slave[j].w_data;
      assign s_slave_w_strb[j]    = slave[j].w_strb;
      assign s_slave_w_last[j]    = slave[j].w_last;
      assign s_slave_w_user[j]    = slave[j].w_user;
      assign s_slave_w_valid[j]   = slave[j].w_valid;
      assign                        slave[j].w_ready = s_slave_w_ready[j];

      assign                        slave[j].b_id[AXI_ID_WIDTH_TARG-1:0] = s_slave_b_id[j];
      assign                        slave[j].b_resp                      = s_slave_b_resp[j];
      assign                        slave[j].b_valid                     = s_slave_b_valid[j];
      assign                        slave[j].b_user                      = s_slave_b_user[j];
      assign s_slave_b_ready[j]   = slave[j].b_ready;

      assign                        slave[j].r_id[AXI_ID_WIDTH_TARG-1:0] = s_slave_r_id[j];
      assign                        slave[j].r_data                      = s_slave_r_data[j];
      assign                        slave[j].r_resp                      = s_slave_r_resp[j];
      assign                        slave[j].r_last                      = s_slave_r_last[j];
      assign                        slave[j].r_user                      = s_slave_r_user[j];
      assign                        slave[j].r_valid                     = s_slave_r_valid[j];
      assign s_slave_r_ready[j]   = slave[j].r_ready;
    end
  endgenerate

  axi_node
  #(
    .AXI_ADDRESS_W      ( AXI_ADDR_WIDTH    ),
    .AXI_DATA_W         ( AXI_DATA_WIDTH    ),
    .N_MASTER_PORT      ( NB_MASTER         ),
    .N_SLAVE_PORT       ( NB_SLAVE          ),
    .AXI_ID_IN          ( AXI_ID_WIDTH_TARG ),
    .AXI_USER_W         ( AXI_USER_WIDTH    ),
    .N_REGION           ( NB_REGION         )
  )
  axi_node_i
  (
    .clk                    ( clk                ),
    .rst_n                  ( rst_n              ),
    .test_en_i              ( test_en_i          ),

    .slave_awid_i           ( s_slave_aw_id      ),
    .slave_awaddr_i         ( s_slave_aw_addr    ),
    .slave_awlen_i          ( s_slave_aw_len     ),
    .slave_awsize_i         ( s_slave_aw_size    ),
    .slave_awburst_i        ( s_slave_aw_burst   ),
    .slave_awlock_i         ( s_slave_aw_lock    ),
    .slave_awcache_i        ( s_slave_aw_cache   ),
    .slave_awprot_i         ( s_slave_aw_prot    ),
    .slave_awregion_i       ( s_slave_aw_region  ),
    .slave_awatop_i         ( s_slave_aw_atop    ),
    .slave_awqos_i          ( s_slave_aw_qos     ),
    .slave_awuser_i         ( s_slave_aw_user    ),
    .slave_awvalid_i        ( s_slave_aw_valid   ),
    .slave_awready_o        ( s_slave_aw_ready   ),

    .slave_wdata_i          ( s_slave_w_data     ),
    .slave_wstrb_i          ( s_slave_w_strb     ),
    .slave_wlast_i          ( s_slave_w_last     ),
    .slave_wuser_i          ( s_slave_w_user     ),
    .slave_wvalid_i         ( s_slave_w_valid    ),
    .slave_wready_o         ( s_slave_w_ready    ),

    .slave_bid_o            ( s_slave_b_id       ),
    .slave_bresp_o          ( s_slave_b_resp     ),
    .slave_buser_o          ( s_slave_b_user     ),
    .slave_bvalid_o         ( s_slave_b_valid    ),
    .slave_bready_i         ( s_slave_b_ready    ),

    .slave_arid_i           ( s_slave_ar_id      ),
    .slave_araddr_i         ( s_slave_ar_addr    ),
    .slave_arlen_i          ( s_slave_ar_len     ),
    .slave_arsize_i         ( s_slave_ar_size    ),
    .slave_arburst_i        ( s_slave_ar_burst   ),
    .slave_arlock_i         ( s_slave_ar_lock    ),
    .slave_arcache_i        ( s_slave_ar_cache   ),
    .slave_arprot_i         ( s_slave_ar_prot    ),
    .slave_arregion_i       ( s_slave_ar_region  ),
    .slave_aruser_i         ( s_slave_ar_user    ),
    .slave_arqos_i          ( s_slave_ar_qos     ),
    .slave_arvalid_i        ( s_slave_ar_valid   ),
    .slave_arready_o        ( s_slave_ar_ready   ),

    .slave_rid_o            ( s_slave_r_id       ),
    .slave_rdata_o          ( s_slave_r_data     ),
    .slave_rresp_o          ( s_slave_r_resp     ),
    .slave_rlast_o          ( s_slave_r_last     ),
    .slave_ruser_o          ( s_slave_r_user     ),
    .slave_rvalid_o         ( s_slave_r_valid    ),
    .slave_rready_i         ( s_slave_r_ready    ),

    .master_awid_o          ( s_master_aw_id     ),
    .master_awaddr_o        ( s_master_aw_addr   ),
    .master_awlen_o         ( s_master_aw_len    ),
    .master_awsize_o        ( s_master_aw_size   ),
    .master_awburst_o       ( s_master_aw_burst  ),
    .master_awlock_o        ( s_master_aw_lock   ),
    .master_awcache_o       ( s_master_aw_cache  ),
    .master_awprot_o        ( s_master_aw_prot   ),
    .master_awregion_o      ( s_master_aw_region ),
    .master_awatop_o        ( s_master_aw_atop   ),
    .master_awqos_o         ( s_master_aw_qos    ),
    .master_awuser_o        ( s_master_aw_user   ),
    .master_awvalid_o       ( s_master_aw_valid  ),
    .master_awready_i       ( s_master_aw_ready  ),

    .master_wdata_o         ( s_master_w_data    ),
    .master_wstrb_o         ( s_master_w_strb    ),
    .master_wlast_o         ( s_master_w_last    ),
    .master_wuser_o         ( s_master_w_user    ),
    .master_wvalid_o        ( s_master_w_valid   ),
    .master_wready_i        ( s_master_w_ready   ),

    .master_bid_i           ( s_master_b_id      ),
    .master_bresp_i         ( s_master_b_resp    ),
    .master_buser_i         ( s_master_b_user    ),
    .master_bvalid_i        ( s_master_b_valid   ),
    .master_bready_o        ( s_master_b_ready   ),

    .master_arid_o          ( s_master_ar_id     ),
    .master_araddr_o        ( s_master_ar_addr   ),
    .master_arlen_o         ( s_master_ar_len    ),
    .master_arsize_o        ( s_master_ar_size   ),
    .master_arburst_o       ( s_master_ar_burst  ),
    .master_arlock_o        ( s_master_ar_lock   ),
    .master_arcache_o       ( s_master_ar_cache  ),
    .master_arprot_o        ( s_master_ar_prot   ),
    .master_arregion_o      ( s_master_ar_region ),
    .master_aruser_o        ( s_master_ar_user   ),
    .master_arqos_o         ( s_master_ar_qos    ),
    .master_arvalid_o       ( s_master_ar_valid  ),
    .master_arready_i       ( s_master_ar_ready  ),

    .master_rid_i           ( s_master_r_id      ),
    .master_rdata_i         ( s_master_r_data    ),
    .master_rresp_i         ( s_master_r_resp    ),
    .master_rlast_i         ( s_master_r_last    ),
    .master_ruser_i         ( s_master_r_user    ),
    .master_rvalid_i        ( s_master_r_valid   ),
    .master_rready_o        ( s_master_r_ready   ),

    .cfg_START_ADDR_i       ( start_addr_i       ),
    .cfg_END_ADDR_i         ( end_addr_i         ),
    .cfg_valid_rule_i       ( valid_rule_i       ),
    .cfg_connectivity_map_i ( {NB_MASTER*NB_SLAVE{1'b1}} ) // required instead of '1 for Vivado
  );

endmodule
