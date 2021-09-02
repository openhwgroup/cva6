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
// Author: Luca Valente, University of Bologna
// Date: 18.06.2021
// Description: AlSaqr platform, it holds host_domain and cluster

`include "register_interface/typedef.svh"
`include "register_interface/assign.svh"
`include "alsaqr_periph_padframe/assign.svh"
`include "cluster_bus_defines.sv"
`include "pulp_soc_defines.sv"

module al_saqr 
  import axi_pkg::xbar_cfg_t;
  import apb_soc_pkg::NUM_GPIO;
  import udma_subsystem_pkg::*;
  import pkg_alsaqr_periph_padframe::*; 
#(
  parameter int unsigned AXI_USER_WIDTH    = 1,
  parameter int unsigned AXI_ADDRESS_WIDTH = 64,
  parameter int unsigned AXI_DATA_WIDTH    = 64,
`ifdef DROMAJO
  parameter bit          InclSimDTM        = 1'b0,
`else
  parameter bit          InclSimDTM        = 1'b1,
`endif
  parameter int unsigned NUM_WORDS         = 2**25,         // memory size
  parameter bit          StallRandomOutput = 1'b0,
  parameter bit          StallRandomInput  = 1'b0,
  parameter bit          JtagEnable        = 1'b1
) (
  input logic         rtc_i,
  input logic         rst_ni,
  inout wire [7:0]    pad_hyper_dq0,
  inout wire [7:0]    pad_hyper_dq1,
  inout wire          pad_hyper_ck,
  inout wire          pad_hyper_ckn,
  inout wire          pad_hyper_csn0,
  inout wire          pad_hyper_csn1,
  inout wire          pad_hyper_rwds0,
  inout wire          pad_hyper_rwds1,
  inout wire          pad_hyper_reset,
  inout wire [7:0]    pad_axi_hyper_dq0,
  inout wire [7:0]    pad_axi_hyper_dq1,
  inout wire          pad_axi_hyper_ck,
  inout wire          pad_axi_hyper_ckn,
  inout wire          pad_axi_hyper_csn0,
  inout wire          pad_axi_hyper_csn1,
  inout wire          pad_axi_hyper_rwds0,
  inout wire          pad_axi_hyper_rwds1,
  inout wire          pad_axi_hyper_reset,
  inout wire [63:0]   pad_gpio,
  // CVA6 DEBUG UART
  input logic         cva6_uart_rx_i,
  output logic        cva6_uart_tx_o,
  // FROM SimDTM
`ifndef TARGET_SYNTHESIS
  input logic         dmi_req_valid,
  output logic        dmi_req_ready,
  input logic [ 6:0]  dmi_req_bits_addr,
  input logic [ 1:0]  dmi_req_bits_op,
  input logic [31:0]  dmi_req_bits_data,
  output logic        dmi_resp_valid,
  input logic         dmi_resp_ready,
  output logic [ 1:0] dmi_resp_bits_resp,
  output logic [31:0] dmi_resp_bits_data, 
`endif
  // JTAG
  input logic         jtag_TCK,
  input logic         jtag_TMS,
  input logic         jtag_TDI,
  input logic         jtag_TRSTn,
  output logic        jtag_TDO_data,
  output logic        jtag_TDO_driven

);

      
  logic [1:0]                  s_hyper_cs_n;
  logic                        s_hyper_ck;
  logic                        s_hyper_ck_n;
  logic [1:0]                  s_hyper_rwds_o;
  logic                        s_hyper_rwds_i;
  logic [1:0]                  s_hyper_rwds_oe;
  logic [15:0]                 s_hyper_dq_i;
  logic [15:0]                 s_hyper_dq_o;
  logic [1:0]                  s_hyper_dq_oe;
  logic                        s_hyper_reset_n;
  logic [1:0]                  s_axi_hyper_cs_n;
  logic                        s_axi_hyper_ck;
  logic                        s_axi_hyper_ck_n;
  logic                        s_axi_hyper_rwds_o;
  logic                        s_axi_hyper_rwds_i;
  logic                        s_axi_hyper_rwds_oe;
  logic [7:0]                  s_axi_hyper_dq_i;
  logic [7:0]                  s_axi_hyper_dq_o;
  logic                        s_axi_hyper_dq_oe;
  logic                        s_axi_hyper_reset_n;

  logic [NUM_GPIO-1:0]         s_gpio_pad_in;
  logic [NUM_GPIO-1:0]         s_gpio_pad_out;
  logic [NUM_GPIO-1:0]         s_gpio_pad_dir;

  logic s_soc_clk  ;
  logic s_soc_rst_n; 
  logic s_cluster_clk  ;
  logic s_cluster_rst_n;

  AXI_BUS #(
     .AXI_ADDR_WIDTH ( AXI_ADDRESS_WIDTH        ),
     .AXI_DATA_WIDTH ( AXI_DATA_WIDTH           ),
     .AXI_ID_WIDTH   ( ariane_soc::IdWidthSlave ),
     .AXI_USER_WIDTH ( AXI_USER_WIDTH           )
  ) soc_to_cluster_axi_bus();
  AXI_BUS #(
     .AXI_ADDR_WIDTH ( AXI_ADDRESS_WIDTH               ),
     .AXI_DATA_WIDTH ( AXI_DATA_WIDTH                  ),
     .AXI_ID_WIDTH   ( ariane_soc::SocToClusterIdWidth ),
     .AXI_USER_WIDTH ( AXI_USER_WIDTH                  )
  ) serialized_soc_to_cluster_axi_bus();   
  AXI_BUS_ASYNC_GRAY #(
     .AXI_ADDR_WIDTH ( AXI_ADDRESS_WIDTH               ),
     .AXI_DATA_WIDTH ( AXI_DATA_WIDTH                  ),
     .AXI_ID_WIDTH   ( ariane_soc::SocToClusterIdWidth ),
     .AXI_USER_WIDTH ( AXI_USER_WIDTH                  ),
     .LOG_DEPTH      ( 3                               )
  ) async_soc_to_cluster_axi_bus();
  AXI_BUS #(
     .AXI_ADDR_WIDTH ( AXI_ADDRESS_WIDTH        ),
     .AXI_DATA_WIDTH ( AXI_DATA_WIDTH           ),
     .AXI_ID_WIDTH   ( ariane_soc::IdWidth      ),
     .AXI_USER_WIDTH ( AXI_USER_WIDTH           )
  ) cluster_to_soc_axi_bus();
  AXI_BUS_ASYNC_GRAY #(
     .AXI_ADDR_WIDTH ( AXI_ADDRESS_WIDTH        ),
     .AXI_DATA_WIDTH ( AXI_DATA_WIDTH           ),
     .AXI_ID_WIDTH   ( ariane_soc::IdWidth      ),
     .AXI_USER_WIDTH ( AXI_USER_WIDTH           ),
     .LOG_DEPTH      ( 3                        )
  ) async_cluster_to_soc_axi_bus();
   
  pad_to_hyper_t s_pad_to_hyper;
  hyper_to_pad_t s_hyper_to_pad;

  qspi_to_pad_t [N_SPI-1:0] s_qspi_to_pad;
  pad_to_qspi_t [N_SPI-1:0] s_pad_to_qspi;
  i2c_to_pad_t [N_I2C-1:0] s_i2c_to_pad;
  pad_to_i2c_t [N_I2C-1:0] s_pad_to_i2c;
  pad_to_cam_t [N_CAM-1:0] s_pad_to_cam;
  pad_to_uart_t [N_UART-1:0] s_pad_to_uart;
  uart_to_pad_t [N_UART-1:0] s_uart_to_pad;
  sdio_to_pad_t [N_SDIO-1:0] s_sdio_to_pad;
  pad_to_sdio_t [N_SDIO-1:0] s_pad_to_sdio;
  pwm_to_pad_t s_pwm_to_pad;
   

  static_connection_signals_pad2soc_t s_static_connection_signals_pad2soc;
  static_connection_signals_soc2pad_t s_static_connection_signals_soc2pad;
  port_signals_pad2soc_t              s_port_signals_pad2soc;
  port_signals_soc2pad_t              s_port_signals_soc2pad;
      
  localparam RegAw  = 32;
  localparam RegDw  = 32;

  typedef logic [RegAw-1:0]   reg_addr_t;
  typedef logic [RegDw-1:0]   reg_data_t;
  typedef logic [RegDw/8-1:0] reg_strb_t;

  `REG_BUS_TYPEDEF_REQ(reg_req_t, reg_addr_t, reg_data_t, reg_strb_t)
  `REG_BUS_TYPEDEF_RSP(reg_rsp_t, reg_data_t)
 
  reg_req_t   reg_req;
  reg_rsp_t   reg_rsp;

   REG_BUS #(
        .ADDR_WIDTH( RegAw ),
        .DATA_WIDTH( RegDw )
    ) i_padframecfg_rbus (
        .clk_i (s_soc_clk)
    ); 
      
    host_domain #(
        .NUM_WORDS         ( NUM_WORDS  ),
        .InclSimDTM        ( 1'b1       ),
        .StallRandomOutput ( 1'b1       ),
        .StallRandomInput  ( 1'b1       ),
        .NUM_GPIO          ( NUM_GPIO   ),
        .JtagEnable        ( JtagEnable )
    ) i_host_domain (
      .rst_ni,
      .rtc_i,
`ifndef TARGET_SYNTHESIS
      .dmi_req_valid,
      .dmi_req_ready,
      .dmi_req_bits_addr,
      .dmi_req_bits_op,
      .dmi_req_bits_data,
      .dmi_resp_valid,
      .dmi_resp_ready,
      .dmi_resp_bits_resp,
      .dmi_resp_bits_data, 
`else                                                                         
      .dmi_req_valid        ( '0 ), 
      .dmi_req_ready        (    ),
      .dmi_req_bits_addr    ( '0 ),
      .dmi_req_bits_op      ( '0 ),
      .dmi_req_bits_data    ( '0 ),
      .dmi_resp_valid       (    ),
      .dmi_resp_ready       ( '0 ),
      .dmi_resp_bits_resp   (    ),
      .dmi_resp_bits_data   (    ), 
`endif
      .jtag_TCK,
      .jtag_TMS,
      .jtag_TDI,
      .jtag_TRSTn,
      .jtag_TDO_data,
      .jtag_TDO_driven,
      .cluster_axi_master     ( soc_to_cluster_axi_bus          ),
      .cluster_axi_slave      ( cluster_to_soc_axi_bus          ),
      .soc_clk_o              ( s_soc_clk                       ),
      .soc_rst_no             ( s_soc_rst_n                     ),
      .rstn_cluster_sync_o    ( s_cluster_rst_n                 ),
      .clk_cluster_o          ( s_cluster_clk                   ),                 
      .padframecfg_reg_master ( i_padframecfg_rbus              ),
      .hyper_to_pad           ( s_hyper_to_pad                  ),
      .pad_to_hyper           ( s_pad_to_hyper                  ),    

      .qspi_to_pad            ( s_qspi_to_pad                   ),
      .pad_to_qspi            ( s_pad_to_qspi                   ),
      .i2c_to_pad             ( s_i2c_to_pad                    ),
      .pad_to_i2c             ( s_pad_to_i2c                    ),
  	  .pad_to_cam             ( s_pad_to_cam                    ),
      .pad_to_uart            ( s_pad_to_uart                   ),
      .uart_to_pad            ( s_uart_to_pad                   ),
      .sdio_to_pad            ( s_sdio_to_pad                   ),
      .pad_to_sdio            ( s_pad_to_sdio                   ),                     
                     
      .gpio_in                ( s_gpio_pad_in                    ),
      .gpio_out               ( s_gpio_pad_out                   ),
      .gpio_dir               ( s_gpio_pad_dir                   ),

      .cva6_uart_rx_i         ( cva6_uart_rx_i                   ),
      .cva6_uart_tx_o         ( cva6_uart_tx_o                   ),

      .pwm_to_pad             ( s_pwm_to_pad                     ),
 
      .axi_hyper_cs_no        ( s_axi_hyper_cs_n                 ),
      .axi_hyper_ck_o         ( s_axi_hyper_ck                   ),
      .axi_hyper_ck_no        ( s_axi_hyper_ck_n                 ),
      .axi_hyper_rwds_o       ( s_axi_hyper_rwds_o               ),
      .axi_hyper_rwds_i       ( s_axi_hyper_rwds_i               ),
      .axi_hyper_rwds_oe_o    ( s_axi_hyper_rwds_oe              ),
      .axi_hyper_dq_i         ( s_axi_hyper_dq_i                 ),
      .axi_hyper_dq_o         ( s_axi_hyper_dq_o                 ),
      .axi_hyper_dq_oe_o      ( s_axi_hyper_dq_oe                ),
      .axi_hyper_reset_no     ( s_axi_hyper_reset_n              )

    );

   assign s_hyper_dq_o[0] = s_hyper_to_pad.dq0_o;
   assign s_hyper_dq_o[1] = s_hyper_to_pad.dq1_o;
   assign s_hyper_dq_o[2] = s_hyper_to_pad.dq2_o;
   assign s_hyper_dq_o[3] = s_hyper_to_pad.dq3_o;
   assign s_hyper_dq_o[4] = s_hyper_to_pad.dq4_o;
   assign s_hyper_dq_o[5] = s_hyper_to_pad.dq5_o;
   assign s_hyper_dq_o[6] = s_hyper_to_pad.dq6_o;
   assign s_hyper_dq_o[7] = s_hyper_to_pad.dq7_o;
   
   assign s_hyper_cs_n[0]    = s_hyper_to_pad.cs0n_o;
   assign s_hyper_cs_n[1]    = s_hyper_to_pad.cs1n_o;
   assign s_hyper_rwds_o[0]  = s_hyper_to_pad.rwds_o;
   assign s_hyper_rwds_oe[0] = s_hyper_to_pad.rwds_oe_o;
   assign s_hyper_dq_oe      = s_hyper_to_pad.dq_oe_o;
   
   assign s_pad_to_hyper.dq0_i = s_hyper_dq_i[0];
   assign s_pad_to_hyper.dq1_i = s_hyper_dq_i[1];
   assign s_pad_to_hyper.dq2_i = s_hyper_dq_i[2];
   assign s_pad_to_hyper.dq3_i = s_hyper_dq_i[3];
   assign s_pad_to_hyper.dq4_i = s_hyper_dq_i[4];
   assign s_pad_to_hyper.dq5_i = s_hyper_dq_i[5];
   assign s_pad_to_hyper.dq6_i = s_hyper_dq_i[6];
   assign s_pad_to_hyper.dq7_i = s_hyper_dq_i[7];

   pad_frame #()
    i_pad_frame
      (       
      .hyper_cs_ni            ( s_hyper_cs_n                    ),
      .hyper_ck_i             ( s_hyper_to_pad.ck_o             ),
      .hyper_ck_ni            ( s_hyper_to_pad.ckn_o            ),
      .hyper_rwds_i           ( s_hyper_rwds_o                  ),
      .hyper_rwds_o           ( s_pad_to_hyper.rwds_i           ),
      .hyper_rwds_oe_i        ( s_hyper_rwds_oe                 ),
      .hyper_dq_o             ( s_hyper_dq_i                    ),
      .hyper_dq_i             ( s_hyper_dq_o                    ),
      .hyper_dq_oe_i          ( s_hyper_dq_oe                   ),
      .hyper_reset_ni         ( s_hyper_to_pad.resetn_o         ),

      .pad_hyper_dq0          ( pad_hyper_dq0                   ),
      .pad_hyper_dq1          ( pad_hyper_dq1                   ),
      .pad_hyper_ck           ( pad_hyper_ck                    ),
      .pad_hyper_ckn          ( pad_hyper_ckn                   ),
      .pad_hyper_csn0         ( pad_hyper_csn0                  ),
      .pad_hyper_csn1         ( pad_hyper_csn1                  ),
      .pad_hyper_rwds0        ( pad_hyper_rwds0                 ),
      .pad_hyper_rwds1        ( pad_hyper_rwds1                 ),
      .pad_hyper_reset        ( pad_hyper_reset                 ),

      .axi_hyper_cs_ni        ( s_axi_hyper_cs_n                ),
      .axi_hyper_ck_i         ( s_axi_hyper_ck                  ),
      .axi_hyper_ck_ni        ( s_axi_hyper_ck_n                ),
      .axi_hyper_rwds_i       ( s_axi_hyper_rwds_o              ),
      .axi_hyper_rwds_o       ( s_axi_hyper_rwds_i              ),
      .axi_hyper_rwds_oe_i    ( s_axi_hyper_rwds_oe             ),
      .axi_hyper_dq_o         ( s_axi_hyper_dq_i                ),
      .axi_hyper_dq_i         ( s_axi_hyper_dq_o                ),
      .axi_hyper_dq_oe_i      ( s_axi_hyper_dq_oe               ),
      .axi_hyper_reset_ni     ( s_axi_hyper_reset_n             ),

      .pad_axi_hyper_dq0      ( pad_axi_hyper_dq0               ),
      .pad_axi_hyper_dq1      ( pad_axi_hyper_dq1               ),
      .pad_axi_hyper_ck       ( pad_axi_hyper_ck                ),
      .pad_axi_hyper_ckn      ( pad_axi_hyper_ckn               ),
      .pad_axi_hyper_csn0     ( pad_axi_hyper_csn0              ),
      .pad_axi_hyper_csn1     ( pad_axi_hyper_csn1              ),
      .pad_axi_hyper_rwds0    ( pad_axi_hyper_rwds0             ),
      .pad_axi_hyper_rwds1    ( pad_axi_hyper_rwds1             ),
      .pad_axi_hyper_reset    ( pad_axi_hyper_reset             ),

      .gpio_pad_out           ( s_gpio_pad_out                  ),
      .gpio_pad_in            ( s_gpio_pad_in                   ),
      .gpio_pad_dir           ( s_gpio_pad_dir                  ),      
      .pad_gpio               ( pad_gpio                        )
     );

   axi_serializer_intf #(
     .AXI_ADDR_WIDTH ( AXI_ADDRESS_WIDTH        ),
     .AXI_DATA_WIDTH ( AXI_DATA_WIDTH           ),
     .AXI_ID_WIDTH   ( ariane_soc::IdWidthSlave ),
     .AXI_USER_WIDTH ( AXI_USER_WIDTH           ),
     .MAX_READ_TXNS  ( ariane_soc::NrSlaves     ),
     .MAX_WRITE_TXNS ( ariane_soc::NrSlaves     )
      ) (
        .clk_i  ( s_soc_clk                         ),
        .rst_ni ( s_soc_rst_n                       ),
        .slv    ( soc_to_cluster_axi_bus            ),
        .mst    ( serialized_soc_to_cluster_axi_bus )
      );

   axi_cdc_src_intf   #(
     .AXI_ADDR_WIDTH ( AXI_ADDRESS_WIDTH               ),
     .AXI_DATA_WIDTH ( AXI_DATA_WIDTH                  ),
     .AXI_ID_WIDTH   ( ariane_soc::SocToClusterIdWidth ),
     .AXI_USER_WIDTH ( AXI_USER_WIDTH                  ),
     .LOG_DEPTH      ( 3                               )
     ) soc_to_cluster_src_cdc_fifo_i 
       (
       .src_clk_i  ( s_soc_clk                         ),
       .src_rst_ni ( s_soc_rst_n                       ),
       .src        ( serialized_soc_to_cluster_axi_bus ),
       .dst        ( async_soc_to_cluster_axi_bus      )
       );
   
   axi_cdc_dst_intf   #(
     .AXI_ADDR_WIDTH ( AXI_ADDRESS_WIDTH        ),
     .AXI_DATA_WIDTH ( AXI_DATA_WIDTH           ),
     .AXI_ID_WIDTH   ( ariane_soc::IdWidth      ),
     .AXI_USER_WIDTH ( AXI_USER_WIDTH           ),
     .LOG_DEPTH      ( 3                        )
     ) soc_to_cluster_dst_cdc_fifo_i 
       (
       .dst_clk_i  ( s_soc_clk                    ),
       .dst_rst_ni ( s_soc_rst_n                  ),
       .src        ( async_cluster_to_soc_axi_bus ),
       .dst        ( cluster_to_soc_axi_bus       )
       );
   
    pulp_cluster
    #(
        .NB_CORES                     ( `NB_CORES                       ),
        .NB_HWPE_PORTS                ( 4                               ),
        .NB_DMAS                      ( `NB_DMAS                        ),
        .HWPE_PRESENT                 ( 0                               ),
        .TCDM_SIZE                    ( 64*2048                         ),
        .NB_TCDM_BANKS                ( 16                              ),
        .SET_ASSOCIATIVE              ( 4                               ),
        .CACHE_LINE                   ( 1                               ),
        .CACHE_SIZE                   ( 4096                            ),
        .ICACHE_DATA_WIDTH            ( 128                             ),
        .L0_BUFFER_FEATURE            ( "DISABLED"                      ),
        .MULTICAST_FEATURE            ( "DISABLED"                      ),
        .SHARED_ICACHE                ( "ENABLED"                       ),
        .DIRECT_MAPPED_FEATURE        ( "DISABLED"                      ),
        .L2_SIZE                      ( ariane_soc::L2SPMLength         ),
        .ROM_BOOT_ADDR                ( 32'h1A000000                    ),
        .BOOT_ADDR                    ( 32'hC0000000                    ),
        .INSTR_RDATA_WIDTH            ( 32                              ),
        .CLUST_FPU                    ( `CLUST_FPU                      ),
        .CLUST_FP_DIVSQRT             ( `CLUST_FP_DIVSQRT               ),
        .CLUST_SHARED_FP              ( `CLUST_SHARED_FP                ),
        .CLUST_SHARED_FP_DIVSQRT      ( `CLUST_SHARED_FP_DIVSQRT        ),
        .AXI_ADDR_WIDTH               ( AXI_ADDRESS_WIDTH               ),
        .AXI_DATA_IN_WIDTH            ( AXI_DATA_WIDTH                  ),
        .AXI_DATA_OUT_WIDTH           ( AXI_DATA_WIDTH                  ),
        .AXI_USER_WIDTH               ( AXI_USER_WIDTH                  ),
        .AXI_ID_IN_WIDTH              ( ariane_soc::SocToClusterIdWidth ),
        .AXI_ID_OUT_WIDTH             ( ariane_soc::IdWidth             ),
        .LOG_DEPTH                    ( 3                               ),
        .DATA_WIDTH                   ( 32                              ),
        .ADDR_WIDTH                   ( 32                              ),
        .LOG_CLUSTER                  ( 3                               ),
        .PE_ROUTING_LSB               ( 10                              ),
        .EVNT_WIDTH                   ( 8                               )
    )    
    cluster_i
    (
        .clk_i                        ( s_cluster_clk                ),
        .rst_ni                       ( s_cluster_rst_n              ),
        .ref_clk_i                    ( rtc_i                        ),

        .pmu_mem_pwdn_i               ( 1'b0                         ),
        
        .base_addr_i                  ( '0                           ),
        
        .dma_pe_evt_ack_i             ( '0                           ),
        .dma_pe_evt_valid_o           (                              ),
        .dma_pe_irq_ack_i             ( '0                           ),
        .dma_pe_irq_valid_o           (                              ),
        .dbg_irq_valid_i              ( '0                           ),
        .pf_evt_ack_i                 ( '0                           ),
        .pf_evt_valid_o               (                              ),
        .en_sa_boot_i                 ( 1'b0                         ),
        .test_mode_i                  ( 1'b0                         ),
        .fetch_en_i                   ( 1'b0                         ),
        .eoc_o                        (                              ),
        .busy_o                       (                              ),
        .cluster_id_i                 ( 6'b000000                    ),

        .async_cluster_events_wptr_i  ( '0  ),
        .async_cluster_events_rptr_o  (     ),
        .async_cluster_events_data_i  ( '0  ),

        .async_data_master_aw_wptr_o  ( async_cluster_to_soc_axi_bus.aw_wptr  ),
        .async_data_master_aw_rptr_i  ( async_cluster_to_soc_axi_bus.aw_rptr  ),
        .async_data_master_aw_data_o  ( async_cluster_to_soc_axi_bus.aw_data  ),
        .async_data_master_ar_wptr_o  ( async_cluster_to_soc_axi_bus.ar_wptr  ),
        .async_data_master_ar_rptr_i  ( async_cluster_to_soc_axi_bus.ar_rptr  ),
        .async_data_master_ar_data_o  ( async_cluster_to_soc_axi_bus.ar_data  ),
        .async_data_master_w_data_o   ( async_cluster_to_soc_axi_bus.w_data   ),
        .async_data_master_w_wptr_o   ( async_cluster_to_soc_axi_bus.w_wptr   ),
        .async_data_master_w_rptr_i   ( async_cluster_to_soc_axi_bus.w_rptr   ),
        .async_data_master_r_wptr_i   ( async_cluster_to_soc_axi_bus.r_wptr   ),
        .async_data_master_r_rptr_o   ( async_cluster_to_soc_axi_bus.r_rptr   ),
        .async_data_master_r_data_i   ( async_cluster_to_soc_axi_bus.r_data   ),
        .async_data_master_b_wptr_i   ( async_cluster_to_soc_axi_bus.b_wptr   ),
        .async_data_master_b_rptr_o   ( async_cluster_to_soc_axi_bus.b_rptr   ),
        .async_data_master_b_data_i   ( async_cluster_to_soc_axi_bus.b_data   ),

        .async_data_slave_aw_wptr_i   ( async_soc_to_cluster_axi_bus.aw_wptr  ),
        .async_data_slave_aw_rptr_o   ( async_soc_to_cluster_axi_bus.aw_rptr  ),
        .async_data_slave_aw_data_i   ( async_soc_to_cluster_axi_bus.aw_data  ),
        .async_data_slave_ar_wptr_i   ( async_soc_to_cluster_axi_bus.ar_wptr  ),
        .async_data_slave_ar_rptr_o   ( async_soc_to_cluster_axi_bus.ar_rptr  ),
        .async_data_slave_ar_data_i   ( async_soc_to_cluster_axi_bus.ar_data  ),
        .async_data_slave_w_data_i    ( async_soc_to_cluster_axi_bus.w_data   ),
        .async_data_slave_w_wptr_i    ( async_soc_to_cluster_axi_bus.w_wptr   ),
        .async_data_slave_w_rptr_o    ( async_soc_to_cluster_axi_bus.w_rptr   ),
        .async_data_slave_r_wptr_o    ( async_soc_to_cluster_axi_bus.r_wptr   ),
        .async_data_slave_r_rptr_i    ( async_soc_to_cluster_axi_bus.r_rptr   ),
        .async_data_slave_r_data_o    ( async_soc_to_cluster_axi_bus.r_data   ),
        .async_data_slave_b_wptr_o    ( async_soc_to_cluster_axi_bus.b_wptr   ),
        .async_data_slave_b_rptr_i    ( async_soc_to_cluster_axi_bus.b_rptr   ),
        .async_data_slave_b_data_o    ( async_soc_to_cluster_axi_bus.b_data   )
   );   
   
  `REG_BUS_ASSIGN_TO_REQ(reg_req,i_padframecfg_rbus)
  `REG_BUS_ASSIGN_FROM_RSP(i_padframecfg_rbus,reg_rsp)

   alsaqr_periph_padframe #(
            .AW     ( 32        ),
            .DW     ( 32        ),
            .req_t  ( reg_req_t ),
            .resp_t ( reg_rsp_t )
            )
   i_alsaqr_periph_padframe
     (
      .clk_i          ( s_soc_clk   ),
      .rst_ni         ( s_soc_rst_n ),
      .static_connection_signals_pad2soc(s_static_connection_signals_pad2soc),
      .static_connection_signals_soc2pad(s_static_connection_signals_soc2pad),
      .port_signals_pad2soc(s_port_signals_pad2soc),
      .port_signals_soc2pad(s_port_signals_soc2pad),
      .config_req_i   ( reg_req     ),
      .config_rsp_o   ( reg_rsp     )      
      );

   `ASSIGN_PERIPHS_I2C0_PAD2SOC(s_pad_to_i2c[0],s_port_signals_pad2soc.periphs.i2c0)
   `ASSIGN_PERIPHS_I2C0_SOC2PAD(s_port_signals_soc2pad.periphs.i2c0,s_i2c_to_pad[0])
   `ASSIGN_PERIPHS_I2C1_PAD2SOC(s_pad_to_i2c[1],s_port_signals_pad2soc.periphs.i2c1)
   `ASSIGN_PERIPHS_I2C1_SOC2PAD(s_port_signals_soc2pad.periphs.i2c1,s_i2c_to_pad[1])
   `ASSIGN_PERIPHS_I2C2_PAD2SOC(s_pad_to_i2c[2],s_port_signals_pad2soc.periphs.i2c2)
   `ASSIGN_PERIPHS_I2C2_SOC2PAD(s_port_signals_soc2pad.periphs.i2c2,s_i2c_to_pad[2])

   `ASSIGN_PERIPHS_SPI0_PAD2SOC(s_pad_to_qspi[0],s_port_signals_pad2soc.periphs.spi0)
   `ASSIGN_PERIPHS_SPI0_SOC2PAD(s_port_signals_soc2pad.periphs.spi0,s_qspi_to_pad[0])
   `ASSIGN_PERIPHS_SPI1_PAD2SOC(s_pad_to_qspi[1],s_port_signals_pad2soc.periphs.spi1)
   `ASSIGN_PERIPHS_SPI1_SOC2PAD(s_port_signals_soc2pad.periphs.spi1,s_qspi_to_pad[1])
   `ASSIGN_PERIPHS_SPI2_PAD2SOC(s_pad_to_qspi[2],s_port_signals_pad2soc.periphs.spi2)
   `ASSIGN_PERIPHS_SPI2_SOC2PAD(s_port_signals_soc2pad.periphs.spi2,s_qspi_to_pad[2])
   `ASSIGN_PERIPHS_SPI3_PAD2SOC(s_pad_to_qspi[3],s_port_signals_pad2soc.periphs.spi3)
   `ASSIGN_PERIPHS_SPI3_SOC2PAD(s_port_signals_soc2pad.periphs.spi3,s_qspi_to_pad[3])
   `ASSIGN_PERIPHS_SPI4_PAD2SOC(s_pad_to_qspi[4],s_port_signals_pad2soc.periphs.spi4)
   `ASSIGN_PERIPHS_SPI4_SOC2PAD(s_port_signals_soc2pad.periphs.spi4,s_qspi_to_pad[4])
   `ASSIGN_PERIPHS_SPI5_PAD2SOC(s_pad_to_qspi[5],s_port_signals_pad2soc.periphs.spi5)
   `ASSIGN_PERIPHS_SPI5_SOC2PAD(s_port_signals_soc2pad.periphs.spi5,s_qspi_to_pad[5])   
   `ASSIGN_PERIPHS_SPI6_PAD2SOC(s_pad_to_qspi[6],s_port_signals_pad2soc.periphs.spi6)
   `ASSIGN_PERIPHS_SPI6_SOC2PAD(s_port_signals_soc2pad.periphs.spi6,s_qspi_to_pad[6])
   
   `ASSIGN_PERIPHS_QSPI_PAD2SOC(s_pad_to_qspi[11],s_port_signals_pad2soc.periphs.qspi)
   `ASSIGN_PERIPHS_QSPI_SOC2PAD(s_port_signals_soc2pad.periphs.qspi,s_qspi_to_pad[11])

   `ASSIGN_PERIPHS_SDIO0_PAD2SOC(s_pad_to_sdio[0],s_port_signals_pad2soc.periphs.sdio0)
   `ASSIGN_PERIPHS_SDIO0_SOC2PAD(s_port_signals_soc2pad.periphs.sdio0,s_sdio_to_pad[0])

   `ASSIGN_PERIPHS_UART0_PAD2SOC(s_pad_to_uart[0],s_port_signals_pad2soc.periphs.uart0)
   `ASSIGN_PERIPHS_UART0_SOC2PAD(s_port_signals_soc2pad.periphs.uart0,s_uart_to_pad[0])
   `ASSIGN_PERIPHS_UART1_PAD2SOC(s_pad_to_uart[1],s_port_signals_pad2soc.periphs.uart1)
   `ASSIGN_PERIPHS_UART1_SOC2PAD(s_port_signals_soc2pad.periphs.uart1,s_uart_to_pad[1])

   
//   `ASSIGN_PERIPHS_UART_CF0_PAD2SOC(s_pad_to_uart[4],s_port_signals_pad2soc.periphs.uart_cf0)
//   `ASSIGN_PERIPHS_UART_CF0_SOC2PAD(s_port_signals_soc2pad.periphs.uart_cf0,s_uart_to_pad[4])
//   `ASSIGN_PERIPHS_UART_CF1_PAD2SOC(s_pad_to_uart[5],s_port_signals_pad2soc.periphs.uart_cf1)
//   `ASSIGN_PERIPHS_UART_CF1_SOC2PAD(s_port_signals_soc2pad.periphs.uart_cf1,s_uart_to_pad[5])
//   `ASSIGN_PERIPHS_UART_CF2_PAD2SOC(s_pad_to_uart[6],s_port_signals_pad2soc.periphs.uart_cf2)
//   `ASSIGN_PERIPHS_UART_CF2_SOC2PAD(s_port_signals_soc2pad.periphs.uart_cf2,s_uart_to_pad[6])
   
   `ASSIGN_PERIPHS_PWM_SOC2PAD(s_port_signals_soc2pad.periphs.pwm,s_pwm_to_pad)
     
   `ASSIGN_PERIPHS_SPI7_PAD2SOC(s_pad_to_qspi[7],s_port_signals_pad2soc.periphs.spi7)
   `ASSIGN_PERIPHS_SPI7_SOC2PAD(s_port_signals_soc2pad.periphs.spi7,s_qspi_to_pad[7])
   `ASSIGN_PERIPHS_SPI8_PAD2SOC(s_pad_to_qspi[8],s_port_signals_pad2soc.periphs.spi8)
   `ASSIGN_PERIPHS_SPI8_SOC2PAD(s_port_signals_soc2pad.periphs.spi8,s_qspi_to_pad[8])
   `ASSIGN_PERIPHS_SPI9_PAD2SOC(s_pad_to_qspi[9],s_port_signals_pad2soc.periphs.spi9)
   `ASSIGN_PERIPHS_SPI9_SOC2PAD(s_port_signals_soc2pad.periphs.spi9,s_qspi_to_pad[9])

   `ASSIGN_PERIPHS_I2C3_PAD2SOC(s_pad_to_i2c[3],s_port_signals_pad2soc.periphs.i2c3)
   `ASSIGN_PERIPHS_I2C3_SOC2PAD(s_port_signals_soc2pad.periphs.i2c3,s_i2c_to_pad[3])
 
   `ASSIGN_PERIPHS_CAM0_PAD2SOC(s_pad_to_cam[0],s_port_signals_pad2soc.periphs.cam0)

   `ASSIGN_PERIPHS_SPI10_PAD2SOC(s_pad_to_qspi[10],s_port_signals_pad2soc.periphs.spi10)
   `ASSIGN_PERIPHS_SPI10_SOC2PAD(s_port_signals_soc2pad.periphs.spi10,s_qspi_to_pad[10])

   `ASSIGN_PERIPHS_I2C4_PAD2SOC(s_pad_to_i2c[4],s_port_signals_pad2soc.periphs.i2c4)
   `ASSIGN_PERIPHS_I2C4_SOC2PAD(s_port_signals_soc2pad.periphs.i2c4,s_i2c_to_pad[4])

   `ASSIGN_PERIPHS_UART2_PAD2SOC(s_pad_to_uart[2],s_port_signals_pad2soc.periphs.uart2)
   `ASSIGN_PERIPHS_UART2_SOC2PAD(s_port_signals_soc2pad.periphs.uart2,s_uart_to_pad[2])
   `ASSIGN_PERIPHS_UART3_PAD2SOC(s_pad_to_uart[3],s_port_signals_pad2soc.periphs.uart3)
   `ASSIGN_PERIPHS_UART3_SOC2PAD(s_port_signals_soc2pad.periphs.uart3,s_uart_to_pad[3])
      
   `ASSIGN_PERIPHS_CAM1_PAD2SOC(s_pad_to_cam[1],s_port_signals_pad2soc.periphs.cam1)

//   `ASSIGN_PERIPHS_UART_CF3_PAD2SOC(s_pad_to_uart[7],s_port_signals_pad2soc.periphs.uart_cf3)
//   `ASSIGN_PERIPHS_UART_CF3_SOC2PAD(s_port_signals_soc2pad.periphs.uart_cf3,s_uart_to_pad[7])

   `ASSIGN_PERIPHS_SDIO1_PAD2SOC(s_pad_to_sdio[1],s_port_signals_pad2soc.periphs.sdio1)
   `ASSIGN_PERIPHS_SDIO1_SOC2PAD(s_port_signals_soc2pad.periphs.sdio1,s_sdio_to_pad[1])

endmodule
