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
// Author: Florian Zaruba, ETH Zurich
// Date: 19.03.2017
// Description: Test-harness for Ariane
//              Instantiates an AXI-Bus and memories

module host_domain 
  import axi_pkg::xbar_cfg_t;
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
  parameter int unsigned N_SPI             = 4,
  parameter int unsigned N_UART            = 4,
  parameter int unsigned CAM_DATA_WIDTH    = 8,
  parameter int unsigned N_I2C             = 1
) (
  input  logic                           clk_i,
  input  logic                           rtc_i,
  input  logic                           rst_ni,
  output logic [31:0]                    exit_o,
   // SPIM
  output logic     [N_SPI-1:0]       spi_clk,
  output logic     [N_SPI-1:0] [3:0] spi_csn,
  output logic     [N_SPI-1:0] [3:0] spi_oen,
  output logic     [N_SPI-1:0] [3:0] spi_sdo,
  input  logic     [N_SPI-1:0] [3:0] spi_sdi,

  // I2C
  input  logic           [N_I2C-1:0] i2c_scl_i,
  output logic           [N_I2C-1:0] i2c_scl_o,
  output logic           [N_I2C-1:0] i2c_scl_oe,
  input  logic           [N_I2C-1:0] i2c_sda_i,
  output logic           [N_I2C-1:0] i2c_sda_o,
  output logic           [N_I2C-1:0] i2c_sda_oe,

  // CAM
  input  logic                       cam_clk_i,
  input  logic  [CAM_DATA_WIDTH-1:0] cam_data_i,
  input  logic                       cam_hsync_i,
  input  logic                       cam_vsync_i,

  // UART
  input  logic          [N_UART-1:0] uart_rx_i,
  output logic          [N_UART-1:0] uart_tx_o,

  // SDIO
  output logic                       sdio_clk_o,
  output logic                       sdio_cmd_o,
  input  logic                       sdio_cmd_i,
  output logic                       sdio_cmd_oen_o,
  output logic                 [3:0] sdio_data_o,
  input  logic                 [3:0] sdio_data_i,
  output logic                 [3:0] sdio_data_oen_o,
  
  // I2S
  input  logic                       i2s_slave_sd0_i,
  input  logic                       i2s_slave_sd1_i,
  input  logic                       i2s_slave_ws_i,
  output logic                       i2s_slave_ws_o,
  output logic                       i2s_slave_ws_oe,
  input  logic                       i2s_slave_sck_i,
  output logic                       i2s_slave_sck_o,
  output logic                       i2s_slave_sck_oe,

  // HYPERBUS
  output logic [1:0]                 hyper_cs_no,
  output logic                       hyper_ck_o,
  output logic                       hyper_ck_no,
  output logic [1:0]                 hyper_rwds_o,
  input  logic                       hyper_rwds_i,
  output logic [1:0]                 hyper_rwds_oe_o,
  input  logic [15:0]                hyper_dq_i,
  output logic [15:0]                hyper_dq_o,
  output logic [1:0]                 hyper_dq_oe_o,
  output logic                       hyper_reset_no
);

   // When changing these parameters, change the L2 size accordingly in ariane_soc_pkg
   localparam NB_L2_BANKS = 8;
   localparam L2_BANK_SIZE = 16384; // 2^15 words (32 bits)

   localparam L2_BANK_ADDR_WIDTH = $clog2(L2_BANK_SIZE);
   localparam L2_MEM_ADDR_WIDTH = $clog2(L2_BANK_SIZE * NB_L2_BANKS) - $clog2(NB_L2_BANKS); 
   localparam L2_DATA_WIDTH = 32 ; // Do not change

   localparam AXI64_2_TCDM32_N_PORTS = 4; // Do not change, to achieve full bandwith from 64 bit AXI and 32 bit tcdm we need 4 ports!
                                          // It is hardcoded in the axi2tcdm_wrap module.

   localparam NB_UDMA_TCDM_CHANNEL = 2;
   
   logic                                 ndmreset_n;
   
   AXI_BUS #(
     .AXI_ADDR_WIDTH ( AXI_ADDRESS_WIDTH        ),
     .AXI_DATA_WIDTH ( AXI_DATA_WIDTH           ),
     .AXI_ID_WIDTH   ( ariane_soc::IdWidthSlave ),
     .AXI_USER_WIDTH ( AXI_USER_WIDTH           )
   ) l2_axi_bus();
 
   AXI_BUS #(
     .AXI_ADDR_WIDTH ( AXI_ADDRESS_WIDTH        ),
     .AXI_DATA_WIDTH ( AXI_DATA_WIDTH           ),
     .AXI_ID_WIDTH   ( ariane_soc::IdWidthSlave ),
     .AXI_USER_WIDTH ( AXI_USER_WIDTH           )
   ) apb_axi_bus();

   
   XBAR_TCDM_BUS axi_bridge_2_interconnect[AXI64_2_TCDM32_N_PORTS]();
   XBAR_TCDM_BUS udma_tcdm_channels[NB_UDMA_TCDM_CHANNEL]();
   
 
   cva6_subsytem # (
        .NUM_WORDS         ( NUM_WORDS ),
        .InclSimDTM        ( 1'b1      ),
        .StallRandomOutput ( 1'b1      ),
        .StallRandomInput  ( 1'b1      )
   ) i_cva_subsystem (
        .clk_i,
        .rst_ni,
        .rtc_i,
        .exit_o,
        .rst_no         ( ndmreset_n  ),
        .l2_axi_master  ( l2_axi_bus  ),
        .apb_axi_master ( apb_axi_bus )
    );
   
   
    axi2tcdm_wrap #(
      .AXI_ID_WIDTH   ( ariane_soc::IdWidthSlave ),
      .AXI_USER_WIDTH ( AXI_USER_WIDTH           ),
      .AXI_ADDR_WIDTH ( AXI_ADDRESS_WIDTH        )
    ) i_axi2mem_l2 (
      .clk_i       ( clk_i                     ),
      .rst_ni      ( ndmreset_n                ),
      .test_en_i   ( test_en                   ),
      .axi_slave   ( l2_axi_bus                ),
      .tcdm_master ( axi_bridge_2_interconnect ),
      .busy_o      (                           )
    );


    l2_subsystem #(
      .NB_L2_BANKS        ( NB_L2_BANKS              ),
      .L2_BANK_SIZE       ( L2_BANK_SIZE             ), 
      .L2_BANK_ADDR_WIDTH ( L2_BANK_ADDR_WIDTH       ),
      .L2_DATA_WIDTH      ( L2_DATA_WIDTH            )                   
     ) i_l2_subsystem   (
      .clk_i                     ( clk_i                     ),
      .rst_ni                    ( ndmreset_n                ),
      .axi_bridge_2_interconnect ( axi_bridge_2_interconnect )
     );


      apb_subsystem #(
       .L2_ADDR_WIDTH  ( L2_MEM_ADDR_WIDTH        ),
       .AXI_ADDR_WIDTH ( AXI_ADDRESS_WIDTH        ),
       .AXI_DATA_WIDTH ( AXI_DATA_WIDTH           ),
       .AXI_USER_WIDTH ( AXI_USER_WIDTH           )
      ) (
      .clk_i                     ( clk_i                     ),
      .rst_ni                    ( ndmreset_n                ),
      .axi_apb_slave             ( apb_axi_bus               ),
      .udma_tcdm_channels        ( udma_tcdm_channels        ),

      .spi_clk         ( spi_clk_o                      ),
      .spi_csn         ( spi_csn_o                      ),
      .spi_oen         ( spi_oen_o                      ),
      .spi_sdo         ( spi_sdo_o                      ),
      .spi_sdi         ( spi_sdi_i                      ),
                                                   
      .sdio_clk_o      ( sdclk_o                        ),
      .sdio_cmd_o      ( sdcmd_o                        ),
      .sdio_cmd_i      ( sdcmd_i                        ),
      .sdio_cmd_oen_o  ( sdcmd_oen_o                    ),
      .sdio_data_o     ( sddata_o                       ),
      .sdio_data_i     ( sddata_i                       ),
      .sdio_data_oen_o ( sddata_oen_o                   ),
                                                   
      .cam_clk_i       ( cam_clk_i                      ),
      .cam_data_i      ( cam_data_i                     ),
      .cam_hsync_i     ( cam_hsync_i                    ),
      .cam_vsync_i     ( cam_vsync_i                    ),
                                                   
      .i2s_slave_sd0_i ( i2s_slave_sd0_i                ),
      .i2s_slave_sd1_i ( i2s_slave_sd1_i                ),
      .i2s_slave_ws_i  ( i2s_slave_ws_i                 ),
      .i2s_slave_ws_o  ( i2s_slave_ws_o                 ),
      .i2s_slave_ws_oe ( i2s_slave_ws_oe                ),
      .i2s_slave_sck_i ( i2s_slave_sck_i                ),
      .i2s_slave_sck_o ( i2s_slave_sck_o                ),
      .i2s_slave_sck_oe( i2s_slave_sck_oe               ),
                                                   
      .uart_rx_i       ( uart_rx                        ),
      .uart_tx_o       ( uart_tx                        ),
                                                   
      .i2c_scl_i       ( i2c_scl_i                      ),
      .i2c_scl_o       ( i2c_scl_o                      ),
      .i2c_scl_oe      ( i2c_scl_oe_o                   ),
      .i2c_sda_i       ( i2c_sda_i                      ),
      .i2c_sda_o       ( i2c_sda_o                      ),
      .i2c_sda_oe      ( i2c_sda_oe_o                   ),
                                                   
      .hyper_cs_no     ( hyper_cs_no                    ),
      .hyper_ck_o      ( hyper_ck_o                     ),
      .hyper_ck_no     ( hyper_ck_no                    ),
      .hyper_rwds_o    ( hyper_rwds_o                   ),
      .hyper_rwds_i    ( hyper_rwds_i                   ),
      .hyper_rwds_oe_o ( hyper_rwds_oe_o                ),
      .hyper_dq_i      ( hyper_dq_i                     ),
      .hyper_dq_o      ( hyper_dq_o                     ),
      .hyper_dq_oe_o   ( hyper_dq_oe_o                  ),
      .hyper_reset_no  ( hyper_reset_no                 )

      );
                     
   
endmodule
