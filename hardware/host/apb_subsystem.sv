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

module apb_subsystem
  import apb_soc_pkg::*;
#( 
    parameter int unsigned AXI_USER_WIDTH = 1,
    parameter int unsigned AXI_ADDR_WIDTH = 64,
    parameter int unsigned AXI_DATA_WIDTH = 64,
    parameter int unsigned L2_ADDR_WIDTH  = 32, // L2 address space
    parameter int unsigned N_SPI          = 4,
    parameter int unsigned N_UART         = 4,
    parameter int unsigned CAM_DATA_WIDTH = 8,
    parameter int unsigned N_I2C          = 1,
    parameter int unsigned N_HYPER        = 1 
) (
    input  logic                       clk_i,
    input  logic                       rst_ni,
    AXI_BUS.Slave                      axi_apb_slave,
    XBAR_TCDM_BUS.Master               udma_tcdm_channels[1:0],
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

   APB_BUS  #(
               .APB_ADDR_WIDTH(32),
               .APB_DATA_WIDTH(32)
   ) apb_peripheral_bus();
  

   axi2apb_wrap #(
         .AXI_ADDR_WIDTH ( AXI_ADDR_WIDTH           ),
         .AXI_DATA_WIDTH ( AXI_DATA_WIDTH           ),
         .AXI_ID_WIDTH   ( ariane_soc::IdWidthSlave ),
         .AXI_USER_WIDTH ( AXI_USER_WIDTH           ),
         .APB_ADDR_WIDTH ( 32                       ),
         .APB_DATA_WIDTH ( 32                       )
         )(
           .clk_i,
           .rst_ni,
           .test_en_i (1'b0),
           
           .axi_slave(axi_apb_slave),
           .apb_master(apb_peripheral_bus)
         );
   
   udma_subsystem
     #(
        .L2_ADDR_WIDTH  ( L2_ADDR_WIDTH ), 
        .APB_ADDR_WIDTH ( 32            )  
     ) 
     (

         .events_o        (                               ),
         
         .event_valid_i   ( '0                            ),
         .event_data_i    ( '0                            ),
         .event_ready_o   (                               ),

         .dft_test_mode_i ( 1'b0                          ),
         .dft_cg_enable_i ( 1'b0                          ),

         .sys_clk_i       (clk_i                          ),
         .sys_resetn_i    (rst_ni                         ),
                                                          
         .periph_clk_i    ( clk_i                         ),

         .L2_ro_wen_o     ( udma_tcdm_channels[0].wen     ),
         .L2_ro_req_o     ( udma_tcdm_channels[0].req     ),
         .L2_ro_gnt_i     ( udma_tcdm_channels[0].gnt     ),
         .L2_ro_addr_o    ( udma_tcdm_channels[0].add     ),
         .L2_ro_be_o      ( udma_tcdm_channels[0].be      ),
         .L2_ro_wdata_o   ( udma_tcdm_channels[0].wdata   ),
         .L2_ro_rvalid_i  ( udma_tcdm_channels[0].r_valid ),
         .L2_ro_rdata_i   ( udma_tcdm_channels[0].r_rdata ),

         .L2_wo_wen_o     ( udma_tcdm_channels[1].wen      ),
         .L2_wo_req_o     ( udma_tcdm_channels[1].req      ),
         .L2_wo_gnt_i     ( udma_tcdm_channels[1].gnt      ),
         .L2_wo_addr_o    ( udma_tcdm_channels[1].add      ),
         .L2_wo_wdata_o   ( udma_tcdm_channels[1].wdata    ),
         .L2_wo_be_o      ( udma_tcdm_channels[1].be       ),
         .L2_wo_rvalid_i  ( udma_tcdm_channels[1].r_valid  ),
         .L2_wo_rdata_i   ( udma_tcdm_channels[1].r_rdata  ),

         .udma_apb_paddr  ( apb_peripheral_bus.paddr       ),
         .udma_apb_pwdata ( apb_peripheral_bus.pwdata      ),
         .udma_apb_pwrite ( apb_peripheral_bus.pwrite      ),
         .udma_apb_psel   ( apb_peripheral_bus.psel        ),
         .udma_apb_penable( apb_peripheral_bus.penable     ),
         .udma_apb_prdata ( apb_peripheral_bus.prdata      ),
         .udma_apb_pready ( apb_peripheral_bus.pready      ),
         .udma_apb_pslverr( apb_peripheral_bus.pslverr     ),
        
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
