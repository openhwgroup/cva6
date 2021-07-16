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

module al_saqr 
  import axi_pkg::xbar_cfg_t;
  import apb_soc_pkg::NUM_GPIO;  
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
  input logic         clk_i,
  input logic         rtc_i,
  input logic         rst_ni,
  output logic [31:0] exit_o,
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
  input logic         dmi_req_valid,
  output logic        dmi_req_ready,
  input logic [ 6:0]  dmi_req_bits_addr,
  input logic [ 1:0]  dmi_req_bits_op,
  input logic [31:0]  dmi_req_bits_data,
  output logic        dmi_resp_valid,
  input logic         dmi_resp_ready,
  output logic [ 1:0] dmi_resp_bits_resp,
  output logic [31:0] dmi_resp_bits_data,   
  // JTAG
  input  logic        jtag_TCK,
  input  logic        jtag_TMS,
  input  logic        jtag_TDI,
  input  logic        jtag_TRSTn,
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
  logic [1:0]                  s_axi_hyper_rwds_o;
  logic                        s_axi_hyper_rwds_i;
  logic [1:0]                  s_axi_hyper_rwds_oe;
  logic [15:0]                 s_axi_hyper_dq_i;
  logic [15:0]                 s_axi_hyper_dq_o;
  logic [1:0]                  s_axi_hyper_dq_oe;
  logic                        s_axi_hyper_reset_n;

  logic [NUM_GPIO-1:0]         s_gpio_pad_in;
  logic [NUM_GPIO-1:0]         s_gpio_pad_out;
  logic [NUM_GPIO-1:0]         s_gpio_pad_dir;
   
    host_domain #(
        .NUM_WORDS         ( NUM_WORDS  ),
        .InclSimDTM        ( 1'b1       ),
        .StallRandomOutput ( 1'b1       ),
        .StallRandomInput  ( 1'b1       ),
        .NUM_GPIO          ( NUM_GPIO   ),
        .JtagEnable        ( JtagEnable )
    ) i_host_domain (
      .clk_i,
      .rst_ni,
      .rtc_i,
      .exit_o,
      .dmi_req_valid,
      .dmi_req_ready,
      .dmi_req_bits_addr,
      .dmi_req_bits_op,
      .dmi_req_bits_data,
      .dmi_resp_valid,
      .dmi_resp_ready,
      .dmi_resp_bits_resp,
      .dmi_resp_bits_data,                                                                          
      .jtag_TCK,
      .jtag_TMS,
      .jtag_TDI,
      .jtag_TRSTn,
      .jtag_TDO_data,
      .jtag_TDO_driven,
      .hyper_cs_no            ( s_hyper_cs_n                    ),
      .hyper_ck_o             ( s_hyper_ck                      ),
      .hyper_ck_no            ( s_hyper_ck_n                    ),
      .hyper_rwds_o           ( s_hyper_rwds_o                  ),
      .hyper_rwds_i           ( s_hyper_rwds_i                  ),
      .hyper_rwds_oe_o        ( s_hyper_rwds_oe                 ),
      .hyper_dq_i             ( s_hyper_dq_i                    ),
      .hyper_dq_o             ( s_hyper_dq_o                    ),
      .hyper_dq_oe_o          ( s_hyper_dq_oe                   ),
      .hyper_reset_no         ( s_hyper_reset_n                 ),     

      .gpio_in                ( s_gpio_pad_in                    ),
      .gpio_out               ( s_gpio_pad_out                   ),
      .gpio_dir               ( s_gpio_pad_dir                   ),

      .cva6_uart_rx_i         ( cva6_uart_rx_i                   ),
      .cva6_uart_tx_o         ( cva6_uart_tx_o                   ),

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

   pad_frame #()
    i_pad_frame
      (       
      .hyper_cs_ni            ( s_hyper_cs_n                    ),
      .hyper_ck_i             ( s_hyper_ck                      ),
      .hyper_ck_ni            ( s_hyper_ck_n                    ),
      .hyper_rwds_i           ( s_hyper_rwds_o                  ),
      .hyper_rwds_o           ( s_hyper_rwds_i                  ),
      .hyper_rwds_oe_i        ( s_hyper_rwds_oe                 ),
      .hyper_dq_o             ( s_hyper_dq_i                    ),
      .hyper_dq_i             ( s_hyper_dq_o                    ),
      .hyper_dq_oe_i          ( s_hyper_dq_oe                   ),
      .hyper_reset_ni         ( s_hyper_reset_n                 ),

      .pad_hyper_dq0          ( pad_hyper_dq0                   ),
      .pad_hyper_dq1          ( pad_hyper_dq1                   ),
      .pad_hyper_ck           ( pad_hyper_ck                    ),
      .pad_hyper_ckn          ( pad_hyper_ckn                   ),
      .pad_hyper_csn0         ( pad_hyper_csn0                  ),
      .pad_hyper_csn1         ( pad_hyper_csn1                  ),
      .pad_hyper_rwds0        ( pad_hyper_rwds0                 ),
      .pad_hyper_rwds1        ( pad_hyper_rwds1                 ),
      .pad_hyper_reset        ( pad_hyper_reset                 ),

      .axi_hyper_cs_ni            ( s_axi_hyper_cs_n                    ),
      .axi_hyper_ck_i             ( s_axi_hyper_ck                      ),
      .axi_hyper_ck_ni            ( s_axi_hyper_ck_n                    ),
      .axi_hyper_rwds_i           ( s_axi_hyper_rwds_o                  ),
      .axi_hyper_rwds_o           ( s_axi_hyper_rwds_i                  ),
      .axi_hyper_rwds_oe_i        ( s_axi_hyper_rwds_oe                 ),
      .axi_hyper_dq_o             ( s_axi_hyper_dq_i                    ),
      .axi_hyper_dq_i             ( s_axi_hyper_dq_o                    ),
      .axi_hyper_dq_oe_i          ( s_axi_hyper_dq_oe                   ),
      .axi_hyper_reset_ni         ( s_axi_hyper_reset_n                 ),

      .pad_axi_hyper_dq0          ( pad_axi_hyper_dq0                   ),
      .pad_axi_hyper_dq1          ( pad_axi_hyper_dq1                   ),
      .pad_axi_hyper_ck           ( pad_axi_hyper_ck                    ),
      .pad_axi_hyper_ckn          ( pad_axi_hyper_ckn                   ),
      .pad_axi_hyper_csn0         ( pad_axi_hyper_csn0                  ),
      .pad_axi_hyper_csn1         ( pad_axi_hyper_csn1                  ),
      .pad_axi_hyper_rwds0        ( pad_axi_hyper_rwds0                 ),
      .pad_axi_hyper_rwds1        ( pad_axi_hyper_rwds1                 ),
      .pad_axi_hyper_reset        ( pad_axi_hyper_reset                 ),

      .gpio_pad_out           ( s_gpio_pad_out                  ),
      .gpio_pad_in            ( s_gpio_pad_in                   ),
      .gpio_pad_dir           ( s_gpio_pad_dir                  ),      
      .pad_gpio               ( pad_gpio                        )
     );
   
endmodule
