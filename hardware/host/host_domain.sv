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
  parameter bit          StallRandomInput  = 1'b0
) (
  input  logic                           clk_i,
  input  logic                           rtc_i,
  input  logic                           rst_ni,
  output logic [31:0]                    exit_o
);

   localparam NB_L2_BANKS = 4;
   localparam AXI64_2_TCDM32_N_PORTS = 4; // Do not change, to achieve full bandwith from 64 bit AXI and 32 bit tcdm we need 4 ports!
                                          // It is hardcoded in the axi2tcdm_wrap module.
   localparam L2_BANK_SIZE = 32768 ; // 2^15 words (32 bits)
   localparam L2_BANK_ADDR_WIDTH = $clog2(L2_BANK_SIZE);
   localparam L2_DATA_WIDTH = 32 ; // Do not change

   logic                                 ndmreset_n;
   
   AXI_BUS #(
     .AXI_ADDR_WIDTH ( AXI_ADDRESS_WIDTH        ),
     .AXI_DATA_WIDTH ( AXI_DATA_WIDTH           ),
     .AXI_ID_WIDTH   ( ariane_soc::IdWidthSlave ),
     .AXI_USER_WIDTH ( AXI_USER_WIDTH           )
   ) l2_axi_bus();
 
   XBAR_TCDM_BUS axi_bridge_2_interconnect[AXI64_2_TCDM32_N_PORTS]();
 
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
        .rst_no ( ndmreset_n ),
        .l2_axi_master ( l2_axi_bus )
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
   
endmodule
