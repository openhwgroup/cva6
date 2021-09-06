// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

`include "apb_macros.sv"

module periph_bus_wrap 
  import apb_soc_pkg::*;
#(
    parameter APB_ADDR_WIDTH = 32,
    parameter APB_DATA_WIDTH = 32
) (
    input logic    clk_i,
    input logic    rst_ni,
    APB_BUS.Slave  apb_slave,
    APB_BUS.Master udma_master,
    APB_BUS.Master gpio_master,
    APB_BUS.Master fll_master,
    APB_BUS.Master hyaxicfg_master,
    APB_BUS.Master advtimer_master,
    APB_BUS.Master padframe_master
);

    APB_BUS
    #(
        .APB_ADDR_WIDTH( APB_ADDR_WIDTH ),
        .APB_DATA_WIDTH( APB_DATA_WIDTH )
    )
    s_masters[apb_soc_pkg::NUM_APB_SLAVES-1:0]();

    APB_BUS #(
        .APB_ADDR_WIDTH ( APB_ADDR_WIDTH ),
        .APB_DATA_WIDTH ( APB_DATA_WIDTH )
    ) s_slave ();

    `APB_ASSIGN_SLAVE(s_slave, apb_slave);

    logic [apb_soc_pkg::NUM_APB_SLAVES-1:0][APB_ADDR_WIDTH-1:0] s_start_addr;
    logic [apb_soc_pkg::NUM_APB_SLAVES-1:0][APB_ADDR_WIDTH-1:0] s_end_addr;

    `APB_ASSIGN_MASTER(s_masters[0], fll_master);
    assign s_start_addr[0] = apb_soc_pkg::FLLBase;
    assign s_end_addr[0]   = apb_soc_pkg::FLLBase + apb_soc_pkg::FLLLength - 1;

    `APB_ASSIGN_MASTER(s_masters[1], gpio_master);
    assign s_start_addr[1] = apb_soc_pkg::GPIOSBase;
    assign s_end_addr[1]   = apb_soc_pkg::GPIOSBase + apb_soc_pkg::GPIOSLength - 1;

    `APB_ASSIGN_MASTER(s_masters[2], udma_master);
    assign s_start_addr[2] = apb_soc_pkg::UDMABase;
    assign s_end_addr[2]   = apb_soc_pkg::UDMABase + apb_soc_pkg::UDMALength - 1;
   
    `APB_ASSIGN_MASTER(s_masters[3], hyaxicfg_master);
    assign s_start_addr[3] = apb_soc_pkg::HYAXICFGBase;
    assign s_end_addr[3]   = apb_soc_pkg::HYAXICFGBase + apb_soc_pkg::HYAXICFGLength - 1 ;

    `APB_ASSIGN_MASTER(s_masters[4], advtimer_master);
    assign s_start_addr[4] = apb_soc_pkg::ADVTIMERBase;
    assign s_end_addr[4]   = apb_soc_pkg::ADVTIMERBase + apb_soc_pkg::ADVTIMERLength - 1 ;

    `APB_ASSIGN_MASTER(s_masters[5], padframe_master);
    assign s_start_addr[5] = apb_soc_pkg::PADFRAMEBase;
    assign s_end_addr[5]   = apb_soc_pkg::PADFRAMEBase + apb_soc_pkg::PADFRAMELength - 1 ;   
   
   apb_node_wrap #(
        .NB_MASTER      ( apb_soc_pkg::NUM_APB_SLAVES ),
        .APB_ADDR_WIDTH ( 32                          ),
        .APB_DATA_WIDTH ( 32                          )
    ) apb_node_wrap_i (
        .clk_i        ( clk_i        ),
        .rst_ni       ( rst_ni       ),

        .apb_slave    ( apb_slave    ),
        .apb_masters  ( s_masters    ),

        .start_addr_i ( s_start_addr ),
        .end_addr_i   ( s_end_addr   )
    );

endmodule
