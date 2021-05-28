// Copyright 2014-2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Engineer:       Igor Loi - igor.loi@unibo.it
// Additional contributions by: Florian Zaruba - zarubaf@iis.ee.thz.ch
// Create Date:    01/02/2014
// Module Name:    axi_node_wrap_with_slices
// Project Name:   PULP
// Language:       SystemVerilog
//
// Description: Slice the interface ports to be AXI compliant
//
// Revision: Under version-control

module axi_node_wrap_with_slices #(
    parameter NB_MASTER          = 4,
    parameter NB_SLAVE           = 4,
    parameter NB_REGION          = 1,
    parameter AXI_ADDR_WIDTH     = 32,
    parameter AXI_DATA_WIDTH     = 32,
    parameter AXI_ID_WIDTH       = 10,
    parameter AXI_USER_WIDTH     = 0,
    parameter MASTER_SLICE_DEPTH = 1,
    parameter SLAVE_SLICE_DEPTH  = 1
)(
    input logic      clk,
    input logic      rst_n,
    input logic      test_en_i,
    AXI_BUS.Slave    slave  [NB_SLAVE-1:0],
    AXI_BUS.Master   master [NB_MASTER-1:0],
    // Memory map
    input  logic [NB_REGION-1:0][NB_MASTER-1:0][AXI_ADDR_WIDTH-1:0] start_addr_i,
    input  logic [NB_REGION-1:0][NB_MASTER-1:0][AXI_ADDR_WIDTH-1:0] end_addr_i,
    input  logic [NB_REGION-1:0][NB_MASTER-1:0]                     valid_rule_i
);
    localparam AXI_ID_OUT = AXI_ID_WIDTH + $clog2(NB_SLAVE);

    AXI_BUS #(
      .AXI_ADDR_WIDTH ( AXI_ADDR_WIDTH  ),
      .AXI_DATA_WIDTH ( AXI_DATA_WIDTH  ),
      .AXI_ID_WIDTH   ( AXI_ID_WIDTH    ),
      .AXI_USER_WIDTH ( AXI_USER_WIDTH  )
    ) axi_slave [NB_SLAVE-1:0]();

    AXI_BUS #(
       .AXI_ADDR_WIDTH ( AXI_ADDR_WIDTH ),
       .AXI_DATA_WIDTH ( AXI_DATA_WIDTH ),
       .AXI_ID_WIDTH   ( AXI_ID_OUT     ),
       .AXI_USER_WIDTH ( AXI_USER_WIDTH )
    ) axi_master [NB_MASTER-1:0]();

    axi_node_intf_wrap #(
        .NB_MASTER      ( NB_MASTER      ),
        .NB_SLAVE       ( NB_SLAVE       ),
        .NB_REGION      ( NB_REGION      ),
        .AXI_ADDR_WIDTH ( AXI_ADDR_WIDTH ),
        .AXI_DATA_WIDTH ( AXI_DATA_WIDTH ),
        .AXI_ID_WIDTH   ( AXI_ID_WIDTH   ),
        .AXI_USER_WIDTH ( AXI_USER_WIDTH )
    ) i_axi_node_intf_wrap (
        .clk            ( clk           ),
        .rst_n          ( rst_n         ),
        .test_en_i      ( test_en_i     ),
        .slave          ( axi_slave     ),
        .master         ( axi_master    ),
        .start_addr_i   ( start_addr_i  ),
        .end_addr_i     ( end_addr_i    ),
        .valid_rule_i   ( valid_rule_i  )
    );

    for (genvar i = 0; i < NB_MASTER; i++) begin : axi_slice_master_port
        axi_multicut #(
            .ADDR_WIDTH ( AXI_ADDR_WIDTH     ),
            .DATA_WIDTH ( AXI_DATA_WIDTH     ),
            .USER_WIDTH ( AXI_USER_WIDTH     ),
            .ID_WIDTH   ( AXI_ID_OUT         ),
            .NUM_CUTS   ( MASTER_SLICE_DEPTH )
        ) i_axi_slice_wrap_master (
            .clk_i      ( clk           ),
            .rst_ni     ( rst_n         ),
            .in         ( axi_master[i] ), // from the node
            .out        ( master[i]     )  // to IO ports
        );
    end

    for (genvar i = 0; i < NB_SLAVE; i++) begin : axi_slice_slave_port
        axi_multicut #(
            .ADDR_WIDTH ( AXI_ADDR_WIDTH    ),
            .DATA_WIDTH ( AXI_DATA_WIDTH    ),
            .USER_WIDTH ( AXI_USER_WIDTH    ),
            .ID_WIDTH   ( AXI_ID_WIDTH      ),
            .NUM_CUTS   ( SLAVE_SLICE_DEPTH )
        ) i_axi_slice_wrap_slave (
            .clk_i      ( clk           ),
            .rst_ni     ( rst_n         ),
            .in         ( slave[i]      ), // from IO_ports
            .out        ( axi_slave[i]  )  // to axi_node
        );
    end
endmodule
