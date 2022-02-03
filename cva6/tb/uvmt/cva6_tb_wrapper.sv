///////////////////////////////////////////////////////////////////////////////
//
// Copyright 2021 OpenHW Group
// Copyright 2021 Thales DIS Design Services SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//    https://solderpad.org/licenses/
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
//
///////////////////////////////////////////////////////////////////////////////
//
// CVA6 "core_only" testbench wrapper.
//
///////////////////////////////////////////////////////////////////////////////

module cva6_tb_wrapper #(
  parameter int unsigned AXI_USER_WIDTH    = 1,
  parameter int unsigned AXI_ADDRESS_WIDTH = 64,
  parameter int unsigned AXI_DATA_WIDTH    = 64,
  parameter int unsigned NUM_WORDS         = 2**25
) (
  input logic clk_i,
  input logic rst_ni,
  output wire tb_exit_o,
  output ariane_rvfi_pkg::rvfi_port_t  rvfi_o
);

  ariane_axi::req_t    axi_ariane_req;
  ariane_axi::resp_t   axi_ariane_resp;

  ariane_rvfi_pkg::rvfi_port_t  rvfi;
  assign rvfi_o = rvfi;

  ariane #(
    .ArianeCfg  ( ariane_soc::ArianeSocCfg )
  ) i_cva6 (
    .clk_i                ( clk_i                     ),
    .rst_ni               ( rst_ni                    ),
    .boot_addr_i          ( 64'h0000_0000_8000_0000   ), //ariane_soc::ROMBase
    .hart_id_i            ( 64'h0000_0000_0000_0000   ),
    .irq_i                ( 2'b00 /*irqs*/            ),
    .ipi_i                ( 1'b0  /*ipi*/             ),
    .time_irq_i           ( 1'b0  /*timer_irq*/       ),
    .debug_req_i          ( 1'b0                      ),
    .rvfi_o               ( rvfi                      ),
    .axi_req_o            ( axi_ariane_req            ),
    .axi_resp_i           ( axi_ariane_resp           )
  );

  //----------------------------------------------------------------------------
  // RVFI
  //----------------------------------------------------------------------------

  rvfi_tracer  #(
    .HART_ID(8'h0),
    .DEBUG_START(0),
    .DEBUG_STOP(0),
    .NR_COMMIT_PORTS(ariane_pkg::NR_COMMIT_PORTS)
  ) rvfi_tracer_i (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .rvfi_i(rvfi)
  ) ;

  //----------------------------------------------------------------------------
  // Memory
  //----------------------------------------------------------------------------

  logic                         req;
  logic                         we;
  logic [AXI_ADDRESS_WIDTH-1:0] addr;
  logic [AXI_DATA_WIDTH/8-1:0]  be;
  logic [AXI_DATA_WIDTH-1:0]    wdata;
  logic [AXI_DATA_WIDTH-1:0]    rdata;

  AXI_BUS #(
    .AXI_ADDR_WIDTH ( AXI_ADDRESS_WIDTH        ),
    .AXI_DATA_WIDTH ( AXI_DATA_WIDTH           ),
    .AXI_ID_WIDTH   ( ariane_soc::IdWidthSlave ),
    .AXI_USER_WIDTH ( AXI_USER_WIDTH           )
  ) cva6_axi_bus();

  axi_master_connect #(
  ) i_axi_master_connect_cva6_to_mem (
    .axi_req_i  (axi_ariane_req),
    .axi_resp_o (axi_ariane_resp),
    .master     (cva6_axi_bus)
  );

  axi2mem #(
    .AXI_ID_WIDTH   ( ariane_soc::IdWidthSlave ),
    .AXI_ADDR_WIDTH ( AXI_ADDRESS_WIDTH        ),
    .AXI_DATA_WIDTH ( AXI_DATA_WIDTH           ),
    .AXI_USER_WIDTH ( AXI_USER_WIDTH           )
  ) i_cva6_axi2mem (
    .clk_i  ( clk_i       ),
    .rst_ni ( rst_ni      ),
    .slave  ( cva6_axi_bus ),
    .req_o  ( req          ),
    .we_o   ( we           ),
    .addr_o ( addr         ),
    .be_o   ( be           ),
    .data_o ( wdata        ),
    .data_i ( rdata        )
  );

  cva6_core_tb_sram #(
    .DATA_WIDTH ( AXI_DATA_WIDTH ),
    .NUM_WORDS  ( NUM_WORDS      )
  ) i_cva6_core_tb_sram (
    .clk_i      ( clk_i                                                                      ),
    .rstn_i     ( rst_ni                                                                     ),
    .req_i      ( req                                                                         ),
    .we_i       ( we                                                                          ),
    .addr_i     ( addr[$clog2(NUM_WORDS)-1+$clog2(AXI_DATA_WIDTH/8):$clog2(AXI_DATA_WIDTH/8)] ),
    .wdata_i    ( wdata                                                                       ),
    .be_i       ( be                                                                          ),
    .rdata_o    ( rdata                                                                       )
    );

endmodule
