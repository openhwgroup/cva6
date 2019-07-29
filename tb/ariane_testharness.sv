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

module ariane_testharness #(
  parameter int unsigned AXI_USER_WIDTH    = 1,
  parameter int unsigned AXI_ADDRESS_WIDTH = 64,
  parameter int unsigned AXI_DATA_WIDTH    = 64,
  parameter bit          InclSimDTM        = 1'b1,
  parameter int unsigned NUM_WORDS         = 2**25,         // memory size
  parameter bit          StallRandomOutput = 1'b0,
  parameter bit          StallRandomInput  = 1'b0
) (
  input  logic                           clk_i,
  input  logic                           rtc_i,
  input  logic                           rst_ni,
  output logic [31:0]                    exit_o
);

  // disable test-enable
  logic        test_en;
  logic        ndmreset;
  logic        ndmreset_n;

  int          jtag_enable;
  logic        init_done;

  assign test_en = 1'b0;

  AXI_BUS #(
    .AXI_ADDR_WIDTH ( AXI_ADDRESS_WIDTH   ),
    .AXI_DATA_WIDTH ( AXI_DATA_WIDTH      ),
    .AXI_ID_WIDTH   ( ariane_soc::IdWidth ),
    .AXI_USER_WIDTH ( AXI_USER_WIDTH      )
  ) slave();

  rstgen i_rstgen_main (
    .clk_i        ( clk_i                ),
    .rst_ni       ( rst_ni & (~ndmreset) ),
    .test_mode_i  ( test_en              ),
    .rst_no       ( ndmreset_n           ),
    .init_no      (                      ) // keep open
  );

  // ---------------
  // Debug
  // ---------------
  assign init_done = rst_ni;

  // ---------------
  // ROM
  // ---------------
  logic                         rom_req;
  logic [AXI_ADDRESS_WIDTH-1:0] rom_addr;
  logic [AXI_DATA_WIDTH-1:0]    rom_rdata;

  axi2mem #(
    .AXI_ID_WIDTH   ( ariane_soc::IdWidthSlave ),
    .AXI_ADDR_WIDTH ( AXI_ADDRESS_WIDTH        ),
    .AXI_DATA_WIDTH ( AXI_DATA_WIDTH           ),
    .AXI_USER_WIDTH ( AXI_USER_WIDTH           )
  ) i_axi2rom (
    .clk_i  ( clk_i                   ),
    .rst_ni ( ndmreset_n              ),
    .slave  ( slave                   ),
    .req_o  ( rom_req                 ),
    .we_o   (                         ),
    .addr_o ( rom_addr                ),
    .be_o   (                         ),
    .data_o (                         ),
    .data_i ( rom_rdata               )
  );

  bootrom i_bootrom (
    .clk_i      ( clk_i     ),
    .req_i      ( rom_req   ),
    .addr_i     ( rom_addr  ),
    .rdata_o    ( rom_rdata )
  );

  // ---------------
  // Core
  // ---------------
  ariane_axi::req_t    axi_ariane_req;
  ariane_axi::resp_t   axi_ariane_resp;

  ariane #(
    .ArianeCfg  ( ariane_soc::ArianeSocCfg )
  ) i_ariane (
    .clk_i                ( clk_i               ),
    .rst_ni               ( ndmreset_n          ),
    .boot_addr_i          ( 64'H80000000        ), // start fetching from ROM
    .hart_id_i            ( '0                  ),
    .irq_i                ( '0                  ),
    .ipi_i                ( '0                  ),
    .time_irq_i           ( '0                  ),

`ifdef RVFI
    .rvfi_valid     (),
    .rvfi_order     (),
    .rvfi_insn      (),
    .rvfi_insn_uncompressed (),
    .rvfi_trap      (),
    .rvfi_halt      (),
    .rvfi_intr      (),
    .rvfi_mode      (),
    .rvfi_rs1_addr  (),
    .rvfi_rs2_addr  (),
    .rvfi_rs1_rdata (),
    .rvfi_rs2_rdata (),
    .rvfi_rd_addr   (),
    .rvfi_rd_wdata  (),
    .rvfi_pc_rdata  (),
    .rvfi_pc_wdata  (),
    .rvfi_mem_addr  (),
    .rvfi_mem_rmask (),
    .rvfi_mem_wmask (),
    .rvfi_mem_rdata (),
    .rvfi_mem_wdata (),
`endif

`ifdef DII
    .flush_ctrl_if     (),
    .addr              (),
    .instr             (),
    .instruction_valid (),
`endif

    .debug_req_i          ( 1'b0                ),
    .axi_req_o            ( axi_ariane_req      ),
    .axi_resp_i           ( axi_ariane_resp     )
  );

  axi_master_connect i_axi_master_connect_ariane (
    .axi_req_i(axi_ariane_req),
    .axi_resp_o(axi_ariane_resp),
    .master(slave)
  );

endmodule
