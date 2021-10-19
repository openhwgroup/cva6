///////////////////////////////////////////////////////////////////////////////
//
// Copyright 2021 OpenHW Group
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
// CVA6 "core_only" testbench.
//
///////////////////////////////////////////////////////////////////////////////

module cva6_core_only_tb #(
  parameter int unsigned AXI_USER_WIDTH    = 1,
  parameter int unsigned AXI_ADDRESS_WIDTH = 64,
  parameter int unsigned AXI_DATA_WIDTH    = 64,
  parameter int unsigned NUM_WORDS         = 2**25       // memory size
  //parameter int unsigned NUM_WORDS         = 2**10         // memory size
) (
  input  logic verilator_clk_i,
  input  logic verilator_rstn_i,
  output wire  tb_exit_o
);

  localparam CLK_REPORT_COUNT  =  100;
  localparam CLK_TIMEOUT_COUNT = 1000000;
  localparam CLK_PERIOD        =   10;
  localparam RESET_ASSERT_TIME =  123;

  reg     r_tb_clk;
  reg     r_tb_rstn;
  reg     r_tb_exit;
  integer clk_cntr;

  wire    tb_clk;
  wire    tb_rstn;

  //----------------------------------------------------------------------------
  // Core:
  //      The AXI REQ and RESP ports are implemented as structs which are
  //      defined in two packages:
  //            - package "ariane_axi" defined in core/include/ariane_axi_pkg.sv
  //            - package "axi_pkg"    defined in corev_apu/axi/src/axi_pkg.sv
  //      TODO: extract these package definitions into a single file that is
  //            completely independ of the RTL.
  //----------------------------------------------------------------------------
  ariane_axi::req_t    axi_ariane_req;
  ariane_axi::resp_t   axi_ariane_resp;

  typedef rvfi_pkg::rvfi_instr_t [ariane_pkg::NR_COMMIT_PORTS-1:0] rvfi_port_t;
  rvfi_port_t    rvfi;

  ariane #(
    .ArianeCfg  ( ariane_soc::ArianeSocCfg )
  ) i_cva6 (
    .clk_i                ( tb_clk                    ),
    .rst_ni               ( tb_rstn                   ),
    .boot_addr_i          ( 64'h0000_0000_8000_0000   ), //ariane_soc::ROMBase
    .hart_id_i            ( 64'h0000_0000_0000_0000   ), //seriously? 2**64 harts?!?
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
    .clk_i(tb_clk),
    .rst_ni(tb_rstn),
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
    .clk_i  ( tb_clk       ),
    .rst_ni ( tb_rstn      ),
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
    .clk_i      ( tb_clk                                                                      ),
    .rstn_i     ( tb_rstn                                                                     ),
    .req_i      ( req                                                                         ),
    .we_i       ( we                                                                          ),
    .addr_i     ( addr[$clog2(NUM_WORDS)-1+$clog2(AXI_DATA_WIDTH/8):$clog2(AXI_DATA_WIDTH/8)] ),
    .wdata_i    ( wdata                                                                       ),
    .be_i       ( be                                                                          ),
    .rdata_o    ( rdata                                                                       )
  );

///////////////////////////////////////////////////////////////////////////////
//
// Testbench control:
//   - clock and reset generation
//   - wavedumping
//   - simulator init
//
///////////////////////////////////////////////////////////////////////////////
`ifdef VERILATOR
  // testbench control for Verilator is handled in cva6_tb_verilator.cpp.
  assign tb_clk    = verilator_clk_i;
  assign tb_rstn   = verilator_rstn_i;
  assign tb_exit_o = 0;
`else  // VERILATOR
  assign tb_clk    = r_tb_clk;
  assign tb_rstn   = r_tb_rstn;
  assign tb_exit_o = r_tb_exit;

  initial begin
    // units, precision, suffix-string, minimum-field-width)
    $timeformat(-9, 3, "ns", 5);
    //$dumpfile("cva6_tb.vcd");
    //$dumpvars(0, cva6_tb);
    r_tb_clk    = 0;
    r_tb_rstn   = 0;
    r_tb_exit   = 0;
    fork
      begin
        #RESET_ASSERT_TIME;
        r_tb_rstn = 1;
        $display("%m @ %0t: Reset de-asserted", $time);
      end
      begin
        #(CLK_PERIOD/2) r_tb_clk = ~r_tb_clk;
        $display("%m @ %0t: Clock started", $time);
        forever #(CLK_PERIOD/2) r_tb_clk = ~r_tb_clk;
      end
    join
  end
`endif // VERILATOR

  always @(posedge tb_clk) begin
    if (!tb_rstn) begin
      clk_cntr  <= 0;
    end
    else begin
      clk_cntr++;
      if (!(clk_cntr%CLK_REPORT_COUNT)) begin
        $display("%m @ %0t: %0d clocks", $time, clk_cntr);
      end
      if (clk_cntr > (CLK_TIMEOUT_COUNT+2)) begin
        $display("%m @ %0t: FINISHED", $time);
        $finish;
      end
    end
  end

endmodule
