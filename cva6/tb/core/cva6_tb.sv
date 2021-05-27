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
  localparam RESET_ASSERT_TIME = 1234;

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
  //            - package "ariane_axi_soc" defined in tb/ariane_axi_soc_pkg.sv
  //            - package "axi_pkg"        defined in src/axi/src/axi_pkg.sv
  //      TODO: extract these package definitions into a single file that is
  //            completely independ of the RTL.
  //----------------------------------------------------------------------------
  ariane_axi_soc::req_t    axi_ariane_req;
  ariane_axi_soc::resp_t   axi_ariane_resp;
  rvfi_pkg::rvfi_port_t    rvfi;

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

    .rvfi_valid_1         ( rvfi[1].valid             ),
    .rvfi_order_1         ( rvfi[1].order             ),
    .rvfi_insn_1          ( rvfi[1].insn              ),
    .rvfi_trap_1          ( rvfi[1].trap              ),
    .rvfi_halt_1          ( rvfi[1].halt              ),
    .rvfi_intr_1          ( rvfi[1].intr              ),
    .rvfi_mode_1          ( rvfi[1].mode              ),
    .rvfi_ixl_1           ( rvfi[1].ixl               ),
    .rvfi_rs1_addr_1      ( rvfi[1].rs1_addr          ),
    .rvfi_rs2_addr_1      ( rvfi[1].rs2_addr          ),
    .rvfi_rs1_rdata_1     ( rvfi[1].rs1_rdata         ),
    .rvfi_rs2_rdata_1     ( rvfi[1].rs2_rdata         ),
    .rvfi_rd_addr_1       ( rvfi[1].rd_addr           ),
    .rvfi_rd_wdata_1      ( rvfi[1].rd_wdata          ),
    .rvfi_pc_rdata_1      ( rvfi[1].pc_rdata          ),
    .rvfi_pc_wdata_1      ( rvfi[1].pc_wdata          ),
    .rvfi_mem_addr_1      ( rvfi[1].mem_addr          ),
    .rvfi_mem_rmask_1     ( rvfi[1].mem_rmask         ),
    .rvfi_mem_wmask_1     ( rvfi[1].mem_wmask         ),
    .rvfi_mem_rdata_1     ( rvfi[1].mem_rdata         ),
    .rvfi_mem_wdata_1     ( rvfi[1].mem_wdata         ),
    .rvfi_valid_0         ( rvfi[0].valid             ),
    .rvfi_order_0         ( rvfi[0].order             ),
    .rvfi_insn_0          ( rvfi[0].insn              ),
    .rvfi_trap_0          ( rvfi[0].trap              ),
    .rvfi_halt_0          ( rvfi[0].halt              ),
    .rvfi_intr_0          ( rvfi[0].intr              ),
    .rvfi_mode_0          ( rvfi[0].mode              ),
    .rvfi_ixl_0           ( rvfi[0].ixl               ),
    .rvfi_rs1_addr_0      ( rvfi[0].rs1_addr          ),
    .rvfi_rs2_addr_0      ( rvfi[0].rs2_addr          ),
    .rvfi_rs1_rdata_0     ( rvfi[0].rs1_rdata         ),
    .rvfi_rs2_rdata_0     ( rvfi[0].rs2_rdata         ),
    .rvfi_rd_addr_0       ( rvfi[0].rd_addr           ),
    .rvfi_rd_wdata_0      ( rvfi[0].rd_wdata          ),
    .rvfi_pc_rdata_0      ( rvfi[0].pc_rdata          ),
    .rvfi_pc_wdata_0      ( rvfi[0].pc_wdata          ),
    .rvfi_mem_addr_0      ( rvfi[0].mem_addr          ),
    .rvfi_mem_rmask_0     ( rvfi[0].mem_rmask         ),
    .rvfi_mem_wmask_0     ( rvfi[0].mem_wmask         ),
    .rvfi_mem_rdata_0     ( rvfi[0].mem_rdata         ),
    .rvfi_mem_wdata_0     ( rvfi[0].mem_wdata         ),

    .aw_id_o              ( axi_ariane_req.aw.id     ),
    .aw_addr_o            ( axi_ariane_req.aw.addr   ),
    .aw_len_o             ( axi_ariane_req.aw.len    ),
    .aw_size_o            ( axi_ariane_req.aw.size   ),
    .aw_burst_o           ( axi_ariane_req.aw.burst  ),
    .aw_lock_o            ( axi_ariane_req.aw.lock   ),
    .aw_cache_o           ( axi_ariane_req.aw.cache  ),
    .aw_prot_o            ( axi_ariane_req.aw.prot   ),
    .aw_qos_o             ( axi_ariane_req.aw.qos    ),
    .aw_region_o          ( axi_ariane_req.aw.region ),
    .aw_atop_o            ( axi_ariane_req.aw.atop   ),
    .aw_user_o            ( axi_ariane_req.aw.user   ),
    .aw_valid_o           ( axi_ariane_req.aw_valid  ),
    .w_data_o             ( axi_ariane_req.w.data    ),
    .w_strb_o             ( axi_ariane_req.w.strb    ),
    .w_last_o             ( axi_ariane_req.w.last    ),
    .w_user_o             ( axi_ariane_req.w.user    ),
    .w_valid_o            ( axi_ariane_req.w_valid   ),
    .b_ready_o            ( axi_ariane_req.b_ready   ),
    .ar_id_o              ( axi_ariane_req.ar.id     ),
    .ar_addr_o            ( axi_ariane_req.ar.addr   ),
    .ar_len_o             ( axi_ariane_req.ar.len    ),
    .ar_size_o            ( axi_ariane_req.ar.size   ),
    .ar_burst_o           ( axi_ariane_req.ar.burst  ),
    .ar_lock_o            ( axi_ariane_req.ar.lock   ),
    .ar_cache_o           ( axi_ariane_req.ar.cache  ),
    .ar_prot_o            ( axi_ariane_req.ar.prot   ),
    .ar_qos_o             ( axi_ariane_req.ar.qos    ),
    .ar_region_o          ( axi_ariane_req.ar.region ),
    .ar_user_o            ( axi_ariane_req.ar.user   ),
    .ar_valid_o           ( axi_ariane_req.ar_valid  ),
    .r_ready_o            ( axi_ariane_req.r_ready   ),
    .aw_ready_i           ( axi_ariane_resp.aw_ready ),
    .ar_ready_i           ( axi_ariane_resp.ar_ready ),
    .w_ready_i            ( axi_ariane_resp.w_ready  ),
    .b_valid_i            ( axi_ariane_resp.b_valid  ),
    .b_id_i               ( axi_ariane_resp.b.id     ),
    .b_resp_i             ( axi_ariane_resp.b.resp   ),
    .b_user_i             ( axi_ariane_resp.b.user   ),
    .r_valid_i            ( axi_ariane_resp.r_valid  ),
    .r_id_i               ( axi_ariane_resp.r.id     ),
    .r_data_i             ( axi_ariane_resp.r.data   ),
    .r_resp_i             ( axi_ariane_resp.r.resp   ),
    .r_last_i             ( axi_ariane_resp.r.last   ),
    .r_user_i             ( axi_ariane_resp.r.user   )
  );

  //----------------------------------------------------------------------------
  // RVFI
  //----------------------------------------------------------------------------

  rvfi_tracer  #(
    .SIM_FINISH(2000000),
    .HART_ID(8'h0),
    .DEBUG_START(0),
    .DEBUG_STOP(0)
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
    .AXI_ID_WIDTH   ( ariane_soc::DRAM ),
    .AXI_USER_WIDTH ( AXI_USER_WIDTH           )
  ) cva6_axi_bus();

  axi_master_connect #(
  ) i_axi_master_connect_cva6_to_mem (
    .axi_req_i  (axi_ariane_req),
    .axi_resp_o (axi_ariane_resp),
    .master     (cva6_axi_bus)
  );

  axi2mem #(
    .AXI_ID_WIDTH   ( ariane_soc::DRAM ),
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
