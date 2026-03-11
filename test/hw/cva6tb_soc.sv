// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Author: Enrico Zelioli <ezelioli@iis.ee.ethz.ch>
//
// Testbench SoC

module cva6tb_soc
  import ariane_pkg::*;
  import cva6tb_pkg::*;
(
  input  logic                      clk_i,
  input  logic                      rst_ni,
  input  logic                      rtc_i,
  input  logic                      boot_mode_i,
  input  logic [NumClicExtIrqs-1:0] clic_ext_irqs_i,
  input  logic [NumPlicExtIrqs-1:0] plic_ext_irqs_i
);

  logic                              clk;
  logic                              rst_n;
  rvfi_probes_t                      rvfi_probes;

  logic                              mtip;
  logic                              msip;
  logic                              rtc_timer_irq;
  logic                        [1:0] xeip;
  logic                        [1:0] sw_xeip;  // raised by software, see cva6tb_regs
  logic            [NumClicIrqs-1:0] clic_irqs;
  logic            [NumPlicIrqs-1:0] plic_irqs;

  axi_mst_req_t                      axi_core_req;
  axi_mst_rsp_t                      axi_core_rsp;
  axi_slv_req_t                      axi_err_req;
  axi_slv_rsp_t                      axi_err_rsp;
  axi_slv_req_t                      axi_reg_req;
  axi_slv_rsp_t                      axi_reg_rsp;
  axi_slv_req_t                      axi_amo_req;
  axi_slv_rsp_t                      axi_amo_rsp;
  axi_slv_req_t                      axi_dly_req;
  axi_slv_rsp_t                      axi_dly_rsp;
  axi_slv_req_t                      axi_mem_req;
  axi_slv_rsp_t                      axi_mem_rsp;
  axi_slv_req_t                      axi_rmp_req;
  axi_slv_rsp_t                      axi_rmp_rsp;
  axi_slv_req_t                      axi_amo_spm_req;
  axi_slv_rsp_t                      axi_amo_spm_rsp;
  axi_slv_req_t                      axi_spm_req;
  axi_slv_rsp_t                      axi_spm_rsp;
  axi_mst_req_t [AxiXbarMasters-1:0] axi_mst_reqs;
  axi_mst_rsp_t [AxiXbarMasters-1:0] axi_mst_rsps;
  axi_slv_req_t [ AxiXbarSlaves-1:0] axi_slv_reqs;
  axi_slv_rsp_t [ AxiXbarSlaves-1:0] axi_slv_rsps;

  logic                              clic_irq_valid, clic_irq_ready;
  logic                              clic_irq_kill_req, clic_irq_kill_ack;
  logic                              clic_irq_shv;
  logic                        [7:0] clic_irq_id;
  logic                        [7:0] clic_irq_level;
  logic                        [1:0] clic_irq_priv;
  logic                              clic_irq_v;
  logic                        [5:0] clic_irq_vsid;

  reg_req_t                          reg_pcr_req;
  reg_rsp_t                          reg_pcr_rsp;
  reg_req_t                          reg_console_req;
  reg_rsp_t                          reg_console_rsp;
  reg_req_t                          reg_clic_req;
  reg_rsp_t                          reg_clic_rsp;
  reg_req_t                          reg_clint_req;
  reg_rsp_t                          reg_clint_rsp;
  reg_req_t                          reg_plic_req;
  reg_rsp_t                          reg_plic_rsp;
  reg_req_t                          reg_bootrom_req;
  reg_rsp_t                          reg_bootrom_rsp;
  reg_req_t                          reg_rtc_timer_req;
  reg_rsp_t                          reg_rtc_timer_rsp;
  reg_req_t                          reg_err_req;
  reg_rsp_t                          reg_err_rsp;
  reg_req_t                          reg_in_req;
  reg_rsp_t                          reg_in_rsp;
  reg_req_t       [RegbusOutNum-1:0] reg_out_reqs;
  reg_rsp_t       [RegbusOutNum-1:0] reg_out_rsps;

  reg_idx_t                          reg_select;
  reg_idx_t                          default_reg_idx;

  logic [63:0]                       rtc_timer_time;

  function automatic void load_sim_spm(string binary_path);
    log("Preloading AXI SPM");
    $readmemh(binary_path, i_axi_spm.mem);
  endfunction

  function automatic void load_sim_mem(string binary_path);
    log("Preloading AXI sim mem");
    $readmemh(binary_path, i_axi_sim_mem.mem);
  endfunction

  // Main memory latency: the delay the AXI delayer applies to each channel, set
  // by the test before reset. A delay of n adds n+2 cycles to every channel.
  localparam int unsigned MemMaxDelay = 16;
  logic [$clog2(MemMaxDelay):0] mem_delay = 'd10;

  function automatic void set_mem_delay(int unsigned delay);
    if (delay > MemMaxDelay)
      $fatal(1, "memory delay %0d exceeds the maximum of %0d", delay, MemMaxDelay);
    log($sformatf("Main memory delay: %0d per AXI channel", delay));
    mem_delay = delay[$clog2(MemMaxDelay):0];
  endfunction

  assign clk   = clk_i;
  assign rst_n = rst_ni;

  assign clic_irqs[ 0] = 1'b0;
  assign clic_irqs[ 1] = 1'b0;
  assign clic_irqs[ 2] = 1'b0;
  assign clic_irqs[ 3] = msip;
  assign clic_irqs[ 4] = 1'b0;
  assign clic_irqs[ 5] = 1'b0;
  assign clic_irqs[ 6] = 1'b0;
  assign clic_irqs[ 7] = mtip;
  assign clic_irqs[ 8] = 1'b0;
  assign clic_irqs[ 9] = 1'b0;
  assign clic_irqs[10] = 1'b0;
  assign clic_irqs[11] = 1'b0;
  assign clic_irqs[12] = 1'b0;
  assign clic_irqs[13] = 1'b0;
  assign clic_irqs[14] = 1'b0;
  assign clic_irqs[15] = 1'b0;
  assign clic_irqs[16] = 1'b0;
  assign clic_irqs[17] = rtc_timer_irq;
  assign clic_irqs[NumClicIrqs-1:NumClicIntIrqs] = clic_ext_irqs_i;

  assign plic_irqs[ 0] = 1'b0;
  assign plic_irqs[ 1] = rtc_timer_irq;
  assign plic_irqs[ 2] = 1'b0;
  assign plic_irqs[ 3] = 1'b0;
  assign plic_irqs[ 4] = 1'b0;
  assign plic_irqs[ 5] = 1'b0;
  assign plic_irqs[ 6] = 1'b0;
  assign plic_irqs[ 7] = 1'b0;
  assign plic_irqs[ 8] = 1'b0;
  assign plic_irqs[ 9] = 1'b0;
  assign plic_irqs[10] = 1'b0;
  assign plic_irqs[11] = 1'b0;
  assign plic_irqs[12] = 1'b0;
  assign plic_irqs[13] = 1'b0;
  assign plic_irqs[14] = 1'b0;
  assign plic_irqs[15] = 1'b0;
  assign plic_irqs[NumPlicIrqs-1:NumPlicIntIrqs] = plic_ext_irqs_i;

  assign default_reg_idx = (RegbusErrId);

  assign axi_mst_reqs[0] = axi_core_req;
  assign axi_core_rsp = axi_mst_rsps[0];

  assign axi_err_req = axi_slv_reqs[AxiSlvIdErrSlv];
  assign axi_slv_rsps[AxiSlvIdErrSlv] = axi_err_rsp;

  assign axi_reg_req = axi_slv_reqs[AxiSlvIdReg];
  assign axi_slv_rsps[AxiSlvIdReg] = axi_reg_rsp;

  assign axi_amo_req = axi_slv_reqs[AxiSlvIdDram];
  assign axi_slv_rsps[AxiSlvIdDram] = axi_amo_rsp;

  assign axi_amo_spm_req = axi_slv_reqs[AxiSlvIdSpm];
  assign axi_slv_rsps[AxiSlvIdSpm] = axi_amo_spm_rsp;

  assign reg_err_req = reg_out_reqs[RegbusErrId];
  assign reg_out_rsps[RegbusErrId] = reg_err_rsp;

  assign reg_pcr_req = reg_out_reqs[RegbusPCRsId];
  assign reg_out_rsps[RegbusPCRsId] = reg_pcr_rsp;

  assign reg_console_req = reg_out_reqs[RegbusConsoleId];
  assign reg_out_rsps[RegbusConsoleId] = reg_console_rsp;

  assign reg_clic_req = reg_out_reqs[RegbusClicId];
  assign reg_out_rsps[RegbusClicId] = reg_clic_rsp;

  assign reg_clint_req = reg_out_reqs[RegbusClintId];
  assign reg_out_rsps[RegbusClintId] = reg_clint_rsp;

  assign reg_plic_req = reg_out_reqs[RegbusPlicId];
  assign reg_out_rsps[RegbusPlicId] = reg_plic_rsp;

  assign reg_bootrom_req = reg_out_reqs[RegbusBootromId];
  assign reg_out_rsps[RegbusBootromId] = reg_bootrom_rsp;

  assign reg_rtc_timer_req = reg_out_reqs[RegbusRTCTimerId];
  assign reg_out_rsps[RegbusRTCTimerId] = reg_rtc_timer_rsp;

  cva6 #(
    .CVA6Cfg             ( CVA6Cfg                           ),
    .rvfi_probes_instr_t ( rvfi_probes_instr_t               ),
    .rvfi_probes_csr_t   ( rvfi_probes_csr_t                 ),
    .rvfi_probes_t       ( rvfi_probes_t                     ),
    .axi_ar_chan_t       ( axi_mst_ar_chan_t                 ),
    .axi_aw_chan_t       ( axi_mst_aw_chan_t                 ),
    .axi_w_chan_t        ( axi_mst_w_chan_t                  ),
    .b_chan_t            ( axi_mst_b_chan_t                  ),
    .r_chan_t            ( axi_mst_r_chan_t                  ),
    .noc_req_t           ( axi_mst_req_t                     ),
    .noc_resp_t          ( axi_mst_rsp_t                     )
  ) i_cva6 (
    .clk_i               ( clk                               ),
    .rst_ni              ( rst_n                             ),
    .boot_addr_i         ( {32'h0, BootromBaseAddr}          ),
    .hart_id_i           ( 64'h0                             ),
    .irq_i               ( xeip | sw_xeip                    ),
    .ipi_i               ( msip                              ),
    .time_irq_i          ( mtip                              ),
    .debug_req_i         ( '0                                ),
    .clic_irq_valid_i    ( clic_irq_valid                    ),
    .clic_irq_id_i       ( clic_irq_id                       ),
    .clic_irq_level_i    ( clic_irq_level                    ),
    .clic_irq_priv_i     ( riscv::priv_lvl_t'(clic_irq_priv) ),
    .clic_irq_v_i        ( clic_irq_v                        ),
    .clic_irq_vsid_i     ( clic_irq_vsid                     ),
    .clic_irq_shv_i      ( clic_irq_shv                      ),
    .clic_irq_ready_o    ( clic_irq_ready                    ),
    .clic_kill_req_i     ( clic_irq_kill_req                 ),
    .clic_kill_ack_o     ( clic_irq_kill_ack                 ),
    .rvfi_probes_o       ( rvfi_probes                       ),
    .cvxif_req_o         ( /* Not connected */               ),
    .cvxif_resp_i        ( '0                                ),
    .noc_req_o           ( axi_core_req                      ),
    .noc_resp_i          ( axi_core_rsp                      )
  );

  // CLIC interrupt controller
  clic #(
    .N_SOURCE       ( NumClicIrqs       ),
    .INTCTLBITS     ( 8                 ),
    .reg_req_t      ( reg_req_t         ),
    .reg_rsp_t      ( reg_rsp_t         ),
    .SSCLIC         ( 1                 ),
    .USCLIC         ( 0                 ),
    .VSCLIC         ( 1                 ),
    .N_VSCTXTS      ( 4                 ),
    .VSPRIO         ( 1                 ),
    .VSPRIO_W       ( 1                 )
  ) i_clic (
    .clk_i          ( clk               ),
    .rst_ni         ( rst_n             ),
    .reg_req_i      ( reg_clic_req      ),
    .reg_rsp_o      ( reg_clic_rsp      ),
    .intr_src_i     ( clic_irqs         ),
    .irq_valid_o    ( clic_irq_valid    ),
    .irq_ready_i    ( clic_irq_ready    ),
    .irq_id_o       ( clic_irq_id       ),
    .irq_level_o    ( clic_irq_level    ),
    .irq_shv_o      ( clic_irq_shv      ),
    .irq_priv_o     ( clic_irq_priv     ),
    .irq_v_o        ( clic_irq_v        ),
    .irq_vsid_o     ( clic_irq_vsid     ),
    .irq_kill_req_o ( clic_irq_kill_req ),
    .irq_kill_ack_i ( clic_irq_kill_ack )
  );

  // CLINT interrupt controller
  clint #(
    .reg_req_t   ( reg_req_t     ),
    .reg_rsp_t   ( reg_rsp_t     )
  ) i_clint (
    .clk_i       ( clk           ),
    .rst_ni      ( rst_n         ),
    .testmode_i  ( 1'b0          ),
    .reg_req_i   ( reg_clint_req ),
    .reg_rsp_o   ( reg_clint_rsp ),
    .rtc_i       ( rtc_i         ),
    .timer_irq_o ( mtip          ),
    .ipi_o       ( msip          )
  );

  // PLIC interrupt controller
  rv_plic #(
    .reg_req_t  ( reg_req_t ),
    .reg_rsp_t  ( reg_rsp_t )
  ) i_plic (
    .clk_i      ( clk          ),
    .rst_ni     ( rst_n        ),
    .reg_req_i  ( reg_plic_req ),
    .reg_rsp_o  ( reg_plic_rsp ),
    .intr_src_i ( plic_irqs    ),
    .irq_o      ( xeip         ),
    .irq_id_o   (              ),
    .msip_o     (              )
  );

  // AXI interconnect
  axi_xbar #(
    .Cfg                   ( AxiXbarCfg             ),
    .ATOPs                 ( 1                      ),
    .Connectivity          ( '1                     ),
    .slv_aw_chan_t         ( axi_mst_aw_chan_t      ),
    .mst_aw_chan_t         ( axi_slv_aw_chan_t      ),
    .w_chan_t              ( axi_mst_w_chan_t       ),
    .slv_b_chan_t          ( axi_mst_b_chan_t       ),
    .mst_b_chan_t          ( axi_slv_b_chan_t       ),
    .slv_ar_chan_t         ( axi_mst_ar_chan_t      ),
    .mst_ar_chan_t         ( axi_slv_ar_chan_t      ),
    .slv_r_chan_t          ( axi_mst_r_chan_t       ),
    .mst_r_chan_t          ( axi_slv_r_chan_t       ),
    .slv_req_t             ( axi_mst_req_t          ),
    .slv_resp_t            ( axi_mst_rsp_t          ),
    .mst_req_t             ( axi_slv_req_t          ),
    .mst_resp_t            ( axi_slv_rsp_t          ),
    .rule_t                ( addr_rule_t            )
  ) i_axi_xbar (
    .clk_i                 ( clk                    ),
    .rst_ni                ( rst_n                  ),
    .test_i                ( '0                     ),
    .slv_ports_req_i       ( axi_mst_reqs           ),
    .slv_ports_resp_o      ( axi_mst_rsps           ),
    .mst_ports_req_o       ( axi_slv_reqs           ),
    .mst_ports_resp_i      ( axi_slv_rsps           ),
    .addr_map_i            ( AxiMap                 ),
    .en_default_mst_port_i ( {AxiXbarMasters{1'b1}} ),
    .default_mst_port_i    ( {AxiXbarMasters{2'b0}} )
  );

  // AXI error slave
  axi_err_slv #(
    .AxiIdWidth  ( AxiSlvIdWidth ),
    .axi_req_t   ( axi_slv_req_t ),
    .axi_resp_t  ( axi_slv_rsp_t )
  ) i_axi_err_slv (
    .clk_i       ( clk           ),
    .rst_ni      ( rst_n         ),
    .test_i      ( '0            ),
    .slv_req_i   ( axi_err_req   ),
    .slv_resp_o  ( axi_err_rsp   )
  );

  // Convert from AXI to reg protocol
  axi_to_reg_v2 #(
    .AxiAddrWidth ( CVA6UserCfg.AxiAddrWidth ),
    .AxiDataWidth ( CVA6UserCfg.AxiDataWidth ),
    .AxiIdWidth   ( AxiSlvIdWidth            ),
    .AxiUserWidth ( CVA6UserCfg.AxiUserWidth ),
    .RegDataWidth ( 32                       ),
    .CutMemReqs   ( 0                        ),
    .axi_req_t    ( axi_slv_req_t            ),
    .axi_rsp_t    ( axi_slv_rsp_t            ),
    .reg_req_t    ( reg_req_t                ),
    .reg_rsp_t    ( reg_rsp_t                )
  ) i_axi_to_reg_v2 (
    .clk_i        ( clk                      ),
    .rst_ni       ( rst_n                    ),
    .axi_req_i    ( axi_reg_req              ),
    .axi_rsp_o    ( axi_reg_rsp              ),
    .reg_req_o    ( reg_in_req               ),
    .reg_rsp_i    ( reg_in_rsp               ),
    .reg_id_o     (                          ),
    .busy_o       (                          )
  );

  // Non-matching addresses are directed to an error slave
  addr_decode #(
    .NoIndices        ( RegbusOutNum    ),
    .NoRules          ( RegbusRulesNum  ),
    .addr_t           ( reg_addr_t      ),
    .rule_t           ( reg_addr_rule_t )
  ) i_reg_demux_decode (
    .addr_i           ( reg_in_req.addr ),
    .addr_map_i       ( RegbusMap       ),
    .idx_o            ( reg_select      ),
    .dec_valid_o      (                 ),
    .dec_error_o      (                 ),
    .en_default_idx_i ( 1'b1            ),
    .default_idx_i    ( default_reg_idx )
  );

  reg_demux #(
    .NoPorts     ( RegbusOutNum ),
    .req_t       ( reg_req_t    ),
    .rsp_t       ( reg_rsp_t    )
  ) i_reg_demux (
    .clk_i       ( clk          ),
    .rst_ni      ( rst_n        ),
    .in_select_i ( reg_select   ),
    .in_req_i    ( reg_in_req   ),
    .in_rsp_o    ( reg_in_rsp   ),
    .out_req_o   ( reg_out_reqs ),
    .out_rsp_i   ( reg_out_rsps )
  );

  reg_err_slv #(
    .DW      ( 32           ),
    .ERR_VAL ( 32'hBADCAB1E ),
    .req_t   ( reg_req_t    ),
    .rsp_t   ( reg_rsp_t    )
  ) i_reg_err_slv (
    .req_i   ( reg_err_req  ),
    .rsp_o   ( reg_err_rsp  )
  );

  // Platform control registers
  cva6tb_regs #(
    .reg_req_t   ( reg_req_t      ),
    .reg_rsp_t   ( reg_rsp_t      )
  ) i_regs (
    .clk_i       ( clk            ),
    .rst_ni      ( rst_n          ),
    .boot_mode_i ( boot_mode_i    ),
    .reg_req_i   ( reg_pcr_req    ),
    .reg_rsp_o   ( reg_pcr_rsp    ),
    .irq_o       ( sw_xeip        )
  );

  // Sim console
  cva6tb_sim_console #(
    .reg_req_t   ( reg_req_t       ),
    .reg_rsp_t   ( reg_rsp_t       )
  ) i_sim_console (
    .clk_i       ( clk             ),
    .rst_ni      ( rst_n           ),
    .reg_req_i   ( reg_console_req ),
    .reg_rsp_o   ( reg_console_rsp )
  );

  // RTC timer
  cva6tb_rtc_timer #(
    .reg_req_t ( reg_req_t         ),
    .reg_rsp_t ( reg_rsp_t         )
  ) i_rtc_timer (
    .clk_i     ( clk               ),
    .rst_ni    ( rst_n             ),
    .reg_req_i ( reg_rtc_timer_req ),
    .reg_rsp_o ( reg_rtc_timer_rsp ),
    .rtc_i     ( rtc_i             ),
    .irq_o     ( rtc_timer_irq     ),
    .time_o    ( rtc_timer_time    )
  );

  // Bootrom
  logic [15:0]  bootrom_addr;
  logic [31:0]  bootrom_data, bootrom_data_q;
  logic         bootrom_req,  bootrom_req_q;
  logic         bootrom_we,   bootrom_we_q;

  // Delay response by one cycle to fulfill mem protocol
  always_ff @(posedge clk or negedge rst_n) begin
    if (~rst_n) begin
      bootrom_data_q <= '0;
      bootrom_req_q  <= '0;
      bootrom_we_q   <= '0;
    end else begin
      bootrom_data_q <= bootrom_data;
      bootrom_req_q  <= bootrom_req;
      bootrom_we_q   <= bootrom_we;
    end
  end

  reg_to_mem #(
    .AW        ( 16              ),
    .DW        ( 32              ),
    .req_t     ( reg_req_t       ),
    .rsp_t     ( reg_rsp_t       )
  ) i_reg_to_bootrom (
    .clk_i     ( clk             ),
    .rst_ni    ( rst_n           ),
    .reg_req_i ( reg_bootrom_req ),
    .reg_rsp_o ( reg_bootrom_rsp ),
    .req_o     ( bootrom_req     ),
    .gnt_i     ( bootrom_req     ),
    .we_o      ( bootrom_we      ),
    .addr_o    ( bootrom_addr    ),
    .wdata_o   (                 ),
    .wstrb_o   (                 ),
    .rdata_i   ( bootrom_data_q  ),
    .rvalid_i  ( bootrom_req_q   ),
    .rerror_i  ( bootrom_we_q    )
  );

  cva6tb_bootrom #(
    .AddrWidth ( 16           ),
    .DataWidth ( 32           )
  ) i_bootrom (
    .clk_i     ( clk          ),
    .rst_ni    ( rst_n        ),
    .req_i     ( bootrom_req  ),
    .addr_i    ( bootrom_addr ),
    .data_o    ( bootrom_data )
  );

  // RISC-V atomics filter
  axi_riscv_atomics_structs #(
    .AxiAddrWidth     ( CVA6UserCfg.AxiAddrWidth ),
    .AxiDataWidth     ( CVA6UserCfg.AxiDataWidth ),
    .AxiIdWidth       ( AxiSlvIdWidth            ),
    .AxiUserWidth     ( CVA6UserCfg.AxiUserWidth ),
    .AxiMaxReadTxns   ( 24                       ),
    .AxiMaxWriteTxns  ( 24                       ),
    .AxiUserAsId      ( 1                        ),
    .AxiUserIdMsb     ( 0                        ),
    .AxiUserIdLsb     ( 0                        ),
    .RiscvWordWidth   ( 64                       ),
    .NAxiCuts         ( 0                        ),
    .axi_req_t        ( axi_slv_req_t            ),
    .axi_rsp_t        ( axi_slv_rsp_t            )
  ) i_riscv_atomics (
    .clk_i            ( clk                      ),
    .rst_ni           ( rst_n                    ),
    .axi_slv_req_i    ( axi_amo_req              ),
    .axi_slv_rsp_o    ( axi_amo_rsp              ),
    .axi_mst_req_o    ( axi_dly_req              ),
    .axi_mst_rsp_i    ( axi_dly_rsp              )
  );

  // AXI delayer
  // Simulates arbitrary memory latency without bandwidth throttling
  axi_fifo_delay_dyn #(
    .aw_chan_t  ( axi_slv_aw_chan_t ),
    .w_chan_t   ( axi_slv_w_chan_t  ),
    .b_chan_t   ( axi_slv_b_chan_t  ),
    .ar_chan_t  ( axi_slv_ar_chan_t ),
    .r_chan_t   ( axi_slv_r_chan_t  ),
    .axi_req_t  ( axi_slv_req_t     ),
    .axi_resp_t ( axi_slv_rsp_t     ),
    .DepthAR    ( 16                ),
    .DepthAW    ( 16                ),
    .DepthR     ( 16                ),
    .DepthW     ( 16                ),
    .DepthB     ( 16                ),
    .MaxDelay   ( MemMaxDelay       )
  ) i_axi_mem_delayer (
    .clk_i      ( clk               ),
    .rst_ni     ( rst_n             ),
    .aw_delay_i ( mem_delay         ),
    .w_delay_i  ( mem_delay         ),
    .b_delay_i  ( mem_delay         ),
    .ar_delay_i ( mem_delay         ),
    .r_delay_i  ( mem_delay         ),
    .slv_req_i  ( axi_dly_req       ),
    .slv_resp_o ( axi_dly_rsp       ),
    .mst_req_o  ( axi_mem_req       ),
    .mst_resp_i ( axi_mem_rsp       )
  );

  // Remap uncached memory accesses
  always_comb begin
    axi_rmp_req = axi_mem_req;
    axi_mem_rsp = axi_rmp_rsp;
    if ((axi_mem_req.aw.addr & ~DramUncachedMask) == DramUncachedBaseAddr) begin
      axi_rmp_req.aw.addr = DramBaseAddr | (axi_mem_req.aw.addr & DramUncachedMask);
    end
    if ((axi_mem_req.ar.addr & ~DramUncachedMask) == DramUncachedBaseAddr) begin
      axi_rmp_req.ar.addr = DramBaseAddr | (axi_mem_req.ar.addr & DramUncachedMask);
    end
  end

  // AXI simulated memory
  cva6tb_axi_sim_mem #(
    .AddrWidth          ( CVA6UserCfg.AxiAddrWidth ),
    .DataWidth          ( CVA6UserCfg.AxiDataWidth ),
    .IdWidth            ( AxiSlvIdWidth            ),
    .UserWidth          ( CVA6UserCfg.AxiUserWidth ),
    .axi_req_t          ( axi_slv_req_t            ),
    .axi_rsp_t          ( axi_slv_rsp_t            ),
  `ifdef ZERO_SIM_MEM
    .UninitializedData  ( "zeros"                  )
  `else
    .UninitializedData  ( "random"                 )
  `endif
  ) i_axi_sim_mem (
    .clk_i              ( clk                      ),
    .rst_ni             ( rst_n                    ),
    .axi_req_i          ( axi_rmp_req              ),
    .axi_rsp_o          ( axi_rmp_rsp              )
  );

  // RISC-V atomics filter
  axi_riscv_atomics_structs #(
    .AxiAddrWidth     ( CVA6UserCfg.AxiAddrWidth ),
    .AxiDataWidth     ( CVA6UserCfg.AxiDataWidth ),
    .AxiIdWidth       ( AxiSlvIdWidth            ),
    .AxiUserWidth     ( CVA6UserCfg.AxiUserWidth ),
    .AxiMaxReadTxns   ( 24                       ),
    .AxiMaxWriteTxns  ( 24                       ),
    .AxiUserAsId      ( 1                        ),
    .AxiUserIdMsb     ( 0                        ),
    .AxiUserIdLsb     ( 0                        ),
    .RiscvWordWidth   ( 64                       ),
    .NAxiCuts         ( 0                        ),
    .axi_req_t        ( axi_slv_req_t            ),
    .axi_rsp_t        ( axi_slv_rsp_t            )
  ) i_riscv_atomics_spm (
    .clk_i            ( clk                      ),
    .rst_ni           ( rst_n                    ),
    .axi_slv_req_i    ( axi_amo_spm_req          ),
    .axi_slv_rsp_o    ( axi_amo_spm_rsp          ),
    .axi_mst_req_o    ( axi_spm_req              ),
    .axi_mst_rsp_i    ( axi_spm_rsp              )
  );

  // AXI simulated memory
  cva6tb_axi_sim_mem #(
    .AddrWidth          ( CVA6UserCfg.AxiAddrWidth ),
    .DataWidth          ( CVA6UserCfg.AxiDataWidth ),
    .IdWidth            ( AxiSlvIdWidth            ),
    .UserWidth          ( CVA6UserCfg.AxiUserWidth ),
    .axi_req_t          ( axi_slv_req_t            ),
    .axi_rsp_t          ( axi_slv_rsp_t            ),
  `ifdef ZERO_SIM_MEM
    .UninitializedData  ( "zeros"                  )
  `else
    .UninitializedData  ( "random"                 )
  `endif
  ) i_axi_spm (
    .clk_i              ( clk                      ),
    .rst_ni             ( rst_n                    ),
    .axi_req_i          ( axi_spm_req              ),
    .axi_rsp_o          ( axi_spm_rsp              )
  );

endmodule
