// (C) 2001-2024 Intel Corporation. All rights reserved.
// Your use of Intel Corporation's design tools, logic functions and other 
// software and tools, and its AMPP partner logic functions, and any output 
// files from any of the foregoing (including device programming or simulation 
// files), and any associated documentation or information are expressly subject 
// to the terms and conditions of the Intel Program License Subscription 
// Agreement, Intel FPGA IP License Agreement, or other applicable 
// license agreement, including, without limitation, that your use is for the 
// sole purpose of programming logic devices manufactured by Intel and sold by 
// Intel or its authorized distributors.  Please refer to the applicable 
// agreement for further details.



///////////////////////////////////////////////////////////////////////////////
// This module handles the creation and wiring of the core clock/reset signals.
//
///////////////////////////////////////////////////////////////////////////////

// altera message_off 10036

 module altera_emif_arch_fm_core_clks_rsts #(
   parameter PHY_CONFIG_ENUM                         = "",
   parameter PHY_CORE_CLKS_SHARING_ENUM              = "",
   parameter PHY_PING_PONG_EN                        = 0,
   parameter C2P_P2C_CLK_RATIO                       = 1,
   parameter USER_CLK_RATIO                          = 1,
   parameter PORT_CLKS_SHARING_MASTER_OUT_WIDTH      = 32,
   parameter PORT_CLKS_SHARING_SLAVE_IN_WIDTH        = 32,
   parameter DIAG_CPA_OUT_1_EN                       = 0,
   parameter DIAG_USE_CPA_LOCK                       = 1,
   parameter DIAG_SYNTH_FOR_SIM                      = 1,
   parameter PORT_DFT_ND_CORE_CLK_BUF_OUT_WIDTH      = 1,
   parameter PORT_DFT_ND_CORE_CLK_LOCKED_WIDTH       = 1
) (
   // For a master interface, the PLL ref clock and the global reset signal
   // come from an external source from user logic, via the following ports.
   // For slave interfaces, they come from the master via the sharing interface.
   // The connectivity ensures that all interfaces in a master/slave
   // configuration share the same ref clock and global reset, which is
   // one of the requirements for core-clock sharing.
   // pll_ref_clk_int is the actual PLL ref clock signal that will be used by the
   // reset of the IP. For a master interface it is equivalent to pll_ref_clk.
   // For a slave interface it is equivalent to the pll_ref_clk signal of the master.
   input  logic                                                 pll_ref_clk,
   output logic                                                 pll_ref_clk_int,

   // For a master interface, core clocks come from the clock phase alignment
   // block of the current interface, via the following ports. Note that the
   // CPA block also expects feedback signals after the clock signals have
   // propagated through core clock networks.
   // For slave interfaces, the core clock signals come from the master
   // via the sharing interface.
   input  logic [1:0]                                           core_clks_from_cpa_pri,
   input  logic [1:0]                                           core_clks_locked_cpa_pri,
   output logic [1:0]                                           core_clks_fb_to_cpa_pri,

   input  logic [1:0]                                           core_clks_from_cpa_sec,
   input  logic [1:0]                                           core_clks_locked_cpa_sec,
   output logic [1:0]                                           core_clks_fb_to_cpa_sec,

   // Async reset_n signal from sequencer to force core clock domain to be in reset.
   // This is needed by local_reset_req as well as by DCD calibration (which can
   // destabilize the CPA output clocks.
   input logic                                                  seq2core_reset_n,

   // PLL lock signal
   input  logic                                                 pll_locked,

   // PLL c-counters
   input  logic [8:0]                                           pll_c_counters,

   // Reset request signal.
   // local_reset_req_int is the actual reset request signal that will be
   // used internally by the rest of the IP. For a master interface it
   // is equivalent to local_reset_req. For a slave interface it is
   // equivalent to the local_reset_req signal of the master.
   input  logic                                                 local_reset_req,
   output logic                                                 local_reset_req_int,

   // The following is the master/slave sharing interfaces.
   input  logic [PORT_CLKS_SHARING_SLAVE_IN_WIDTH-1:0]          clks_sharing_slave_in,
   output logic [PORT_CLKS_SHARING_MASTER_OUT_WIDTH-1:0]        clks_sharing_master_out,

   // The following are all the possible core clock/reset signals.
   // afi_* only exists in PHY-only mode (or if soft controller is used).
   // emif_usr_* only exists if hard memory controller is used.
   output logic                                                 afi_clk,
   output logic                                                 afi_half_clk,
   output logic                                                 afi_reset_n,

   output logic                                                 emif_usr_clk,
   output logic                                                 emif_usr_half_clk,
   output logic                                                 emif_usr_reset_n,

   output logic                                                 emif_usr_clk_sec,
   output logic                                                 emif_usr_half_clk_sec,
   output logic                                                 emif_usr_reset_n_sec,

   // DFT
   output logic [PORT_DFT_ND_CORE_CLK_BUF_OUT_WIDTH-1:0]        dft_core_clk_buf_out,
   output logic [PORT_DFT_ND_CORE_CLK_LOCKED_WIDTH-1:0]         dft_core_clk_locked
);
   timeunit 1ns;
   timeprecision 1ps;

   // This is the length of the core reset synchronizer chain. At a high-level,
   // we de-assert reset whenever the core clock is stable (as indicated by signals such
   // as CPA lock and DCC stable).
   // The chain actually has two purposes: reset synchronization (which typically requires
   // no more than 3 FFs for reasonable MTBF), and delaying reset deassertion enough to
   // satisfy the following two requirements:
   // 1) It is set higher than the length of the reset chain
   //    in the periphery (5+), to avoid the core from getting out of reset
   //    earlier than the hard PHY/sequencer/controller.
   //    This is for extra safety, but isn't strictly necessary, because
   //    soft logic must either wait for the hard controller's assertion of
   //    the ready signal, or, if the hard controller is bypassed,
   //    for the sequencer to assert the afi_cal_success, prior to accessing
   //    the hard circuitries.
   // 2) It is set high enough for the reset state to propagate to all Hyper-register
   //    stages in the IP. Since Hyper-registers can't be reset asynchronously,
   //    they are carefully designed such that they'll naturally reach the reset
   //    state with enough number of clock cycles, prior to system reset
   //    deassertion occurs. For this purpose we reserve 16 FFs.
   // 3) The async reset to the reset synchronizer has MCP setup=7, hold=6 to
   //    relax timing. This means the async reset arrival time has a max variance
   //    of 7 cycles, which means the output of synchronizer FF 0..6 can all be
   //    metastable. For this purpose we reserve 7 FFs
   localparam CPA_RESET_SYNC_LENGTH = 27;

   // Reset synchronizer chain length for PLL-based core clocks
   // The async reset to the reset synchronizer has MCP setup=7, hold=6 to
   // relax timing. This means the async reset arrival time has a max variance
   // of 7 cycles, which means the output of synchronizer FF 0..6 can all be
   // metastable. For safety set sychronzier length to be 7+3=10.   
   localparam PLL_RESET_SYNC_LENGTH = 10;

   // Data synchronizer chain length for local_reset_req
   localparam LOCAL_RESET_REQ_SYNC_LENGTH = 3;

   /////////////////////////////////////////////////////////////
   // Get signals to/from the master/slave sharing interface.
   logic local_reset_req_sync;
   logic pll_locked_int;
   logic seq2core_reset_n_int;
   logic counter_lock;
   logic cpa_lock_pri;
   logic cpa_lock_sec;
   logic async_reset_n_pri;
   logic async_reset_n_sec;
   logic issp_reset_n;

`ifdef ALTERA_EMIF_ENABLE_ISSP
   altsource_probe #(
      .sld_auto_instance_index ("YES"),
      .sld_instance_index      (0),
      .instance_id             ("TGR"),
      .probe_width             (0),
      .source_width            (1),
      .source_initial_value    ("1"),
      .enable_metastability    ("NO")
   ) core_reset_n_issp (
      .source  (issp_reset_n)
   );
`else
   assign issp_reset_n = 1'b1;
`endif

   assign async_reset_n_pri = (DIAG_USE_CPA_LOCK ? cpa_lock_pri : counter_lock) & seq2core_reset_n_int & issp_reset_n;
   assign async_reset_n_sec = (DIAG_USE_CPA_LOCK ? cpa_lock_sec : counter_lock) & seq2core_reset_n_int & issp_reset_n;

   logic pll_ref_clk_slave_in;
   logic pll_locked_slave_in;
   logic cpa_lock_pri_slave_in;
   logic cpa_lock_sec_slave_in;
   logic local_reset_req_slave_in;
   logic seq2core_reset_n_slave_in;
   logic afi_clk_slave_in;
   logic afi_half_clk_slave_in;
   logic afi_reset_n_pre_reg_slave_in;
   logic afi_reset_n_pre_reg;
   logic counter_lock_slave_in;
   logic emif_usr_clk_slave_in;
   logic emif_usr_half_clk_slave_in;
   logic emif_usr_reset_n_pri_pre_reg_slave_in;
   logic emif_usr_reset_n_pri_pre_reg;
   logic emif_usr_clk_sec_slave_in;
   logic emif_usr_half_clk_sec_slave_in;
   logic emif_usr_reset_n_sec_pre_reg_slave_in;
   logic emif_usr_reset_n_sec_pre_reg;


   /////////////////////////////////////////////////////////////
   // Generate connectivity for PLL ref clk and reset.
   generate
      if (PHY_CORE_CLKS_SHARING_ENUM == "CORE_CLKS_SHARING_SLAVE")
      begin : slave
         assign pll_ref_clk_int                   = pll_ref_clk_slave_in;
         assign pll_locked_int                    = pll_locked_slave_in;
         assign local_reset_req_int               = local_reset_req_slave_in;
         assign seq2core_reset_n_int              = seq2core_reset_n_slave_in;

         assign pll_ref_clk_slave_in                  = clks_sharing_slave_in[0];
         assign pll_locked_slave_in                   = clks_sharing_slave_in[1];
         assign seq2core_reset_n_slave_in             = clks_sharing_slave_in[2];
         assign local_reset_req_slave_in              = clks_sharing_slave_in[3];
         assign cpa_lock_pri_slave_in                 = clks_sharing_slave_in[4];
         assign cpa_lock_sec_slave_in                 = clks_sharing_slave_in[5];
         assign counter_lock_slave_in                 = clks_sharing_slave_in[6];
         assign afi_clk_slave_in                      = clks_sharing_slave_in[7];
         assign afi_half_clk_slave_in                 = clks_sharing_slave_in[8];
         assign afi_reset_n_pre_reg_slave_in          = clks_sharing_slave_in[9];
         assign emif_usr_clk_slave_in                 = clks_sharing_slave_in[10];
         assign emif_usr_half_clk_slave_in            = clks_sharing_slave_in[11];
         assign emif_usr_reset_n_pri_pre_reg_slave_in = clks_sharing_slave_in[12];
         assign emif_usr_clk_sec_slave_in             = clks_sharing_slave_in[13];
         assign emif_usr_half_clk_sec_slave_in        = clks_sharing_slave_in[14];
         assign emif_usr_reset_n_sec_pre_reg_slave_in = clks_sharing_slave_in[15];

         assign clks_sharing_master_out = '0;
      end else
      begin : master

`ifdef ALTERA_EMIF_ENABLE_ISSP
         altsource_probe #(
            .sld_auto_instance_index ("YES"),
            .sld_instance_index      (0),
            .instance_id             ("PALP"),
            .probe_width             (1),
            .source_width            (0),
            .source_initial_value    ("0"),
            .enable_metastability    ("NO")
         ) cpa_lock_pri_issp (
            .probe  (cpa_lock_pri)
         );

         altsource_probe #(
            .sld_auto_instance_index ("YES"),
            .sld_instance_index      (0),
            .instance_id             ("PALS"),
            .probe_width             (1),
            .source_width            (0),
            .source_initial_value    ("0"),
            .enable_metastability    ("NO")
         ) cpa_lock_sec_issp (
            .probe  (cpa_lock_sec)
         );
`endif

         assign local_reset_req_int  = local_reset_req_sync;
         assign pll_ref_clk_int      = pll_ref_clk;
         assign pll_locked_int       = pll_locked;
         assign seq2core_reset_n_int = seq2core_reset_n;

         assign clks_sharing_master_out[0]  = pll_ref_clk_int;
         assign clks_sharing_master_out[1]  = pll_locked_int;
         assign clks_sharing_master_out[2]  = seq2core_reset_n_int;
         assign clks_sharing_master_out[3]  = local_reset_req_int;
         assign clks_sharing_master_out[4]  = cpa_lock_pri;
         assign clks_sharing_master_out[5]  = cpa_lock_sec;
         assign clks_sharing_master_out[6]  = counter_lock;
         assign clks_sharing_master_out[7]  = afi_clk;
         assign clks_sharing_master_out[8]  = afi_half_clk;
         assign clks_sharing_master_out[9]  = afi_reset_n_pre_reg;
         assign clks_sharing_master_out[10] = emif_usr_clk;
         assign clks_sharing_master_out[11] = emif_usr_half_clk;
         assign clks_sharing_master_out[12] = emif_usr_reset_n_pri_pre_reg;
         assign clks_sharing_master_out[13] = emif_usr_clk_sec;
         assign clks_sharing_master_out[14] = emif_usr_half_clk_sec;
         assign clks_sharing_master_out[15] = emif_usr_reset_n_sec_pre_reg;

         assign clks_sharing_master_out[PORT_CLKS_SHARING_MASTER_OUT_WIDTH-1:16] = '0;
      end
   endgenerate

   /////////////////////////////////////////////////////////////
   // Generate core clock lock signal if CPA lock isn't used
   generate
      if (DIAG_USE_CPA_LOCK)
      begin : use_cpa_lock
         assign counter_lock = 1'b0;
      end
      else
      begin : use_counter_lock
         if (PHY_CORE_CLKS_SHARING_ENUM == "CORE_CLKS_SHARING_SLAVE")
         begin : counter_lock_gen_slave
            assign counter_lock = counter_lock_slave_in;
         end else
         begin : counter_lock_gen_master

            // Synchronize PLL lock signal to PLL ref clock domain.
            // This may not be necessary but we do it for extra safety.
            logic pll_ref_clk_reset_n;
            logic pll_ref_clk_reset_n_sync_r;
            logic pll_ref_clk_reset_n_sync_rr;
            logic pll_ref_clk_reset_n_sync_rrr;

            assign pll_ref_clk_reset_n = pll_ref_clk_reset_n_sync_rrr;

            always_ff @(posedge pll_ref_clk_int or negedge pll_locked_int) begin
               if (~pll_locked_int) begin
                  pll_ref_clk_reset_n_sync_r   <= 1'b0;
                  pll_ref_clk_reset_n_sync_rr  <= 1'b0;
                  pll_ref_clk_reset_n_sync_rrr <= 1'b0;
               end else begin
                  pll_ref_clk_reset_n_sync_r   <= 1'b1;
                  pll_ref_clk_reset_n_sync_rr  <= pll_ref_clk_reset_n_sync_r;
                  pll_ref_clk_reset_n_sync_rrr <= pll_ref_clk_reset_n_sync_rr;
               end
            end

            // CPA takes ~50k core clock cycles to lock. Obviously we can't use a potentially
            // unstable core clock to clock the counter. We need to use the ref clock instead.
            // The fastest legal ref clock can run at the same rate as core clock, so we simply
            // count 64k PLL ref clock cycles.
            logic [16:0] cpa_count_to_lock;

            // The following is evaluated for simulation. Don't wait too long during simulation.
            // synthesis translate_off
            `define USE_SIM_COUNTER_LOCK_EXP TRUE
            // synthesis translate_on

            `ifdef USE_SIM_COUNTER_LOCK_EXP
               localparam COUNTER_LOCK_EXP = 9;
            `else
               localparam COUNTER_LOCK_EXP  = DIAG_SYNTH_FOR_SIM ? 9 : 16;
            `endif
            
            always_ff @(posedge pll_ref_clk_int or negedge pll_ref_clk_reset_n) begin
               if (~pll_ref_clk_reset_n) begin
                  cpa_count_to_lock <= '0;
                  counter_lock <= 1'b0;
               end else begin
                  if (~cpa_count_to_lock[COUNTER_LOCK_EXP]) begin
                     cpa_count_to_lock <= cpa_count_to_lock + 1'b1;
                  end
                  counter_lock <= cpa_count_to_lock[COUNTER_LOCK_EXP];
               end
            end
         end
      end
   endgenerate

   /////////////////////////////////////////////////////////////
   // Generate CPA-based core clock signals
   logic [1:0] core_clks_from_cpa_pri_buffered;
   logic [1:0] core_clks_from_cpa_sec_buffered;

   /////////////////////////////////////////////////////////////
   // Assign signals for DFT
   assign dft_core_clk_locked = DIAG_USE_CPA_LOCK ? core_clks_locked_cpa_pri : {2{counter_lock}};
   assign dft_core_clk_buf_out = core_clks_from_cpa_pri_buffered;

   generate
      if (PHY_CONFIG_ENUM == "CONFIG_PHY_AND_HARD_CTRL")
      begin : clk_gen_hmc

         // If HMC is used, there's no AFI clock
         assign afi_half_clk = 1'b0;
         assign afi_clk      = 1'b0;

         if (USER_CLK_RATIO == 2 && C2P_P2C_CLK_RATIO == 4)
         begin : bridge_2x
            // For 2x-bridge mode, expose two core clocks:
            //    0) A half-rate clock (i.e. emif_usr_clk)
            //    1) A quarter-rate clock (i.e. emif_usr_half_clk)

            if (PHY_CORE_CLKS_SHARING_ENUM == "CORE_CLKS_SHARING_SLAVE")
            begin : clk_gen_slave
               assign core_clks_from_cpa_pri_buffered = {emif_usr_half_clk_slave_in, emif_usr_clk_slave_in};
               assign core_clks_from_cpa_sec_buffered = {emif_usr_half_clk_sec_slave_in, emif_usr_clk_sec_slave_in};
               assign core_clks_fb_to_cpa_pri = '0;
               assign core_clks_fb_to_cpa_sec = '0;
               assign cpa_lock_pri = cpa_lock_pri_slave_in;
               assign cpa_lock_sec = cpa_lock_sec_slave_in;
            end else
            begin : clk_gen_master

               // Fitter can automatically insert clock buffers as needed
               assign core_clks_from_cpa_pri_buffered[0] = core_clks_from_cpa_pri[0];
               assign core_clks_from_cpa_pri_buffered[1] = core_clks_from_cpa_pri[1];

               assign cpa_lock_pri = core_clks_locked_cpa_pri[0];
               assign core_clks_fb_to_cpa_pri = core_clks_from_cpa_pri_buffered;
               if (PHY_PING_PONG_EN) begin : gen_sec_clk
                  // Fitter can automatically insert clock buffers as needed
                  assign core_clks_from_cpa_sec_buffered[0] = core_clks_from_cpa_sec[0];
                  assign core_clks_from_cpa_sec_buffered[1] = core_clks_from_cpa_sec[1];

                  assign cpa_lock_sec = core_clks_locked_cpa_sec[0] & core_clks_locked_cpa_sec[1];
                  assign core_clks_fb_to_cpa_sec = core_clks_from_cpa_sec_buffered;

               end else begin : non_pp
                  assign cpa_lock_sec = 1'b0;
                  assign core_clks_fb_to_cpa_sec = '0;
                  assign core_clks_from_cpa_sec_buffered = '0;
               end
            end

            assign emif_usr_clk          = core_clks_from_cpa_pri_buffered[0];
            assign emif_usr_half_clk     = core_clks_from_cpa_pri_buffered[1];
            assign emif_usr_clk_sec      = core_clks_from_cpa_sec_buffered[0];
            assign emif_usr_half_clk_sec = core_clks_from_cpa_sec_buffered[1];

         end else
         begin : hr_qr

            // For half/quarter-rate, expose one core clock (i.e. emif_usr_clk)
            // running at the user-requested rate
            if (PHY_CORE_CLKS_SHARING_ENUM == "CORE_CLKS_SHARING_SLAVE")
            begin : clk_gen_slave
               assign core_clks_from_cpa_pri_buffered = {emif_usr_half_clk_slave_in, emif_usr_clk_slave_in};
               assign core_clks_from_cpa_sec_buffered = {emif_usr_half_clk_sec_slave_in, emif_usr_clk_sec_slave_in};
               assign core_clks_fb_to_cpa_pri = '0;
               assign core_clks_fb_to_cpa_sec = '0;
               assign cpa_lock_pri = cpa_lock_pri_slave_in;
               assign cpa_lock_sec = cpa_lock_sec_slave_in;
            end else
            begin : clk_gen_master

               // Fitter can automatically insert clock buffers as needed
               assign core_clks_from_cpa_pri_buffered[0] = core_clks_from_cpa_pri[0];

               if (DIAG_CPA_OUT_1_EN)
               begin : force_cpa_out_1_en
                  assign core_clks_from_cpa_pri_buffered[1] = core_clks_from_cpa_pri[1];
                  assign cpa_lock_pri = core_clks_locked_cpa_pri[0] & core_clks_locked_cpa_pri[1];

               end else begin : normal
                  assign core_clks_from_cpa_pri_buffered[1] = core_clks_from_cpa_pri_buffered[0];
                  assign cpa_lock_pri = core_clks_locked_cpa_pri[0];
               end

               assign core_clks_fb_to_cpa_pri = core_clks_from_cpa_pri_buffered;

               if (PHY_PING_PONG_EN) begin : gen_sec_clk
                  // Fitter can automatically insert clock buffers as needed
                  assign core_clks_from_cpa_sec_buffered[0] = core_clks_from_cpa_sec[0];

                  assign cpa_lock_sec = core_clks_locked_cpa_sec[0];
                  assign core_clks_fb_to_cpa_sec = core_clks_from_cpa_sec_buffered;
                  assign core_clks_from_cpa_sec_buffered[1] = core_clks_from_cpa_sec_buffered[0];

               end else begin : non_pp
                  assign cpa_lock_sec = 1'b0;
                  assign core_clks_fb_to_cpa_sec = '0;
                  assign core_clks_from_cpa_sec_buffered = '0;
               end
            end

            assign emif_usr_clk          = core_clks_from_cpa_pri_buffered[0];
            assign emif_usr_half_clk     = core_clks_from_cpa_pri_buffered[1];
            assign emif_usr_clk_sec      = core_clks_from_cpa_sec_buffered[0];
            assign emif_usr_half_clk_sec = core_clks_from_cpa_sec_buffered[1];

         end
      end else
      begin : clk_gen_non_hmc

         // If HMC isn't used, there's no emif_usr_* clocks
         assign emif_usr_clk          = 1'b0;
         assign emif_usr_half_clk     = 1'b0;
         assign emif_usr_clk_sec      = 1'b0;
         assign emif_usr_half_clk_sec = 1'b0;

         // Always expose both afi_clk and afi_half_clk
         if (PHY_CORE_CLKS_SHARING_ENUM == "CORE_CLKS_SHARING_SLAVE")
         begin : clk_gen_slave
            assign core_clks_from_cpa_pri_buffered = {afi_clk_slave_in, afi_half_clk_slave_in};
            assign core_clks_from_cpa_sec_buffered = '0;
            assign core_clks_fb_to_cpa_pri = '0;
            assign core_clks_fb_to_cpa_sec = '0;
            assign cpa_lock_pri = cpa_lock_pri_slave_in;
            assign cpa_lock_sec = cpa_lock_sec_slave_in;
         end else
         begin : clk_gen_master
            // Fitter can automatically insert clock buffers as needed
            assign core_clks_from_cpa_pri_buffered[0] = core_clks_from_cpa_pri[0];
            assign core_clks_from_cpa_pri_buffered[1] = core_clks_from_cpa_pri[1];

            assign core_clks_fb_to_cpa_pri = core_clks_from_cpa_pri_buffered;
            assign core_clks_fb_to_cpa_sec = '0;
            assign cpa_lock_pri = core_clks_locked_cpa_pri[0];
            assign cpa_lock_sec = 1'b0;
         end

         assign afi_clk      = core_clks_from_cpa_pri_buffered[0];
         assign afi_half_clk = 1'b0;
      end
   endgenerate

   /////////////////////////////////////////////////////////////
   // Generate core reset signals for CPA-based core clocks
   logic sync_clk_pri;
   logic sync_clk_sec;
   logic reset_sync_pri_pre_reg;
   logic reset_sync_sec_pre_reg;

   // Every interface flops the synchronized reset signal locally.
   // We do this so every interface has an anchor point that our SDC can use
   // as starting point to traverse the clock topology.
   // The flop is marked to prevent from being optimized away.
   (* altera_attribute = {"-name GLOBAL_SIGNAL ON"}*) logic reset_sync_pri_sdc_anchor /* synthesis dont_merge syn_noprune syn_preserve = 1 */;
   always_ff @(posedge sync_clk_pri or negedge async_reset_n_pri) begin
      if (~async_reset_n_pri) begin
         reset_sync_pri_sdc_anchor <= '0;
      end else begin
         reset_sync_pri_sdc_anchor <= reset_sync_pri_pre_reg;
      end
   end

   logic reset_sync_sec_sdc_anchor_ext;
   generate
      if (PHY_PING_PONG_EN) begin : pp
         (* altera_attribute = {"-name GLOBAL_SIGNAL ON"}*) logic reset_sync_sec_sdc_anchor /* synthesis dont_merge syn_noprune syn_preserve = 1 */;
         always_ff @(posedge sync_clk_sec or negedge async_reset_n_sec) begin
            if (~async_reset_n_sec) begin
               reset_sync_sec_sdc_anchor <= '0;
            end else begin
               reset_sync_sec_sdc_anchor <= reset_sync_sec_pre_reg;
            end
         end
         assign reset_sync_sec_sdc_anchor_ext = reset_sync_sec_sdc_anchor;
      end else begin : no_pp
         assign reset_sync_sec_sdc_anchor_ext = 1'b0;
      end
   endgenerate

   generate
      if (PHY_CONFIG_ENUM == "CONFIG_PHY_AND_HARD_CTRL")
      begin : reset_gen_hmc
         assign sync_clk_pri                 = emif_usr_clk;
         assign sync_clk_sec                 = emif_usr_clk_sec;
         assign emif_usr_reset_n_pri_pre_reg = reset_sync_pri_pre_reg;
         assign emif_usr_reset_n_sec_pre_reg = reset_sync_sec_pre_reg;
         assign emif_usr_reset_n             = reset_sync_pri_sdc_anchor;
         assign emif_usr_reset_n_sec         = reset_sync_sec_sdc_anchor_ext;
         assign afi_reset_n_pre_reg          = 1'b0;
         assign afi_reset_n                  = 1'b0;
      end else
      begin: reset_gen_non_hmc
         assign sync_clk_pri                 = afi_clk;
         assign sync_clk_sec                 = 1'b0;
         assign afi_reset_n_pre_reg          = reset_sync_pri_pre_reg;
         assign afi_reset_n                  = reset_sync_pri_sdc_anchor;
         assign emif_usr_reset_n_pri_pre_reg = 1'b0;
         assign emif_usr_reset_n             = 1'b0;
         assign emif_usr_reset_n_sec_pre_reg = 1'b0;
         assign emif_usr_reset_n_sec         = 1'b0;
      end

      if (PHY_CORE_CLKS_SHARING_ENUM == "CORE_CLKS_SHARING_SLAVE")
      begin : reset_gen_slave
         // The master exposes a synchronized reset signal for the slaves
         if (PHY_CONFIG_ENUM == "CONFIG_PHY_AND_HARD_CTRL") begin
            assign reset_sync_pri_pre_reg = emif_usr_reset_n_pri_pre_reg_slave_in;
            assign reset_sync_sec_pre_reg = emif_usr_reset_n_sec_pre_reg_slave_in;
         end else begin
            assign reset_sync_pri_pre_reg = afi_reset_n_pre_reg_slave_in;
            assign reset_sync_sec_pre_reg = 1'b0;
         end
      end else
      begin : reset_gen_master

         // Synchronize reset deassertion to core clock
         logic [CPA_RESET_SYNC_LENGTH-1:0] reset_sync_pri;
         always_ff @(posedge sync_clk_pri or negedge async_reset_n_pri) begin
            if (~async_reset_n_pri) begin
               reset_sync_pri <= '0;
            end else begin
               reset_sync_pri[0] <= 1'b1;
               reset_sync_pri[CPA_RESET_SYNC_LENGTH-1:1] <= reset_sync_pri[CPA_RESET_SYNC_LENGTH-2:0];
            end
         end
         assign reset_sync_pri_pre_reg = reset_sync_pri[CPA_RESET_SYNC_LENGTH-1];

         if (PHY_PING_PONG_EN) begin : gen_sec_rst_sync
            logic [CPA_RESET_SYNC_LENGTH-1:0] reset_sync_sec;
            always_ff @(posedge sync_clk_sec or negedge async_reset_n_sec) begin
               if (~async_reset_n_sec) begin
                  reset_sync_sec <= '0;
               end else begin
                  reset_sync_sec[0] <= 1'b1;
                  reset_sync_sec[CPA_RESET_SYNC_LENGTH-1:1] <= reset_sync_sec[CPA_RESET_SYNC_LENGTH-2:0];
               end
            end
            assign reset_sync_sec_pre_reg = reset_sync_sec[CPA_RESET_SYNC_LENGTH-1];
         end else begin : no_pp
            assign reset_sync_sec_pre_reg = 1'b0;
         end
      end
   endgenerate

   ///////////////////////////////////////////////////////////////////
   // Synchronize local_reset_req to core clock domain. This gives
   // users freedom to use an asynchonrous source for local_reset_req,
   // but with the extra requirement that the request pulse must be
   // at least 2 core clock cycles long.
   // Instantiate synchronizer at the master only and use the output
   // of the synchronizer to drive all slaves, to make sure that
   // the request gets to the sequencer at the exact same cycle for
   // all masters and slaves.
   generate
      if (PHY_CORE_CLKS_SHARING_ENUM == "CORE_CLKS_SHARING_SLAVE")
      begin : local_reset_req_sync_gen_slave
         assign local_reset_req_sync = 1'b0;
      end else
      begin : local_reset_req_sync_gen_master
         logic sync_clk;
         logic sync_reset_n;

         assign sync_clk     = (PHY_CONFIG_ENUM == "CONFIG_PHY_AND_HARD_CTRL") ? emif_usr_clk     : afi_clk;
         assign sync_reset_n = (PHY_CONFIG_ENUM == "CONFIG_PHY_AND_HARD_CTRL") ? emif_usr_reset_n : afi_reset_n;
         
         altera_std_synchronizer_nocut # (
            .depth     (LOCAL_RESET_REQ_SYNC_LENGTH),
            .rst_value (0)
         ) local_reset_req_sync_inst (
            .clk     (sync_clk),
            .reset_n (sync_reset_n),
            .din     (local_reset_req),
            .dout    (local_reset_req_sync)
         );         
      end
   endgenerate

endmodule
`ifdef QUESTA_INTEL_OEM
`pragma questa_oem_00 "EVeqkz9MvDzapiiVw7+udc++m43wu2P9R6Bkf/lfBn9ZttFzW71hzuu9P3yzPlvUUu1GESHEht8oUjkuxH5nYF5m2Y4yEaZOsor1W+qakklkcNM5gczDB8G/zUljAitcohcjlH9xX4F5r3RrLLQB1HrtXmnxKKrsVs2RsxKt4plRYJGUCxRjs6twKgr6lps1q22taZT7+7dZh7dYE0uKJfWB1PYeKR+rbOxvrAyMNm2gdRxeoq7YMd09J0Ox2d/MTEgLDbJ+E/3atnQdXbskMZMHQcqp+8mGKfqevapAP2IgQ+qIFxbK+YkgPvlocVbVuyZ9pe7XFS2l3zfsGznlSFOtxGDinGuQdWWREYMp7BJewXAOBa/csqcSb5Huo94qc0TuDmAaen0VgIPgnK7peyZnMWQVDb9uJYGkbg0nL6alMBr8S7yzVX7NlwvesdKqpXEsOh2zar4CTw1MEpW2UYbjJpQgNeFwrfBcvllGXlYSSCfUWbeXDc2MEuBYpW7cGljz+93O3fX5k9I4R6kM4BNrbAFl9GjyFYTEE6A5IKkUAWFAjEwa8vCMtuv//BKWyd4CZU5SDopV2XE9w1VFHcaAETfktskD0f4X7ARtdZUo8T+rtSFwTd0ePlpcJx88dq9knVDD0vs4Gh4+mQ+o2iy2B0v00/6ua9HYCoOgvvtjxBS2ZZeI75GOWRWA1fjjMWSk9QGi07g/qYZf3ouCaXt4br+GDf+b0hoVxkZbSBKSQv+l2z5R5hSEQwTKE4wdfVZ155ttLjSuWFObZGReDJWHfimwOH//LX8eGWlPcQZ8w7WtK1sQ8Rqc3uem43Lo5y/Q3CdGV2gx+i+lfIMfFa9/ruhzY9E4RjphYQqNkyqVPWiKc4CeOmGai0KnvtTKHZ1okAOVXov8P++VzhXrcaaMz+kiCDtylPGkm7AaX+TZWnVGIqqEYjDNXKO+8gcRHZOGM9cyCgAdmFCGG0wcIEyQiGm/tilN3Idf0WbyqMc14ZqNed/uW6gUOl5+jGAT"
`endif