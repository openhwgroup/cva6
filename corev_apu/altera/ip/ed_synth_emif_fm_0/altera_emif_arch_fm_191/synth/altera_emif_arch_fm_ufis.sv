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
// Wrapper module for C2P/P2C UFIs
///////////////////////////////////////////////////////////////////////////////

`define _get_db_pin_proc_mode_raw(_tile_i, _lane_i, _pin_i) ( DB_PINS_PROC_MODE[(_tile_i * LANES_PER_TILE * PINS_PER_LANE + _lane_i * PINS_PER_LANE + _pin_i) * 5 +: 5] )
`define _get_pin_usage(_tile_i, _lane_i, _pin_i)     ( LANE_PIN_USAGE[((_tile_i * LANES_PER_TILE * PINS_PER_LANE) + (_lane_i * PINS_PER_LANE) + _pin_i) * 4 +: 4] )
`define _get_lane_usage(_tile_i, _lane_i)            ( LANES_USAGE[(_tile_i * LANES_PER_TILE + _lane_i) * 3 +: 3] )
`define _is_lane_ac_or_empty(_tile_i, _lane_i)       ( `_get_lane_usage(_tile_i, _lane_i) == LANE_USAGE_UNUSED  ? 1 : ( \
                                                       `_get_lane_usage(_tile_i, _lane_i) == LANE_USAGE_AC_HMC  ? 1 : ( \
                                                       `_get_lane_usage(_tile_i, _lane_i) == LANE_USAGE_AC_CORE ? 1 : ( \
                                                                                                                  0   ))))
`define _is_clk_pin(_tile_i, _lane_i, _pin_i)        ( `_get_db_pin_proc_mode_raw(_tile_i, _lane_i, _pin_i) == DB_PIN_PROC_MODE_CLK   ? 1 : ( \
                                                       `_get_db_pin_proc_mode_raw(_tile_i, _lane_i, _pin_i) == DB_PIN_PROC_MODE_CLKB  ? 1 : ( \
                                                                                                                                        0   )))
module altera_emif_arch_fm_ufis #(
   parameter NUM_OF_RTL_TILES                        = 1,
   parameter LANES_PER_TILE                          = 1,
   parameter PINS_PER_LANE                           = 1,

   parameter PROTOCOL_ENUM                           = "",
   parameter AMM_C2P_UFI_MODE                        = "",
   parameter AMM_P2C_UFI_MODE                        = "",
   parameter MMR_C2P_UFI_MODE                        = "",
   parameter MMR_P2C_UFI_MODE                        = "",
   parameter SIDEBAND_C2P_UFI_MODE                   = "",
   parameter SIDEBAND_P2C_UFI_MODE                   = "",
   parameter SEQ_C2P_UFI_MODE                        = "",
   parameter SEQ_P2C_UFI_MODE                        = "",
   parameter ECC_C2P_UFI_MODE                        = "",
   parameter ECC_P2C_UFI_MODE                        = "",
   parameter LANE_C2P_UFI_MODE                       = "",
   parameter LANE_P2C_UFI_MODE                       = "",
   parameter LANE_PIN_USAGE                          = 0,
   parameter LANES_USAGE                             = 0,
   parameter DB_PINS_PROC_MODE                       = 0,

   parameter AMM_HIPI_DELAY                          = 225,
   parameter MMR_HIPI_DELAY                          = 225,
   parameter SIDEBAND_HIPI_DELAY                     = 225,
   parameter SEQ_HIPI_DELAY                          = 225,
   parameter ECC_HIPI_DELAY                          = 225,
   parameter LANE_HIPI_DELAY                         = 225,

   parameter ENABLE_RD_TYPE                          = 0,
   parameter PHY_PING_PONG_EN                        = 0,
   parameter NUM_OF_HMC_PORTS                        = 1,
   parameter PINS_C2L_DRIVEN                         = 0,
   parameter HMC_AVL_PROTOCOL_ENUM                   = "",
   parameter IS_HPS                                  = 0,
   parameter PRI_HMC_DBC_SHADOW_LANE_INDEX           = -1,
   parameter PRI_AC_TILE_INDEX                       = -1
) (
   input logic                                                                       ufi_phy_clk,
   input logic                                                                       ufi_core_clk,

   // Avalon interfaces between core and HMC
   input logic [62:0]                                                                i_core2ctl_avl_0,
   input logic [62:0]                                                                i_core2ctl_avl_1,
   input logic                                                                       i_core2ctl_avl_rd_data_ready_0,
   input logic                                                                       i_core2ctl_avl_rd_data_ready_1,
   input logic                                                                       i_ctl2core_avl_cmd_ready_0,
   input logic                                                                       i_ctl2core_avl_cmd_ready_1,
   input logic [12:0]                                                                i_ctl2core_avl_rdata_id_0,
   input logic [12:0]                                                                i_ctl2core_avl_rdata_id_1,
   output logic [62:0]                                                               actual_core2ctl_avl_0,
   output logic                                                                      actual_core2ctl_avl_rd_data_ready_0,
   output logic [62:0]                                                               actual_core2ctl_avl_1,
   output logic                                                                      actual_core2ctl_avl_rd_data_ready_1,
   output logic                                                                      actual_ctl2core_avl_cmd_ready_0,
   output logic                                                                      actual_ctl2core_avl_cmd_ready_1,
   output logic [12:0]                                                               actual_ctl2core_avl_rdata_id_0,
   output logic [12:0]                                                               actual_ctl2core_avl_rdata_id_1,

   // MMR signals between core and HMC
   input logic [33:0]                                                                i_ctl2core_mmr_0,
   input logic [50:0]                                                                i_core2ctl_mmr_0,
   input logic [33:0]                                                                i_ctl2core_mmr_1,
   input logic [50:0]                                                                i_core2ctl_mmr_1,
   output logic [33:0]                                                               actual_ctl2core_mmr_0,
   output logic [50:0]                                                               actual_core2ctl_mmr_0,
   output logic [33:0]                                                               actual_ctl2core_mmr_1,
   output logic [50:0]                                                               actual_core2ctl_mmr_1,

   // Side-band signals between core and HMC
   input logic [41:0]                                                                i_core2ctl_sideband_0,
   input logic [13:0]                                                                i_ctl2core_sideband_0,
   input logic [41:0]                                                                i_core2ctl_sideband_1,
   input logic [13:0]                                                                i_ctl2core_sideband_1,
   output logic [41:0]                                                               actual_core2ctl_sideband_0,
   output logic [13:0]                                                               actual_ctl2core_sideband_0,
   output logic [41:0]                                                               actual_core2ctl_sideband_1,
   output logic [13:0]                                                               actual_ctl2core_sideband_1,

   // sequencer signals between tile and core
   input logic [17:0]                                                                i_c2t_afi,
   input logic [26:0]                                                                i_t2c_afi,
   output logic [17:0]                                                               actual_c2t_afi,
   output logic [26:0]                                                               actual_t2c_afi,

   // Signals between core and data lanes
   input logic  [NUM_OF_RTL_TILES-1:0][LANES_PER_TILE-1:0][PINS_PER_LANE * 8 - 1:0]  i_core2l_data,
   input logic  [NUM_OF_RTL_TILES-1:0][LANES_PER_TILE-1:0][PINS_PER_LANE * 8 - 1:0]  i_l2core_data,
   input logic  [NUM_OF_RTL_TILES-1:0][LANES_PER_TILE-1:0][47:0]                     i_core2l_oe,
   input logic  [NUM_OF_RTL_TILES-1:0][LANES_PER_TILE-1:0][3:0]                      i_core2l_rdata_en_full,
   input logic  [NUM_OF_RTL_TILES-1:0][LANES_PER_TILE-1:0][7:0]                      i_core2l_mrnk_read,
   input logic  [NUM_OF_RTL_TILES-1:0][LANES_PER_TILE-1:0][7:0]                      i_core2l_mrnk_write,
   input logic                                                                       i_l2core_rd_type,
   input logic  [3:0]                                                                i_l2core_rdata_valid_pri,
   input logic  [3:0]                                                                i_l2core_rdata_valid_sec,

   output logic [NUM_OF_RTL_TILES-1:0][LANES_PER_TILE-1:0][PINS_PER_LANE * 8 - 1:0]  actual_l2core_data,
   output logic [NUM_OF_RTL_TILES-1:0][LANES_PER_TILE-1:0][PINS_PER_LANE * 8 - 1:0]  actual_core2l_data,
   output logic [NUM_OF_RTL_TILES-1:0][LANES_PER_TILE-1:0][47:0]                     actual_core2l_oe,
   output logic [NUM_OF_RTL_TILES-1:0][LANES_PER_TILE-1:0][3:0]                      actual_core2l_rdata_en_full,
   output logic [NUM_OF_RTL_TILES-1:0][LANES_PER_TILE-1:0][7:0]                      actual_core2l_mrnk_read,
   output logic [NUM_OF_RTL_TILES-1:0][LANES_PER_TILE-1:0][7:0]                      actual_core2l_mrnk_write,
   output logic                                                                      actual_l2core_rd_type,
   output logic [3:0]                                                                actual_l2core_rdata_valid_pri,
   output logic [3:0]                                                                actual_l2core_rdata_valid_sec,

   // ECC signals between core and lanes
   input logic                                                                       i_core2l_wr_data_vld_ast,
   input logic                                                                       i_core2l_rd_data_rdy_ast,
   input logic  [12:0]                                                               i_core2l_wr_ecc_info,
   input logic                                                                       i_l2core_wr_data_rdy_ast,
   input logic                                                                       i_l2core_rd_data_vld_avl,
   input logic  [11:0]                                                               i_l2core_wb_pointer_for_ecc,
   output logic [NUM_OF_RTL_TILES-1:0][LANES_PER_TILE-1:0]                           actual_core2l_wr_data_vld_ast,
   output logic [NUM_OF_RTL_TILES-1:0][LANES_PER_TILE-1:0]                           actual_core2l_rd_data_rdy_ast,
   output logic [NUM_OF_RTL_TILES-1:0][LANES_PER_TILE-1:0][12:0]                     actual_core2l_wr_ecc_info,
   output logic [11:0]                                                               actual_l2core_wb_pointer_for_ecc,
   output logic                                                                      actual_l2core_wr_data_rdy_ast,
   output logic                                                                      actual_l2core_rd_data_vld_avl

);

   localparam UFI_IN_OUT_DIRECT_L0 = "pin_ufi_use_in_direct_out_direct";
   localparam UFI_C2P_FIFO_OREG_L2 = "pin_ufi_use_delay_fifo_out_reg";
   localparam UFI_P2C_FIFO_OREG_L2 = "pin_ufi_use_fast_fifo_out_reg";

   typedef enum bit [2:0] {
      LANE_USAGE_UNUSED  = 3'b000,
      LANE_USAGE_AC_HMC  = 3'b001,
      LANE_USAGE_AC_CORE = 3'b010,
      LANE_USAGE_RDATA   = 3'b011,
      LANE_USAGE_WDATA   = 3'b100,
      LANE_USAGE_WRDATA  = 3'b101
   } LANE_USAGE;

   // Enum that defines the pin usage within a lane 
   typedef enum bit [3:0] {
      LANE_PIN_USAGE_MODE_UNUSED = 4'b0000,
      LANE_PIN_USAGE_MODE_DQ     = 4'b0001,
      LANE_PIN_USAGE_MODE_DQS    = 4'b0010,
      LANE_PIN_USAGE_MODE_DQSB   = 4'b0011,
      LANE_PIN_USAGE_MODE_CA_SDR = 4'b0100,
      LANE_PIN_USAGE_MODE_CA_DDR = 4'b0101,
      LANE_PIN_USAGE_MODE_DM     = 4'b1000,
      LANE_PIN_USAGE_MODE_DBI    = 4'b1001
   } LANE_PIN_USAGE_MODE;

   typedef enum bit [4:0] {
      DB_PIN_PROC_MODE_AC_CORE    = 5'b00000,
      DB_PIN_PROC_MODE_AC_IN_CORE = 5'b10100,
      DB_PIN_PROC_MODE_WDB_AC     = 5'b00001,
      DB_PIN_PROC_MODE_WDB_DQ     = 5'b00010,
      DB_PIN_PROC_MODE_WDB_DBI    = 5'b00011,
      DB_PIN_PROC_MODE_WDB_DM     = 5'b00100,
      DB_PIN_PROC_MODE_WDB_CLK    = 5'b00101,
      DB_PIN_PROC_MODE_WDB_CLKB   = 5'b00110,
      DB_PIN_PROC_MODE_WDB_DQS    = 5'b00111,
      DB_PIN_PROC_MODE_WDB_DQSB   = 5'b01000,
      DB_PIN_PROC_MODE_DQS        = 5'b01001,
      DB_PIN_PROC_MODE_DQSB       = 5'b01010,
      DB_PIN_PROC_MODE_DQ         = 5'b01011,
      DB_PIN_PROC_MODE_DM         = 5'b01100,
      DB_PIN_PROC_MODE_DBI        = 5'b01101,
      DB_PIN_PROC_MODE_CLK        = 5'b01110,
      DB_PIN_PROC_MODE_CLKB       = 5'b01111,
      DB_PIN_PROC_MODE_DQS_DDR4   = 5'b10000,
      DB_PIN_PROC_MODE_DQSB_DDR4  = 5'b10001,
      DB_PIN_PROC_MODE_RDQ        = 5'b10010,
      DB_PIN_PROC_MODE_RDQS       = 5'b10011,
      DB_PIN_PROC_MODE_GPIO       = 5'b11111
   } DB_PIN_PROC_MODE;


   generate
      genvar tile_i, lane_i, pin_i, phase_i, sig_i;
      logic [NUM_OF_RTL_TILES-1:0][LANES_PER_TILE-1:0][PINS_PER_LANE * 8 - 1:0]  ufi_core2l_data /* synthesis dont_merge*/;
      logic [NUM_OF_RTL_TILES-1:0][LANES_PER_TILE-1:0][47:0]                     ufi_core2l_oe /* synthesis dont_merge*/;
      logic [NUM_OF_RTL_TILES-1:0][LANES_PER_TILE-1:0][3:0]                      ufi_core2l_rdata_en_full /* synthesis dont_merge*/;
      logic [NUM_OF_RTL_TILES-1:0][LANES_PER_TILE-1:0][7:0]                      ufi_core2l_mrnk_read /* synthesis dont_merge*/;
      logic [NUM_OF_RTL_TILES-1:0][LANES_PER_TILE-1:0][7:0]                      ufi_core2l_mrnk_write /* synthesis dont_merge*/;
      logic [NUM_OF_RTL_TILES-1:0][LANES_PER_TILE-1:0][PINS_PER_LANE * 8 - 1:0]  ufi_l2core_data             /*synthesis dont_merge*/;

      logic [3:0]                                                                ufi_l2core_rdata_valid_pri /*synthesis dont_merge*/;
      logic [3:0]                                                                ufi_l2core_rdata_valid_sec /*synthesis dont_merge*/;
      logic                                                                      ufi_l2core_rd_data_vld_avl /*synthesis dont_merge*/;
      logic                                                                      ufi_l2core_rd_type /*synthesis dont_merge*/;

      logic [NUM_OF_RTL_TILES-1:0][LANES_PER_TILE-1:0]                           ufi_core2l_rd_data_rdy_ast /* synthesis dont_merge*/;
      logic [NUM_OF_RTL_TILES-1:0][LANES_PER_TILE-1:0]                           ufi_core2l_wr_data_vld_ast /* synthesis dont_merge*/;
      logic [NUM_OF_RTL_TILES-1:0][LANES_PER_TILE-1:0] [12:0]                    ufi_core2l_wr_ecc_info     /* synthesis dont_merge*/;
      logic                                                                      ufi_l2core_wr_data_rdy_ast  /*synthesis dont_merge*/;
      logic [11:0]                                                               ufi_l2core_wb_pointer_for_ecc /* synthesis dont_merge*/;

      logic [62:0]                                                               ufi_core2ctl_avl_0 /*synthesis dont_merge*/;
      logic                                                                      ufi_core2ctl_avl_rd_data_ready_0 /*synthesis dont_merge*/;
      logic                                                                      ufi_ctl2core_avl_cmd_ready_0 /*synthesis dont_merge*/;
      logic [12:0]                                                               ufi_ctl2core_avl_rdata_id_0 /*synthesis dont_merge*/;

      logic [62:0]                                                               ufi_core2ctl_avl_1 /*synthesis dont_merge*/;
      logic                                                                      ufi_core2ctl_avl_rd_data_ready_1 /* synthesis dont_merge*/;
      logic                                                                      ufi_ctl2core_avl_cmd_ready_1 /*synthesis dont_merge*/;
      logic [12:0]                                                               ufi_ctl2core_avl_rdata_id_1 /*synthesis dont_merge*/;

      logic [33:0]                                                               ufi_ctl2core_mmr_0 /*synthesis dont_merge*/;
      logic [50:0]                                                               ufi_core2ctl_mmr_0 /*synthesis dont_merge*/;
      logic [33:0]                                                               ufi_ctl2core_mmr_1 /*synthesis dont_merge*/;
      logic [50:0]                                                               ufi_core2ctl_mmr_1 /*synthesis dont_merge*/;

      logic [41:0]                                                               ufi_core2ctl_sideband_0 /*synthesis dont_merge*/;
      logic [13:0]                                                               ufi_ctl2core_sideband_0 /*synthesis dont_merge*/;
      logic [41:0]                                                               ufi_core2ctl_sideband_1 /*synthesis dont_merge*/;
      logic [13:0]                                                               ufi_ctl2core_sideband_1 /*synthesis dont_merge*/;

      logic [17:0]                                                               ufi_seq_core2ctl /*synthesis dont_merge*/;
      logic [26:0]                                                               ufi_seq_ctl2core /*synthesis dont_merge*/;


      for (sig_i = 0; sig_i < 18; ++sig_i) begin: sequencer_c2p_ufi_gen
        altera_emif_arch_fm_ufi_wrapper #(
          .MODE        ((PROTOCOL_ENUM == "PROTOCOL_QDR4") ? "pin_ufi_use_in_direct_out_direct" :  SEQ_C2P_UFI_MODE),
          .HIPI_DELAY  (SEQ_HIPI_DELAY),
          .IS_C2P      (1),
          .IS_HPS      (IS_HPS),
          .TIEOFF      (NUM_OF_HMC_PORTS > 0 && sig_i > 7)
        ) core2ctl_seq_c2p_ufi_i (
            .i_src_clk (ufi_core_clk),
            .i_dst_clk (ufi_phy_clk),
            .i_din     (i_c2t_afi[sig_i]),
            .o_dout    (ufi_seq_core2ctl[sig_i])
        );
      end

      for (sig_i = 0; sig_i < 27; ++sig_i) begin: sequencer_p2c_ufi_gen
        altera_emif_arch_fm_ufi_wrapper #(
          .MODE        (SEQ_P2C_UFI_MODE),
          .IS_HPS      (IS_HPS),
          .IS_C2P      (0)
        ) ctl2core_seq_p2c_ufi_i (
            .i_src_clk (ufi_phy_clk),
            .i_dst_clk (ufi_core_clk),
            .i_din     (i_t2c_afi[sig_i]),
            .o_dout    (ufi_seq_ctl2core[sig_i])
        );
      end
                  
      if (NUM_OF_HMC_PORTS == 0) begin: tie_off_hmc_ufis
         assign ufi_core2ctl_avl_0                  = '0;
         assign ufi_core2ctl_avl_1                  = '0;
         assign ufi_core2ctl_avl_rd_data_ready_0    = '1;
         assign ufi_ctl2core_avl_cmd_ready_0        = '1;
         assign ufi_ctl2core_avl_rdata_id_0         = '0;
         assign ufi_core2ctl_avl_rd_data_ready_1    = '1;
         assign ufi_ctl2core_avl_cmd_ready_1        = '1;
         assign ufi_ctl2core_avl_rdata_id_1         = '0;

         assign ufi_ctl2core_mmr_0                  = '0;
         assign ufi_ctl2core_mmr_1                  = '0;
         assign ufi_core2ctl_mmr_0                  = '0;
         assign ufi_core2ctl_mmr_1                  = '0;
         assign ufi_core2ctl_sideband_0             = '0;
         assign ufi_core2ctl_sideband_1             = '0;
         assign ufi_ctl2core_sideband_0             = '0;
         assign ufi_ctl2core_sideband_1             = '0;
      end else begin : generate_hmc_ufis 
         for (sig_i = 0; sig_i < 63; ++sig_i) begin: avl_ctl_ufi_gen
           altera_emif_arch_fm_ufi_wrapper #(
             .MODE      (AMM_C2P_UFI_MODE),
             .HIPI_DELAY(AMM_HIPI_DELAY),
             .IS_HPS    (IS_HPS),
             .IS_C2P    (1)
           ) avl0_amm_c2p_ufi_i (
               .i_src_clk (ufi_core_clk),
               .i_dst_clk (ufi_phy_clk),
               .i_din     (i_core2ctl_avl_0[sig_i]),
               .o_dout    (ufi_core2ctl_avl_0[sig_i])
           );
         
           if (PHY_PING_PONG_EN) begin : sec_avl_ctl_ufi_gen
             altera_emif_arch_fm_ufi_wrapper #(
                .MODE      (AMM_C2P_UFI_MODE),
                .HIPI_DELAY(AMM_HIPI_DELAY),
                .IS_HPS    (IS_HPS),
                .IS_C2P    (1)
              ) avl1_amm_c2p_ufi_i (
                 .i_src_clk (ufi_core_clk),
                 .i_dst_clk (ufi_phy_clk),
                 .i_din     (i_core2ctl_avl_1[sig_i]),
                 .o_dout    (ufi_core2ctl_avl_1[sig_i])
             );
           end
         end

          altera_emif_arch_fm_ufi_wrapper #(
              .MODE      (AMM_C2P_UFI_MODE),
              .HIPI_DELAY(AMM_HIPI_DELAY),
              .IS_HPS    (IS_HPS),
              .IS_C2P    (1)
          ) avl_rd_data_ready_0_amm_c2p_ufi_i (
              .i_src_clk (ufi_core_clk),
              .i_dst_clk (ufi_phy_clk),
              .i_din     (i_core2ctl_avl_rd_data_ready_0),
              .o_dout    (ufi_core2ctl_avl_rd_data_ready_0)
          );

          altera_emif_arch_fm_ufi_wrapper #(
              .MODE  (AMM_P2C_UFI_MODE),
              .IS_HPS(IS_HPS),
              .IS_C2P(0)
          ) avl_cmd_ready_0_amm_p2c_ufi_i (
              .i_src_clk (ufi_phy_clk),
              .i_dst_clk (ufi_core_clk),
              .i_din     (i_ctl2core_avl_cmd_ready_0),
              .o_dout    (ufi_ctl2core_avl_cmd_ready_0)
          );

          for (sig_i = 0; sig_i < 13; ++sig_i) begin : ctl2core_avl_rdata_id_0_ufi_gen
             altera_emif_arch_fm_ufi_wrapper #(
                .MODE  (AMM_P2C_UFI_MODE),
                .IS_HPS(IS_HPS),
                .IS_C2P(0)
             ) rdata_id_amm_p2c_ufi_i (
                .i_src_clk (ufi_phy_clk),
                .i_dst_clk (ufi_core_clk),
                .i_din     (i_ctl2core_avl_rdata_id_0[sig_i]),
                .o_dout    (ufi_ctl2core_avl_rdata_id_0[sig_i])
             );
          end

          if (PHY_PING_PONG_EN) begin : sec_avl_cmd_ufi_gen
             altera_emif_arch_fm_ufi_wrapper #(
                .MODE      (AMM_C2P_UFI_MODE),
                .HIPI_DELAY(AMM_HIPI_DELAY),
                .IS_HPS    (IS_HPS),
                .IS_C2P    (1)
             ) avl_rd_data_ready_1_amm_c2p_ufi_i (
                 .i_src_clk (ufi_core_clk),
                 .i_dst_clk (ufi_phy_clk),
                 .i_din     (i_core2ctl_avl_rd_data_ready_1),
                 .o_dout    (ufi_core2ctl_avl_rd_data_ready_1)
             );

             altera_emif_arch_fm_ufi_wrapper #(
                .MODE  (AMM_P2C_UFI_MODE),
                .IS_HPS(IS_HPS),
                .IS_C2P(0)
             ) avl_cmd_ready_1_amm_p2c_ufi_i (
                 .i_src_clk (ufi_phy_clk),
                 .i_dst_clk (ufi_core_clk),
                 .i_din     (i_ctl2core_avl_cmd_ready_1),
                 .o_dout    (ufi_ctl2core_avl_cmd_ready_1)
             );

             for (sig_i = 0; sig_i < 13; ++sig_i) begin : ctl2core_avl_rdata_id_1_ufi_gen
               altera_emif_arch_fm_ufi_wrapper #(
                 .MODE  (AMM_P2C_UFI_MODE),
                 .IS_HPS(IS_HPS),
                 .IS_C2P(0)
               ) rdata_id_amm_p2c_ufi_i (
                 .i_src_clk (ufi_phy_clk),
                 .i_dst_clk(ufi_core_clk),
                 .i_din    (i_ctl2core_avl_rdata_id_1[sig_i]),
                 .o_dout   (ufi_ctl2core_avl_rdata_id_1[sig_i])
               );
             end
          end

          for (sig_i = 0; sig_i < 34; ++sig_i) begin: ctl2core_mmr_ufi_gen
              altera_emif_arch_fm_ufi_wrapper #(
                .MODE  (MMR_P2C_UFI_MODE),
                .IS_HPS(IS_HPS),
                .IS_C2P(0)
              ) mmr_p2c_ufi_i (
                  .i_src_clk (ufi_phy_clk),
                  .i_dst_clk(ufi_core_clk),
                  .i_din    (i_ctl2core_mmr_0[sig_i]),
                  .o_dout   (ufi_ctl2core_mmr_0[sig_i])
              );

              if (PHY_PING_PONG_EN) begin : sec_ctl2core_mmr_ufi_gen
                 altera_emif_arch_fm_ufi_wrapper #(
                   .MODE  (MMR_P2C_UFI_MODE),
                   .IS_HPS(IS_HPS),
                   .IS_C2P(0)
                 ) mmr_p2c_ufi_i (
                     .i_src_clk (ufi_phy_clk),
                     .i_dst_clk(ufi_core_clk),
                     .i_din    (i_ctl2core_mmr_1[sig_i]),
                     .o_dout   (ufi_ctl2core_mmr_1[sig_i])
                 );
              end
          end

          for (sig_i = 0; sig_i < 51; ++sig_i) begin: core2ctl_mmr_ufi_gen
              altera_emif_arch_fm_ufi_wrapper #(
                .MODE      (MMR_C2P_UFI_MODE),
                .HIPI_DELAY(MMR_HIPI_DELAY),
                .IS_HPS    (IS_HPS),
                .IS_C2P    (1)
              ) mmr_c2p_ufi_i(
                  .i_src_clk (ufi_core_clk),
                  .i_dst_clk(ufi_phy_clk),
                  .i_din    (i_core2ctl_mmr_0[sig_i]),
                  .o_dout   (ufi_core2ctl_mmr_0[sig_i])
              );

              if (PHY_PING_PONG_EN) begin : sec_core2ctl_mmr_ufi_gen
                altera_emif_arch_fm_ufi_wrapper #(
                  .MODE      (MMR_C2P_UFI_MODE),
                  .HIPI_DELAY(MMR_HIPI_DELAY),
                  .IS_HPS    (IS_HPS),
                  .IS_C2P    (1)
                ) mmr_c2p_ufi_i (
                    .i_src_clk (ufi_core_clk),
                    .i_dst_clk(ufi_phy_clk),
                    .i_din    (i_core2ctl_mmr_1[sig_i]),
                    .o_dout   (ufi_core2ctl_mmr_1[sig_i])
                );
              end
          end

          for (sig_i = 0; sig_i < 42; ++sig_i) begin: core2ctl_sideband_ufi_gen
            altera_emif_arch_fm_ufi_wrapper #(
              .MODE      ((sig_i < 27) ? (sig_i == 20) ? UFI_IN_OUT_DIRECT_L0 : SIDEBAND_C2P_UFI_MODE : ECC_C2P_UFI_MODE),
              .HIPI_DELAY((sig_i < 27) ? SIDEBAND_HIPI_DELAY : ECC_HIPI_DELAY),
              .IS_HPS    (IS_HPS),
              .IS_C2P    (1)
            ) sideband_c2p_ufi_i (
                .i_src_clk (ufi_core_clk),
                .i_dst_clk(ufi_phy_clk),
                .i_din    (i_core2ctl_sideband_0[sig_i]),
                .o_dout   (ufi_core2ctl_sideband_0[sig_i])
            );

            if (PHY_PING_PONG_EN) begin : sec_ufi_gen
              altera_emif_arch_fm_ufi_wrapper #(
                .MODE      ((sig_i < 27) ? SIDEBAND_C2P_UFI_MODE : ECC_C2P_UFI_MODE),
                .HIPI_DELAY((sig_i < 27) ? SIDEBAND_HIPI_DELAY : ECC_HIPI_DELAY),
                .IS_HPS    (IS_HPS),
                .IS_C2P    (1)
              ) sideband_c2p_ufi_i (
                  .i_src_clk (ufi_core_clk),
                  .i_dst_clk(ufi_phy_clk),
                  .i_din    (i_core2ctl_sideband_1[sig_i]),
                  .o_dout   (ufi_core2ctl_sideband_1[sig_i])
              );
            end
          end

          for (sig_i = 0; sig_i < 14; ++sig_i) begin: ctl2core_sideband_ufi_gen
              altera_emif_arch_fm_ufi_wrapper #(
                .MODE   ((sig_i < 6 || sig_i == 12) ? ECC_P2C_UFI_MODE : SIDEBAND_P2C_UFI_MODE),
                .IS_HPS (IS_HPS),
                .IS_C2P (0)
              ) sideband_p2c_ufi_i (
                  .i_src_clk(ufi_phy_clk),
                  .i_dst_clk(ufi_core_clk),
                  .i_din    (i_ctl2core_sideband_0[sig_i]),
                  .o_dout   (ufi_ctl2core_sideband_0[sig_i])
              );
              if (PHY_PING_PONG_EN) begin : sec_ctl2core_sideband_ufi_gen
                altera_emif_arch_fm_ufi_wrapper #(
                  .MODE   ((sig_i < 6 || sig_i == 12) ? ECC_P2C_UFI_MODE : SIDEBAND_P2C_UFI_MODE),
                  .IS_HPS(IS_HPS),
                  .IS_C2P(0)
                ) sideband_p2c_ufi_i (
                    .i_src_clk(ufi_phy_clk),
                    .i_dst_clk(ufi_core_clk),
                    .i_din    (i_ctl2core_sideband_1[sig_i]),
                    .o_dout   (ufi_ctl2core_sideband_1[sig_i])
                );
              end
          end
      end 
      

      assign actual_core2ctl_avl_0               = ufi_core2ctl_avl_0;
      assign actual_ctl2core_avl_cmd_ready_0     = ufi_ctl2core_avl_cmd_ready_0;
      assign actual_ctl2core_avl_rdata_id_0      = ufi_ctl2core_avl_rdata_id_0;
      assign actual_core2ctl_avl_rd_data_ready_0 = ufi_core2ctl_avl_rd_data_ready_0 ;

      assign actual_ctl2core_mmr_0               = ufi_ctl2core_mmr_0;
      assign actual_core2ctl_mmr_0               = ufi_core2ctl_mmr_0;
      assign actual_core2ctl_sideband_0          = ufi_core2ctl_sideband_0;
      assign actual_ctl2core_sideband_0          = ufi_ctl2core_sideband_0;

      assign actual_c2t_afi                      = ufi_seq_core2ctl;
      assign actual_t2c_afi                      = ufi_seq_ctl2core;

      if (PHY_PING_PONG_EN) begin : sec_tie_offs
        assign actual_ctl2core_mmr_1               = ufi_ctl2core_mmr_1;
        assign actual_core2ctl_mmr_1               = ufi_core2ctl_mmr_1;
        assign actual_core2ctl_sideband_1          = ufi_core2ctl_sideband_1;
        assign actual_ctl2core_sideband_1          = ufi_ctl2core_sideband_1;
        assign actual_core2ctl_avl_1               = ufi_core2ctl_avl_1;
        assign actual_ctl2core_avl_cmd_ready_1     = ufi_ctl2core_avl_cmd_ready_1;
        assign actual_ctl2core_avl_rdata_id_1      = ufi_ctl2core_avl_rdata_id_1;
        assign actual_core2ctl_avl_rd_data_ready_1 = ufi_core2ctl_avl_rd_data_ready_1;
      end else begin : no_ufis
        assign actual_ctl2core_mmr_1               = i_ctl2core_mmr_1;
        assign actual_core2ctl_mmr_1               = i_core2ctl_mmr_1;
        assign actual_core2ctl_sideband_1          = i_core2ctl_sideband_1;
        assign actual_ctl2core_sideband_1          = i_ctl2core_sideband_1;
        assign actual_core2ctl_avl_1               = i_core2ctl_avl_1;
        assign actual_ctl2core_avl_cmd_ready_1     = i_ctl2core_avl_cmd_ready_1;
        assign actual_ctl2core_avl_rdata_id_1      = i_ctl2core_avl_rdata_id_1;
        assign actual_core2ctl_avl_rd_data_ready_1 = i_core2ctl_avl_rd_data_ready_1;
      end

      if (NUM_OF_HMC_PORTS > 0) begin : p2c_per_if_hmc_ufi_gen
         altera_emif_arch_fm_ufi_wrapper #(
            .MODE  (LANE_P2C_UFI_MODE),
            .IS_HPS(IS_HPS),
            .IS_C2P(0)
         ) rd_data_vld_avl_lane_p2c_ufi_i (
             .i_src_clk (ufi_phy_clk),
             .i_dst_clk(ufi_core_clk),
             .i_din    (i_l2core_rd_data_vld_avl),
             .o_dout   (ufi_l2core_rd_data_vld_avl)
         );

         altera_emif_arch_fm_ufi_wrapper #(
            .MODE  (LANE_P2C_UFI_MODE),
            .IS_HPS(IS_HPS),
            .IS_C2P(0),
            .TIEOFF(ENABLE_RD_TYPE)
         ) rd_type_avl_lane_p2c_ufi_i (
             .i_src_clk (ufi_phy_clk),
             .i_dst_clk (ufi_core_clk),
             .i_din     (i_l2core_rd_type),
             .o_dout    (ufi_l2core_rd_type)
         );
      
         if (HMC_AVL_PROTOCOL_ENUM == "CTRL_AVL_PROTOCOL_ST") begin : p2c_ecc_ufi_gen
            altera_emif_arch_fm_ufi_wrapper #(
               .MODE  (ECC_P2C_UFI_MODE),
               .IS_HPS(IS_HPS),
               .IS_C2P(0)
            ) wr_data_rdy_ast_ecc_p2c_ufi_i (
               .i_src_clk (ufi_phy_clk),
               .i_dst_clk(ufi_core_clk),
               .i_din    (i_l2core_wr_data_rdy_ast),
               .o_dout   (ufi_l2core_wr_data_rdy_ast)
            );
            for (sig_i = 0; sig_i < 12; ++sig_i) begin : ecc_wb_ptr_gen
                altera_emif_arch_fm_ufi_wrapper #(
                  .MODE  (ECC_P2C_UFI_MODE),
                  .IS_HPS(IS_HPS),
                  .IS_C2P(0)
                ) wb_ptr_ecc_p2c_ufi_i(
                   .i_src_clk (ufi_phy_clk),
                   .i_dst_clk(ufi_core_clk),
                   .i_din    (i_l2core_wb_pointer_for_ecc[sig_i]),
                   .o_dout   (ufi_l2core_wb_pointer_for_ecc[sig_i])
                );
            end
         end else begin : p2c_ecc_tie_off
            assign ufi_l2core_wr_data_rdy_ast = i_l2core_wr_data_rdy_ast;
            assign ufi_l2core_wb_pointer_for_ecc = 12'b0;
         end
            
         assign ufi_l2core_rdata_valid_pri = '0;
         assign ufi_l2core_rdata_valid_sec = '0;

      end else begin : p2c_per_if_smc
         for (sig_i = 0; sig_i < 4; ++sig_i) begin: rvalid_ufi_gen
             altera_emif_arch_fm_ufi_wrapper #(
               .MODE  (LANE_P2C_UFI_MODE),
               .IS_HPS(IS_HPS),
               .IS_C2P(0)
             ) pri_rvalid_lane_p2c_ufi_i (
               .i_src_clk (ufi_phy_clk),
               .i_dst_clk(ufi_core_clk),
               .i_din    (i_l2core_rdata_valid_pri[sig_i]),
               .o_dout   (ufi_l2core_rdata_valid_pri[sig_i])
             );

             altera_emif_arch_fm_ufi_wrapper #(
               .MODE  (LANE_P2C_UFI_MODE),
               .IS_HPS(IS_HPS),
               .IS_C2P(0)
             ) sec_rvalid_lane_p2c_ufi_i (
               .i_src_clk (ufi_phy_clk),
               .i_dst_clk(ufi_core_clk),
               .i_din    (i_l2core_rdata_valid_sec[sig_i]),
               .o_dout   (ufi_l2core_rdata_valid_sec[sig_i])
             );
         end

         assign ufi_l2core_wb_pointer_for_ecc = '0;
         assign ufi_l2core_wr_data_rdy_ast = '0;
         assign ufi_l2core_rd_data_vld_avl = '0;
         assign ufi_l2core_rd_type = '0;
      end

      for (tile_i = 0; tile_i < NUM_OF_RTL_TILES; ++tile_i) begin: tile_gen
         for (lane_i = 0; lane_i < LANES_PER_TILE; ++lane_i) begin: lane_gen
             localparam AC_TIE_OFF = `_is_lane_ac_or_empty(tile_i, lane_i) || (NUM_OF_HMC_PORTS != 0);

             for (sig_i = 0; sig_i < 48; ++sig_i) begin: oe_ufi_gen
                altera_emif_arch_fm_ufi_wrapper # (
                 .MODE      (LANE_C2P_UFI_MODE),
                 .HIPI_DELAY(LANE_HIPI_DELAY),
                 .IS_HPS    (IS_HPS),
                 .IS_C2P    (1),
                 .TIEOFF    (AC_TIE_OFF)
                ) oe_lane_c2p_ufi_i (
                  .i_src_clk (ufi_core_clk),
                  .i_dst_clk(ufi_phy_clk),
                  .i_din    (i_core2l_oe[tile_i][lane_i][sig_i]),
                  .o_dout   (ufi_core2l_oe[tile_i][lane_i][sig_i])
                );
             end
             for (sig_i = 0; sig_i < 4; ++sig_i) begin: rdata_en_full_ufi_gen
               altera_emif_arch_fm_ufi_wrapper #(
                 .MODE      (LANE_C2P_UFI_MODE),
                 .HIPI_DELAY(LANE_HIPI_DELAY),
                 .IS_HPS    (IS_HPS),
                 .IS_C2P    (1),
                 .TIEOFF    (AC_TIE_OFF)
               ) rdata_en_lane_c2p_ufi_i (
                 .i_src_clk (ufi_core_clk),
                 .i_dst_clk(ufi_phy_clk),
                 .i_din    (i_core2l_rdata_en_full[tile_i][lane_i][sig_i]),
                 .o_dout   (ufi_core2l_rdata_en_full[tile_i][lane_i][sig_i])
               );
             end

            altera_emif_arch_fm_ufi_wrapper #(
               .MODE      (ECC_C2P_UFI_MODE),
               .HIPI_DELAY(LANE_HIPI_DELAY),
               .IS_HPS    (IS_HPS),
               .IS_C2P    (1),
               .TIEOFF    (HMC_AVL_PROTOCOL_ENUM != "CTRL_AVL_PROTOCOL_ST")
            ) wr_data_vld_ast_ecc_c2p_ufi_i (
               .i_src_clk (ufi_core_clk),
               .i_dst_clk(ufi_phy_clk),
               .i_din    (i_core2l_wr_data_vld_ast),
               .o_dout   (ufi_core2l_wr_data_vld_ast[tile_i][lane_i])
            );
            altera_emif_arch_fm_ufi_wrapper #(
               .MODE      (ECC_C2P_UFI_MODE),
               .HIPI_DELAY(LANE_HIPI_DELAY),
               .IS_HPS    (IS_HPS),
               .IS_C2P    (1),
               .TIEOFF    (HMC_AVL_PROTOCOL_ENUM != "CTRL_AVL_PROTOCOL_ST")
            ) rd_data_rdy_ast_ecc_c2p_ufi_i (
               .i_src_clk (ufi_core_clk),
               .i_dst_clk(ufi_phy_clk),
               .i_din    (i_core2l_rd_data_rdy_ast),
               .o_dout   (ufi_core2l_rd_data_rdy_ast[tile_i][lane_i])
            );

            for (sig_i = 0; sig_i < 8; ++sig_i) begin: mrnk_ufi_gen
              altera_emif_arch_fm_ufi_wrapper #(
                .MODE      ((PROTOCOL_ENUM == "PROTOCOL_QDR4") ?  "pin_ufi_use_in_direct_out_direct" : LANE_C2P_UFI_MODE),
                .HIPI_DELAY(LANE_HIPI_DELAY),
                .IS_HPS    (IS_HPS),
                .IS_C2P    (1),
                .TIEOFF    (NUM_OF_HMC_PORTS != 0)
              ) mrnk_read_lane_c2p_ufi_i (
                  .i_src_clk (ufi_core_clk),
                  .i_dst_clk(ufi_phy_clk),
                  .i_din    (i_core2l_mrnk_read[tile_i][lane_i][sig_i]),
                  .o_dout   (ufi_core2l_mrnk_read[tile_i][lane_i][sig_i])
              );
            
              altera_emif_arch_fm_ufi_wrapper #(
                .MODE      ((PROTOCOL_ENUM == "PROTOCOL_QDR4") ?  "pin_ufi_use_in_direct_out_direct" : LANE_C2P_UFI_MODE),
                .HIPI_DELAY(LANE_HIPI_DELAY),
                .IS_HPS    (IS_HPS),
                .IS_C2P    (1),
                .TIEOFF    (NUM_OF_HMC_PORTS != 0)
              ) mrnk_write_lane_c2p_ufi_i (
                  .i_src_clk (ufi_core_clk),
                  .i_dst_clk(ufi_phy_clk),
                  .i_din    (i_core2l_mrnk_write[tile_i][lane_i][sig_i]),
                  .o_dout   (ufi_core2l_mrnk_write[tile_i][lane_i][sig_i])
              );
            end
            
            for (sig_i = 0; sig_i < 13; ++sig_i) begin: ecc_info_gen
              altera_emif_arch_fm_ufi_wrapper #(
                 .MODE      (ECC_C2P_UFI_MODE),
                 .HIPI_DELAY(LANE_HIPI_DELAY),
                 .IS_HPS    (IS_HPS),
                 .IS_C2P    (1)
              ) info_ecc_c2p_ufi_i(
                .i_src_clk (ufi_core_clk),
                .i_dst_clk(ufi_phy_clk),
                .i_din    (i_core2l_wr_ecc_info[sig_i]),
                .o_dout   (ufi_core2l_wr_ecc_info[tile_i][lane_i][sig_i])
              );
            end

            for (pin_i = 0; pin_i < PINS_PER_LANE; ++pin_i) begin : pin_gen
               localparam phase_size = ((`_get_pin_usage(tile_i, lane_i, pin_i) == LANE_PIN_USAGE_MODE_CA_SDR) || `_is_clk_pin(tile_i, lane_i, pin_i)) ? 4 : 8;
                                         
               for (phase_i = 0; phase_i < 8; ++phase_i) begin : phase_gen
                   if ( (phase_i < phase_size) && PINS_C2L_DRIVEN[(LANES_PER_TILE * PINS_PER_LANE) * tile_i + PINS_PER_LANE * lane_i + pin_i] ) begin
                      altera_emif_arch_fm_ufi_wrapper #(
                        .MODE      (LANE_C2P_UFI_MODE),
                        .HIPI_DELAY(LANE_HIPI_DELAY),
                        .IS_HPS    (IS_HPS),
                        .IS_C2P    (1)
                      ) data_lane_c2p_ufi_i (
                          .i_src_clk (ufi_core_clk),
                          .i_dst_clk(ufi_phy_clk),
                          .i_din    (i_core2l_data[tile_i][lane_i][8 * pin_i + phase_i]),
                          .o_dout   (ufi_core2l_data[tile_i][lane_i][8 * pin_i + phase_i])
                      );

                      altera_emif_arch_fm_ufi_wrapper #(
                        .MODE   (LANE_P2C_UFI_MODE),
                        .IS_HPS (IS_HPS),
                        .IS_C2P (0),
                        .TIEOFF (NUM_OF_HMC_PORTS != 0 && pin_i==6)
                      ) data_lane_p2c_ufi_i (
                          .i_src_clk (ufi_phy_clk),
                          .i_dst_clk(ufi_core_clk),
                          .i_din    (i_l2core_data[tile_i][lane_i][8 * pin_i + phase_i]),
                          .o_dout   (ufi_l2core_data[tile_i][lane_i][8 * pin_i + phase_i])
                      );
                      assign actual_core2l_data[tile_i][lane_i][8 * pin_i + phase_i] = ufi_core2l_data[tile_i][lane_i][8 * pin_i + phase_i];
                      assign actual_l2core_data[tile_i][lane_i][8 * pin_i + phase_i] = ufi_l2core_data[tile_i][lane_i][8 * pin_i + phase_i];
                   end else begin
                      assign actual_core2l_data[tile_i][lane_i][8 * pin_i + phase_i] = i_core2l_data[tile_i][lane_i][8 * pin_i + phase_i];
                      assign actual_l2core_data[tile_i][lane_i][8 * pin_i + phase_i] = i_l2core_data[tile_i][lane_i][8 * pin_i + phase_i];
                   end
               end 
            end 
      end 
   end 

   assign actual_l2core_rd_type             = ufi_l2core_rd_type;
   assign actual_l2core_rd_data_vld_avl     = ufi_l2core_rd_data_vld_avl;
   assign actual_l2core_wr_data_rdy_ast     = ufi_l2core_wr_data_rdy_ast;
   assign actual_l2core_rdata_valid_pri     = ufi_l2core_rdata_valid_pri;
   assign actual_l2core_rdata_valid_sec     = ufi_l2core_rdata_valid_sec;

   assign actual_core2l_oe                  = ufi_core2l_oe;
   assign actual_core2l_rdata_en_full       = ufi_core2l_rdata_en_full;

   assign actual_core2l_mrnk_read           = ufi_core2l_mrnk_read;
   assign actual_core2l_mrnk_write          = ufi_core2l_mrnk_write;

   assign actual_l2core_wb_pointer_for_ecc = ufi_l2core_wb_pointer_for_ecc;
   assign actual_core2l_wr_ecc_info        = ufi_core2l_wr_ecc_info;
   assign actual_core2l_wr_data_vld_ast    = ufi_core2l_wr_data_vld_ast;
   assign actual_core2l_rd_data_rdy_ast    = ufi_core2l_rd_data_rdy_ast;

   endgenerate

endmodule
`ifdef QUESTA_INTEL_OEM
`pragma questa_oem_00 "EVeqkz9MvDzapiiVw7+udc++m43wu2P9R6Bkf/lfBn9ZttFzW71hzuu9P3yzPlvUUu1GESHEht8oUjkuxH5nYF5m2Y4yEaZOsor1W+qakklkcNM5gczDB8G/zUljAitcohcjlH9xX4F5r3RrLLQB1HrtXmnxKKrsVs2RsxKt4plRYJGUCxRjs6twKgr6lps1q22taZT7+7dZh7dYE0uKJfWB1PYeKR+rbOxvrAyMNm1oKyPZcd5kjMwa4n0A4xOKz9qUQXFQ2gsapiCXVq166BU40pq//T1QzfJs0GctI4nj1Erpj72AJVYt0W8FNaE2gvqBYaEuLSKK/cLcX1Tn+Fb0zPvgXEferiTC0FmH7ol0/9R49qrKwsilR8ei8imZrClUbsh3B4IPMQtYL7e7CfVgbKutVRXtalZ8kdfT68CAGOHXQ5V4it1DsH/6Kf7AvcsrY62eBO/AlP2Q3JeGdm2BHTnE36CCYvoDW3yQ793/di9qQUSqqrTpormr8eaRUqjEe6rtm/qR1N6a17IoxQlTL+ZoDMM6LakoRclnHpoM60IF68B/0p/4hNI7TwOp5GOzYyDLU9pnj8Mx2DPfT5eFNFelCqHahy7A5P2UTufFNCgAjYu8SFcPTf0czESrnO+5zk9XWi9ZZLIodOsXF6cwXwLWeCQmFQq/JhnUI07M7ayhRgJ+7ZwHsLwCUeHgOGs2eSzzVhK4NLLcJq//nKVDUHgFVZiH7Pnh8ySAok5iYHp0J5JTaOj88VaARTKkxJ2DnSSbUzf/3XOQdo5++Y8fBmyvdD35EVRaCxGT2IJxALaRV26PDlFvyV7sMQ/YOarJBF8g1hpXFT2hWwNclFhG797zReIWGNubwKALfQ/bpf+JIg/X0IDSzVrKxT8J8A5t4XYReZTPnaK2DPRutkzLiUT5aFULtAn3KXV50b4rH/Ewgzsuvmaxyxd6faq71tgfcEwaEGMk8IB6KbbMZUWMEr/TDuxy7etlpm7LhEV44rbyhJ+IoePTiEccCIQ1"
`endif