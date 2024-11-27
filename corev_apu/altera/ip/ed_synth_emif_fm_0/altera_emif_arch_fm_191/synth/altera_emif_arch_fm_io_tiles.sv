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
// This module instantiates one or more x48 I/O tiles (along with
// the necessary x12 I/O lanes) that are required to build as single EMIF.
//
///////////////////////////////////////////////////////////////////////////////

// Index to signal buses used to implement a daisy chain of
// (L0->L1->T0->L2->L3)->(L0->L1->T1->L2->L3)->...
`define _get_chain_index_for_tile(_tile_i)               ( _tile_i * (LANES_PER_TILE + 1) + 2 )

`define _get_chain_index_for_lane(_tile_i, _lane_i)      ( (_lane_i < 2) ? (_tile_i * (LANES_PER_TILE + 1) + _lane_i) : ( \
                                                                           (_tile_i * (LANES_PER_TILE + 1) + _lane_i + 1 )) )

// Index to signal buses used to implement a daisy chain of
// (L0->L1->L2->L3)->(L0->L1->L2->L3)->...
`define _get_broadcast_chain_index(_tile_i, _lane_i)     ( _tile_i * LANES_PER_TILE + _lane_i )

`define _get_lane_usage(_tile_i, _lane_i)                ( LANES_USAGE[(_tile_i * LANES_PER_TILE + _lane_i) * 3 +: 3] )

`define _get_pin_oct_mode_raw(_tile_i, _lane_i, _pin_i)  ( PINS_OCT_MODE[(_tile_i * LANES_PER_TILE * PINS_PER_LANE + _lane_i * PINS_PER_LANE + _pin_i)] )

`define _get_pin_ddr_raw(_tile_i, _lane_i, _pin_i)       ( PINS_RATE[_tile_i * LANES_PER_TILE * PINS_PER_LANE + _lane_i * PINS_PER_LANE + _pin_i] )
`define _get_pin_ddr_str(_tile_i, _lane_i, _pin_i)       ( `_get_pin_ddr_raw(_tile_i, _lane_i, _pin_i) == PIN_RATE_DDR ? "mode_ddr" : "mode_sdr" )

`define _get_lane_pin_usage_raw(_tile_i, _lane_i, _pin_i) ( LANE_PIN_USAGE[((_tile_i * LANES_PER_TILE * PINS_PER_LANE) + (_lane_i * PINS_PER_LANE) + _pin_i) * 4 +: 4] )

`define _get_lane_ddr_mode_str(_tile_i, _lane_i) ( `_get_lane_usage(_tile_i, _lane_i) == LANE_USAGE_UNUSED  ? "lane_ddr_notddr" : ( \
                                                   `_get_lane_usage(_tile_i, _lane_i) == LANE_USAGE_AC_HMC  ? "lane_ddr_ca_sdr" : ( \
                                                   `_get_lane_usage(_tile_i, _lane_i) == LANE_USAGE_AC_CORE ? ((PROTOCOL_ENUM == "PROTOCOL_QDR4") ? "lane_ddr_ca_ddr" : "lane_ddr_ca_sdr") : ( \
                                                                                         DQS_BUS_MODE_ENUM == "DQS_BUS_MODE_X4" ? "lane_ddr_ddr2x4"  : ( \
                                                                                         DQS_BUS_MODE_ENUM == "DQS_BUS_MODE_X9_DINV" ? "lane_ddr_qdrx10"  : ( \
                                                                                         DQS_BUS_MODE_ENUM == "DQS_BUS_MODE_X18_DINV" ? "lane_ddr_qdrx10"  : ( \
                                                                                                                                        "lane_ddr_ddrx8"   )))))))

`define _get_dqs_group_width                             ( DQS_BUS_MODE_ENUM == "DQS_BUS_MODE_X4"       ? "x4" : ( \
                                                           DQS_BUS_MODE_ENUM == "DQS_BUS_MODE_X8_X9"    ? "x8" : ( \
                                                           DQS_BUS_MODE_ENUM == "DQS_BUS_MODE_X9_DINV"  ? "x8" : ( \
                                                           DQS_BUS_MODE_ENUM == "DQS_BUS_MODE_X16_X18"  ? "x16" : ( \
                                                           DQS_BUS_MODE_ENUM == "DQS_BUS_MODE_X18_DINV" ? "x16" : ( \
                                                           DQS_BUS_MODE_ENUM == "DQS_BUS_MODE_X32_X36"  ? "x32" : ( \
                                                                                                          "x8"    )))))))
                                                                                 
`define _get_lane_pin_mode_str(_tile_i, _lane_i, _pin_i)     ( `_get_lane_pin_usage_raw(_tile_i, _lane_i, _pin_i) == LANE_PIN_USAGE_MODE_UNUSED ? "pin_unused" : "pin_ddr" )
`define _get_lane_pin_ddr_mode_str(_tile_i, _lane_i, _pin_i) ( `_get_lane_pin_usage_raw(_tile_i, _lane_i, _pin_i) == LANE_PIN_USAGE_MODE_UNUSED ? "ddr_notddr" : ( \
                                                               `_get_lane_pin_usage_raw(_tile_i, _lane_i, _pin_i) == LANE_PIN_USAGE_MODE_DQ     ? "ddr_dq" : ( \
                                                               `_get_lane_pin_usage_raw(_tile_i, _lane_i, _pin_i) == LANE_PIN_USAGE_MODE_DQS    ? "ddr_dqs" : ( \
                                                               `_get_lane_pin_usage_raw(_tile_i, _lane_i, _pin_i) == LANE_PIN_USAGE_MODE_DQSB   ? "ddr_dqsb" : ( \
                                                               `_get_lane_pin_usage_raw(_tile_i, _lane_i, _pin_i) == LANE_PIN_USAGE_MODE_CA_SDR ? "ddr_ca_sdr" : ( \
                                                               `_get_lane_pin_usage_raw(_tile_i, _lane_i, _pin_i) == LANE_PIN_USAGE_MODE_CA_DDR ? "ddr_ca_ddr" : ( \
                                                               `_get_lane_pin_usage_raw(_tile_i, _lane_i, _pin_i) == LANE_PIN_USAGE_MODE_DM     ? "ddr_dm" : ( \
                                                                                                                                                  "ddr_notddr"   ))))))))
                                                                                              

`define _get_db_pin_proc_mode_raw(_tile_i, _lane_i, _pin_i)      ( DB_PINS_PROC_MODE[(_tile_i * LANES_PER_TILE * PINS_PER_LANE + _lane_i * PINS_PER_LANE + _pin_i) * 5 +: 5] )
`define _get_db_pin_proc_mode_str(_tile_i, _lane_i, _pin_i)      ( `_get_db_pin_proc_mode_raw(_tile_i, _lane_i, _pin_i) == DB_PIN_PROC_MODE_AC_CORE        ? "ac_core"       : ( \
                                                                   `_get_db_pin_proc_mode_raw(_tile_i, _lane_i, _pin_i) == DB_PIN_PROC_MODE_AC_IN_CORE     ? "ac_in_core"    : ( \
                                                                   `_get_db_pin_proc_mode_raw(_tile_i, _lane_i, _pin_i) == DB_PIN_PROC_MODE_WDB_AC         ? "ac_hmc"        : ( \
                                                                   `_get_db_pin_proc_mode_raw(_tile_i, _lane_i, _pin_i) == DB_PIN_PROC_MODE_WDB_DQ         ? "dq_wdb_mode"   : ( \
                                                                   `_get_db_pin_proc_mode_raw(_tile_i, _lane_i, _pin_i) == DB_PIN_PROC_MODE_WDB_DBI        ? "dbi_wdb_mode"  : ( \
                                                                   `_get_db_pin_proc_mode_raw(_tile_i, _lane_i, _pin_i) == DB_PIN_PROC_MODE_WDB_DM         ? "dm_wdb_mode"   : ( \
                                                                   `_get_db_pin_proc_mode_raw(_tile_i, _lane_i, _pin_i) == DB_PIN_PROC_MODE_WDB_CLK        ? "clk_wdb_mode"  : ( \
                                                                   `_get_db_pin_proc_mode_raw(_tile_i, _lane_i, _pin_i) == DB_PIN_PROC_MODE_WDB_CLKB       ? "clkb_wdb_mode" : ( \
                                                                   `_get_db_pin_proc_mode_raw(_tile_i, _lane_i, _pin_i) == DB_PIN_PROC_MODE_WDB_DQS        ? "dqs_wdb_mode"  : ( \
                                                                   `_get_db_pin_proc_mode_raw(_tile_i, _lane_i, _pin_i) == DB_PIN_PROC_MODE_WDB_DQSB       ? "dqsb_wdb_mode" : ( \
                                                                   `_get_db_pin_proc_mode_raw(_tile_i, _lane_i, _pin_i) == DB_PIN_PROC_MODE_DQS            ? "dqs_mode"      : ( \
                                                                   `_get_db_pin_proc_mode_raw(_tile_i, _lane_i, _pin_i) == DB_PIN_PROC_MODE_DQSB           ? "dqsb_mode"     : ( \
                                                                   `_get_db_pin_proc_mode_raw(_tile_i, _lane_i, _pin_i) == DB_PIN_PROC_MODE_DQ             ? "dq_mode"       : ( \
                                                                   `_get_db_pin_proc_mode_raw(_tile_i, _lane_i, _pin_i) == DB_PIN_PROC_MODE_DM             ? "dm_mode"       : ( \
                                                                   `_get_db_pin_proc_mode_raw(_tile_i, _lane_i, _pin_i) == DB_PIN_PROC_MODE_DBI            ? "dbi_mode"      : ( \
                                                                   `_get_db_pin_proc_mode_raw(_tile_i, _lane_i, _pin_i) == DB_PIN_PROC_MODE_CLK            ? "clk_mode"      : ( \
                                                                   `_get_db_pin_proc_mode_raw(_tile_i, _lane_i, _pin_i) == DB_PIN_PROC_MODE_CLKB           ? "clkb_mode"     : ( \
                                                                   `_get_db_pin_proc_mode_raw(_tile_i, _lane_i, _pin_i) == DB_PIN_PROC_MODE_DQS_DDR4       ? "dqs_ddr4_mode" : ( \
                                                                   `_get_db_pin_proc_mode_raw(_tile_i, _lane_i, _pin_i) == DB_PIN_PROC_MODE_DQSB_DDR4      ? "dqsb_ddr4_mode": ( \
                                                                   `_get_db_pin_proc_mode_raw(_tile_i, _lane_i, _pin_i) == DB_PIN_PROC_MODE_RDQ            ? "rdq_mode"      : ( \
                                                                   `_get_db_pin_proc_mode_raw(_tile_i, _lane_i, _pin_i) == DB_PIN_PROC_MODE_RDQS           ? "rdqs_mode"     : ( \
                                                                   `_get_db_pin_proc_mode_raw(_tile_i, _lane_i, _pin_i) == DB_PIN_PROC_MODE_GPIO           ? "gpio_mode"     : ( \
                                                                                                                                                             "dq_mode"         )))))))))))))))))))))))

`define _get_pin_oct_rt_str(_tile_i, _lane_i, _pin_i)   ( `_get_pin_oct_mode_raw(_tile_i, _lane_i, _pin_i) == PIN_OCT_STATIC_OFF  ? "static_oct_off" : ( \
                                                          `_get_pin_oct_mode_raw(_tile_i, _lane_i, _pin_i) == PIN_OCT_DYNAMIC     ? "static_oct_off" : ( \
                                                                                                                                    "static_oct_on" )))

`define _get_pin_dyn_oct_str(_tile_i, _lane_i, _pin_i)   ( `_get_pin_oct_mode_raw(_tile_i, _lane_i, _pin_i) == PIN_OCT_DYNAMIC  ? "dyn_oct_on" : ( \
                                                                                                                                  "dyn_oct_off" ))

`define _get_pin_data_in_mode_raw(_tile_i, _lane_i, _pin_i) ( PINS_DATA_IN_MODE[(_tile_i * LANES_PER_TILE * PINS_PER_LANE + _lane_i * PINS_PER_LANE + _pin_i) * 3 +: 3] )

`define _get_pin_data_in_mode_str(_tile_i, _lane_i, _pin_i) ( `_get_pin_data_in_mode_raw(_tile_i, _lane_i, _pin_i) == PIN_DATA_IN_MODE_DISABLED         ? "dq" : ( \
                                                              `_get_pin_data_in_mode_raw(_tile_i, _lane_i, _pin_i) == PIN_DATA_IN_MODE_SSTL_IN          ? "dq" : ( \
                                                              `_get_pin_data_in_mode_raw(_tile_i, _lane_i, _pin_i) == PIN_DATA_IN_MODE_LOOPBACK_IN      ? "dq" : ( \
                                                              `_get_pin_data_in_mode_raw(_tile_i, _lane_i, _pin_i) == PIN_DATA_IN_MODE_XOR_LOOPBACK_IN  ? "dq" : ( \
                                                              `_get_pin_data_in_mode_raw(_tile_i, _lane_i, _pin_i) == PIN_DATA_IN_MODE_DIFF_IN          ? "dq" : ( \
                                                              `_get_pin_data_in_mode_raw(_tile_i, _lane_i, _pin_i) == PIN_DATA_IN_MODE_DIFF_IN_AVL_OUT  ? "dq" : ( \
                                                              `_get_pin_data_in_mode_raw(_tile_i, _lane_i, _pin_i) == PIN_DATA_IN_MODE_DIFF_IN_X12_OUT  ? "dq" : ( \
                                                                                                                                                          "dqs"  ))))))))

`define _get_pin_dqs_mode_str(_tile_i, _lane_i, _pin_i)   ( (PROTOCOL_ENUM == "PROTOCOL_QDR2")                       ?  "dqs_sampler_b_a_rise" :  ( \
                                                            (DQS_BUS_MODE_ENUM == "DQS_BUS_MODE_X4") && (_pin_i > 5) ?  "dqs_sampler_b" : ( \
                                                                                                                        "dqs_sampler_a" )))

//  Given the tile and lane index of a lane, returns the index of the AC tile controlling
//  this lane. For non-ping-pong, return value is always PRI_AC_TILE_INDEX.
//  For ping-pong, return SEC_AC_TILE_INDEX for all tiles below tile at SEC_AC_TILE_INDEX,
//  and for lane 2 and 3 of tile SEC_AC_TILE_INDEX; return PRI_AC_TILE_INDEX otherwise.
//  This assumption must be consistent with the logical pin placement strategy in hwtcl.
`define _get_ac_tile_index(_tile_i, _lane_i)             ( (PHY_PING_PONG_EN && (_tile_i < SEC_AC_TILE_INDEX || (_tile_i == SEC_AC_TILE_INDEX && _lane_i < 2))) ? SEC_AC_TILE_INDEX : PRI_AC_TILE_INDEX )

//  The following account for latency incurred when cross tile boundaries
`define _get_dbc_pipe_lat(_tile_i, _lane_i)                       ( DBC_PIPE_LATS[(_tile_i * LANES_PER_TILE + _lane_i) * 4 +: 4] )
`define _get_db_ptr_pipe_depth_str(_tile_i, _lane_i)              ( DB_PTR_PIPELINE_DEPTHS[(_tile_i * LANES_PER_TILE + _lane_i) * 4 +: 4] == 4'b0000 ? "db_ptr_pipeline_depth_0" : \
                                                                    DB_PTR_PIPELINE_DEPTHS[(_tile_i * LANES_PER_TILE + _lane_i) * 4 +: 4] == 4'b0001 ? "db_ptr_pipeline_depth_1" : \
                                                                    DB_PTR_PIPELINE_DEPTHS[(_tile_i * LANES_PER_TILE + _lane_i) * 4 +: 4] == 4'b0010 ? "db_ptr_pipeline_depth_2" : \
                                                                    DB_PTR_PIPELINE_DEPTHS[(_tile_i * LANES_PER_TILE + _lane_i) * 4 +: 4] == 4'b0011 ? "db_ptr_pipeline_depth_3" : \
                                                                    DB_PTR_PIPELINE_DEPTHS[(_tile_i * LANES_PER_TILE + _lane_i) * 4 +: 4] == 4'b0100 ? "db_ptr_pipeline_depth_4" : \
                                                                                                                                                       "db_ptr_pipeline_depth_0")

`define _get_db_seq_rd_en_full_pipeline_raw(_tile_i, _lane_i)     ( DB_SEQ_RD_EN_FULL_PIPELINES[(_tile_i * LANES_PER_TILE + _lane_i) * 4 +: 4] )
`define _get_db_seq_rd_en_full_pipeline_str(_tile_i, _lane_i)     ( `_get_db_seq_rd_en_full_pipeline_raw(_tile_i, _lane_i) == 4'b0001 ? "db_seq_rd_en_full_pipeline_1" : \
                                                                    `_get_db_seq_rd_en_full_pipeline_raw(_tile_i, _lane_i) == 4'b0010 ? "db_seq_rd_en_full_pipeline_2" : \
                                                                    `_get_db_seq_rd_en_full_pipeline_raw(_tile_i, _lane_i) == 4'b0011 ? "db_seq_rd_en_full_pipeline_3" : \
                                                                    `_get_db_seq_rd_en_full_pipeline_raw(_tile_i, _lane_i) == 4'b0100 ? "db_seq_rd_en_full_pipeline_4" : \
                                                                    `_get_db_seq_rd_en_full_pipeline_raw(_tile_i, _lane_i) == 4'b0000 ? "db_seq_rd_en_full_pipeline_0" : \
                                                                                                                                        "db_seq_rd_en_full_pipeline_1")

`define _get_db_data_alignment_mode                      ( (NUM_OF_HMC_PORTS > 0) ? "align_ena" : "align_disable" )

`define _get_memory_standard                             ( PROTOCOL_ENUM == "PROTOCOL_DDR4"   ? "ddr4"    : ( \
                                                           PROTOCOL_ENUM == "PROTOCOL_QDR4"   ? "qdriv"   : ( \
                                                                                                "rldram3"  )))

`define _get_lane_mode_rate_in                           ( PHY_HMC_CLK_RATIO == 4 ? "in_rate_1_4" : ( \
                                                           PHY_HMC_CLK_RATIO == 2 ? "in_rate_1_2" : ( \
                                                                                    "in_rate_full" )))

`define _get_lane_mode_rate_out                          ( PLL_VCO_TO_MEM_CLK_FREQ_RATIO == 8 ? "out_rate_1_8" : ( \
                                                           PLL_VCO_TO_MEM_CLK_FREQ_RATIO == 4 ? "out_rate_1_4" : ( \
                                                           PLL_VCO_TO_MEM_CLK_FREQ_RATIO == 2 ? "out_rate_1_2" : ( \
                                                                                                "out_rate_full" ))))

`define _get_hmc_ctrl_mem_type                           ( PROTOCOL_ENUM == "PROTOCOL_DDR3"   ? "mem_type_ddr3"   : ( \
                                                           PROTOCOL_ENUM == "PROTOCOL_DDR4"   ? "mem_type_ddr4"   : ( \
                                                           PROTOCOL_ENUM == "PROTOCOL_QDR4"   ? "mem_type_default"   : ( \
                                                                                                "mem_type_lpddr3"   ))))

`define _get_hmc_or_smc                                  ( NUM_OF_HMC_PORTS == 0 ? "smc" : "hmc" )
`define _get_hmc_or_core                                 ( NUM_OF_HMC_PORTS == 0 ? "db_core" : "db_hmc" )
`define _get_hmc_or_core_physeq                          ( NUM_OF_HMC_PORTS == 0 ? "core" : "hmc" )

`define _get_hmc_cmd_rate                                ( PHY_HMC_CLK_RATIO == 4 ? "ctrl_cfg_cmd_rate_qr" : "ctrl_cfg_cmd_rate_hr" )
`define _get_dbc0_cmd_rate                               ( PHY_HMC_CLK_RATIO == 4 ? "dbc0_cfg_cmd_rate_qr" : "dbc0_cfg_cmd_rate_hr" )
`define _get_dbc1_cmd_rate                               ( PHY_HMC_CLK_RATIO == 4 ? "dbc1_cfg_cmd_rate_qr" : "dbc1_cfg_cmd_rate_hr" )
`define _get_dbc2_cmd_rate                               ( PHY_HMC_CLK_RATIO == 4 ? "dbc2_cfg_cmd_rate_qr" : "dbc2_cfg_cmd_rate_hr" )
`define _get_dbc3_cmd_rate                               ( PHY_HMC_CLK_RATIO == 4 ? "dbc3_cfg_cmd_rate_qr" : "dbc3_cfg_cmd_rate_hr" )

`define _get_hmc_protocol                                ( HMC_AVL_PROTOCOL_ENUM == "CTRL_AVL_PROTOCOL_MM" ? "ctrl_amm" : "ctrl_ast" )
`define _get_dbc0_protocol                               ( HMC_AVL_PROTOCOL_ENUM == "CTRL_AVL_PROTOCOL_MM" ? "dbc0_amm" : "dbc0_ast" )
`define _get_dbc1_protocol                               ( HMC_AVL_PROTOCOL_ENUM == "CTRL_AVL_PROTOCOL_MM" ? "dbc1_amm" : "dbc1_ast" )
`define _get_dbc2_protocol                               ( HMC_AVL_PROTOCOL_ENUM == "CTRL_AVL_PROTOCOL_MM" ? "dbc2_amm" : "dbc2_ast" )
`define _get_dbc3_protocol                               ( HMC_AVL_PROTOCOL_ENUM == "CTRL_AVL_PROTOCOL_MM" ? "dbc3_amm" : "dbc3_ast" )

`define _get_memory_burst_length                        ( PROTOCOL_ENUM == "PROTOCOL_RLD3" ? "bl2" : ( \
                                                           PROTOCOL_ENUM == "PROTOCOL_QDR2" ? "bl2" : ( \
                                                           PROTOCOL_ENUM == "PROTOCOL_QDR4" ? "bl2" : ( \
                                                           MEM_BURST_LENGTH == 2 ? "bl2"   : ( \
                                                           MEM_BURST_LENGTH == 4 ? "bl4"   : ( \
                                                           MEM_BURST_LENGTH == 8 ? "bl8"   : ( \
                                                                                   ""                   )))))))

`define _get_cpa_0_clk_divider                           ( (USER_CLK_RATIO * PLL_VCO_TO_MEM_CLK_FREQ_RATIO) == 1   ? "core_clk0_div1" : ( \
                                                           (USER_CLK_RATIO * PLL_VCO_TO_MEM_CLK_FREQ_RATIO) == 2   ? "core_clk0_div2" : ( \
                                                           (USER_CLK_RATIO * PLL_VCO_TO_MEM_CLK_FREQ_RATIO) == 4   ? "core_clk0_div4" : ( \
                                                           (USER_CLK_RATIO * PLL_VCO_TO_MEM_CLK_FREQ_RATIO) == 8   ? "core_clk0_div8" : ( \
                                                           (USER_CLK_RATIO * PLL_VCO_TO_MEM_CLK_FREQ_RATIO) == 16  ? "core_clk0_div16" : ( \
                                                           (USER_CLK_RATIO * PLL_VCO_TO_MEM_CLK_FREQ_RATIO) == 32  ? "core_clk0_div32" : ( \
                                                           (USER_CLK_RATIO * PLL_VCO_TO_MEM_CLK_FREQ_RATIO) == 64  ? "core_clk0_div64" : ( \
                                                                                                                     "core_clk0_div1"    ))))))))

// CPA output 0 - in HMC mode, matches emif_usr_clk; in non-HMC mode, since afi_half_clk is no longer used in FM, use the same clock ratio
`define _get_cpa_0_clk_ratio                             ( NUM_OF_HMC_PORTS > 0 ? USER_CLK_RATIO : (USER_CLK_RATIO) )

// CPA output 1 - always matches the C2P/P2C rate
`define _get_cpa_1_clk_ratio                             ( C2P_P2C_CLK_RATIO )
`define _get_pa_exponent_1                               ( (`_get_pa_exponent(`_get_cpa_1_clk_ratio)) )

// CPA output 0 - clock divider on PHY clock feedback.
//                Enable divide-by-2 whenever the core clock needs to run at half the speed of the feedback clock
`define _get_pa_feedback_divider_p0                      ( (`_get_cpa_0_clk_ratio == C2P_P2C_CLK_RATIO * 2) ? "fb_clk0_div2" : "fb_clk0_div1" )

// CPA output 0 - clock divider on core clock feedback.
//                Enable divide-by-2 whenever the core clock needs to run at 2x the speed of the feedback clock
`define _get_pa_feedback_divider_c0                      ( (`_get_cpa_0_clk_ratio * 2 == C2P_P2C_CLK_RATIO) ? "core_clk0_div2" : "core_clk0_div1" )

`define _get_dqsin(_tile_i, _lane_i)                     ( (`_get_lane_usage(_tile_i, _lane_i) != LANE_USAGE_RDATA && `_get_lane_usage(_tile_i, _lane_i) != LANE_USAGE_WDATA && `_get_lane_usage(_tile_i, _lane_i) != LANE_USAGE_WRDATA) ? 2'b0 : ( \
                                                           DQS_BUS_MODE_ENUM == "DQS_BUS_MODE_X4"       ? t2l_dqsbus_x4[_lane_i]  : ( \
                                                           DQS_BUS_MODE_ENUM == "DQS_BUS_MODE_X8_X9"    ? t2l_dqsbus_x8[_lane_i]  : ( \
                                                           DQS_BUS_MODE_ENUM == "DQS_BUS_MODE_X9_DINV"  ? t2l_dqsbus_x8[_lane_i]  : ( \
                                                           DQS_BUS_MODE_ENUM == "DQS_BUS_MODE_X16_X18"  ? t2l_dqsbus_x18[_lane_i] : ( \
                                                           DQS_BUS_MODE_ENUM == "DQS_BUS_MODE_X18_DINV" ? t2l_dqsbus_x18[_lane_i] : ( \
                                                           DQS_BUS_MODE_ENUM == "DQS_BUS_MODE_X32_X36"  ? t2l_dqsbus_x36[_lane_i] : ( \
                                                                                                                                    2'b0 ))))))))

`define _get_hmc_burst_length                            ( MEM_BURST_LENGTH == 2 ? 5'b00010   : ( \
                                                           MEM_BURST_LENGTH == 4 ? 5'b00100   : ( \
                                                           MEM_BURST_LENGTH == 8 ? 5'b01000   : ( \
                                                                                   5'b00000              ))))

// DBC Mux Scheme (non-ping-pong):
//
// Tiles above      :   switch0 = don't-care   dbc*_sel = switch1 (lower mux)
//                      switch1 = from lower
//
// AC Tile          :   switch0 = local        dbc*_sel = switch0 (upper mux)
//                      switch1 = local
//
// Tiles below      :   switch0 = from upper   dbc*_sel = switch0 (upper mux)
//                      switch1 = don't-care
//
`define _get_ctrl2dbc_switch_0_non_pp(_tile_i)             ( (_tile_i == PRI_AC_TILE_INDEX) ? "local_tile_dbc0" : ( \
                                                             (_tile_i <= PRI_AC_TILE_INDEX) ? "upper_tile_dbc0" : ( \
                                                                                              "lower_tile_dbc0" )))

`define _get_ctrl2dbc_switch_1_non_pp(_tile_i)             ( (_tile_i == PRI_AC_TILE_INDEX) ? "local_tile_dbc1" : ( \
                                                             (_tile_i >  PRI_AC_TILE_INDEX) ? "lower_tile_dbc1" : ( \
                                                                                              "upper_tile_dbc1" )))

`define _get_ctrl2dbc_sel_0_non_pp(_tile_i)                ( (_tile_i <= PRI_AC_TILE_INDEX) ? "upper_mux_dbc0" : "lower_mux_dbc0" )
`define _get_ctrl2dbc_sel_1_non_pp(_tile_i)                ( (_tile_i <= PRI_AC_TILE_INDEX) ? "upper_mux_dbc1" : "lower_mux_dbc1" )
`define _get_ctrl2dbc_sel_2_non_pp(_tile_i)                ( (_tile_i <= PRI_AC_TILE_INDEX) ? "upper_mux_dbc2" : "lower_mux_dbc2" )
`define _get_ctrl2dbc_sel_3_non_pp(_tile_i)                ( (_tile_i <= PRI_AC_TILE_INDEX) ? "upper_mux_dbc3" : "lower_mux_dbc3" )

// DBC Mux Scheme (ping-pong):
//
// Tiles above      :   switch0 = don't-care   dbc*_sel = switch1 (lower mux)
//                      switch1 = from lower
//
// Primary AC Tile  :   switch0 = local        dbc*_sel = switch1 (lower mux)
//                      switch1 = local
//
// Secondary AC Tile:   switch0 = local        dbc2_sel, dbc3_sel = switch0 (upper mux)
//                      switch1 = from upper   dbc0_sel, dbc1_sel = switch1 (lower mux)
//
// Tiles below      :   switch0 = from upper   dbc*_sel = switch0 (upper mux)
//                      switch1 = don't-care
//
`define _get_ctrl2dbc_switch_0_pp(_tile_i)               ( (_tile_i == PRI_AC_TILE_INDEX) ? "local_tile_dbc0" : ( \
                                                           (_tile_i == SEC_AC_TILE_INDEX) ? "local_tile_dbc0" : ( \
                                                           (_tile_i <  SEC_AC_TILE_INDEX) ? "upper_tile_dbc0" : ( \
                                                                                            "lower_tile_dbc0" ))))

`define _get_ctrl2dbc_switch_1_pp(_tile_i)               ( (_tile_i == PRI_AC_TILE_INDEX) ? "local_tile_dbc1" : ( \
                                                           (_tile_i == SEC_AC_TILE_INDEX) ? "upper_tile_dbc1" : ( \
                                                           (_tile_i >  PRI_AC_TILE_INDEX) ? "lower_tile_dbc1" : ( \
                                                                                            "upper_tile_dbc1" ))))

`define _get_ctrl2dbc_sel_0_pp(_tile_i)                  ( (_tile_i >= PRI_AC_TILE_INDEX) ? "lower_mux_dbc0" : ((_tile_i < SEC_AC_TILE_INDEX) ? "upper_mux_dbc0" : (`_get_ac_tile_index(_tile_i, 0) == PRI_AC_TILE_INDEX ? "lower_mux_dbc0" : "upper_mux_dbc0")) )
`define _get_ctrl2dbc_sel_1_pp(_tile_i)                  ( (_tile_i >= PRI_AC_TILE_INDEX) ? "lower_mux_dbc1" : ((_tile_i < SEC_AC_TILE_INDEX) ? "upper_mux_dbc1" : (`_get_ac_tile_index(_tile_i, 1) == PRI_AC_TILE_INDEX ? "lower_mux_dbc1" : "upper_mux_dbc1")) )
`define _get_ctrl2dbc_sel_2_pp(_tile_i)                  ( (_tile_i >= PRI_AC_TILE_INDEX) ? "lower_mux_dbc2" : ((_tile_i < SEC_AC_TILE_INDEX) ? "upper_mux_dbc2" : (`_get_ac_tile_index(_tile_i, 2) == PRI_AC_TILE_INDEX ? "lower_mux_dbc2" : "upper_mux_dbc2")) )
`define _get_ctrl2dbc_sel_3_pp(_tile_i)                  ( (_tile_i >= PRI_AC_TILE_INDEX) ? "lower_mux_dbc3" : ((_tile_i < SEC_AC_TILE_INDEX) ? "upper_mux_dbc3" : (`_get_ac_tile_index(_tile_i, 3) == PRI_AC_TILE_INDEX ? "lower_mux_dbc3" : "upper_mux_dbc3")) )

// DBC Mux Scheme (ping-pong and non-ping-pong)
`define _get_ctrl2dbc_switch_0(_tile_i)                  ( PHY_PING_PONG_EN ? `_get_ctrl2dbc_switch_0_pp(_tile_i) : `_get_ctrl2dbc_switch_0_non_pp(_tile_i) )
`define _get_ctrl2dbc_switch_1(_tile_i)                  ( PHY_PING_PONG_EN ? `_get_ctrl2dbc_switch_1_pp(_tile_i) : `_get_ctrl2dbc_switch_1_non_pp(_tile_i) )
`define _get_ctrl2dbc_sel_0(_tile_i)                     ( PHY_PING_PONG_EN ? `_get_ctrl2dbc_sel_0_pp(_tile_i)    : `_get_ctrl2dbc_sel_0_non_pp(_tile_i) )
`define _get_ctrl2dbc_sel_1(_tile_i)                     ( PHY_PING_PONG_EN ? `_get_ctrl2dbc_sel_1_pp(_tile_i)    : `_get_ctrl2dbc_sel_1_non_pp(_tile_i) )
`define _get_ctrl2dbc_sel_2(_tile_i)                     ( PHY_PING_PONG_EN ? `_get_ctrl2dbc_sel_2_pp(_tile_i)    : `_get_ctrl2dbc_sel_2_non_pp(_tile_i) )
`define _get_ctrl2dbc_sel_3(_tile_i)                     ( PHY_PING_PONG_EN ? `_get_ctrl2dbc_sel_3_pp(_tile_i)    : `_get_ctrl2dbc_sel_3_non_pp(_tile_i) )

// Select which DBC to use as shadow.
// For the primary HMC tile or non-Ping-Pong HMC tile, pick "dbc1_to_local" as it's guaranteed to be used by the interface (as an A/C lane).
// For the secondary HMC tile, which one we pick depends on which data lane in the tile belongs to the secondary interface.
`define _get_hmc_dbc2ctrl_sel_non_pp(_tile_i)            ( PRI_HMC_DBC_SHADOW_LANE_INDEX == 0 ? "dbc0_to_local" : ( \
                                                           PRI_HMC_DBC_SHADOW_LANE_INDEX == 1 ? "dbc1_to_local" : ( \
                                                           PRI_HMC_DBC_SHADOW_LANE_INDEX == 2 ? "dbc2_to_local" : ( \
                                                                                                "dbc3_to_local" ))))

`define _get_hmc_dbc2ctrl_sel_pp(_tile_i)                ( (_tile_i != SEC_AC_TILE_INDEX) ? `_get_hmc_dbc2ctrl_sel_non_pp(_tile_i) : ( \
                                                           (`_get_ac_tile_index(SEC_AC_TILE_INDEX, 0) == SEC_AC_TILE_INDEX) ? "dbc0_to_local" : ( \
                                                           (`_get_ac_tile_index(SEC_AC_TILE_INDEX, 1) == SEC_AC_TILE_INDEX) ? "dbc1_to_local" : ( \
                                                           (`_get_ac_tile_index(SEC_AC_TILE_INDEX, 2) == SEC_AC_TILE_INDEX) ? "dbc2_to_local" : ( \
                                                                                                                              "dbc3_to_local" )))))
`define _get_hmc_dbc2ctrl_sel(_tile_i)                   ( PHY_PING_PONG_EN ? `_get_hmc_dbc2ctrl_sel_pp(_tile_i) : `_get_hmc_dbc2ctrl_sel_non_pp(_tile_i) )

// ac_hmc is hard connectivity between HMC and A/C lanes
// The Fitter uses ac_hmc as a special connection to locate the A/C tile and lanes, regardless of whether HMC is used.
// Normally, we only connect these to lanes that are used as A/C, regardless of HMC or SMC.
`define _get_ac_hmc(_tile_i, _lane_i)                    ( (`_get_lane_usage(_tile_i, _lane_i) == LANE_USAGE_AC_HMC || \
                                                            `_get_lane_usage(_tile_i, _lane_i) == LANE_USAGE_AC_CORE) ? \
                                                            t2l_ac_hmc[lane_i] : 96'b0 )

// The following is evaluated for simulation. Don't wait too long during simulation.
`define _get_core2dbc_wr_data_vld(_tile_i, _lane_i)           ( ((`_get_lane_usage(_tile_i, _lane_i) == LANE_USAGE_WRDATA) || \
                                                                 (_lane_i == 0 && `_get_lane_usage(_tile_i, 0) == LANE_USAGE_AC_HMC && `_get_hmc_dbc2ctrl_sel(_tile_i) == "dbc0_to_local") || \
                                                                 (_lane_i == 1 && `_get_lane_usage(_tile_i, 1) == LANE_USAGE_AC_HMC && `_get_hmc_dbc2ctrl_sel(_tile_i) == "dbc1_to_local") || \
                                                                 (_lane_i == 2 && `_get_lane_usage(_tile_i, 2) == LANE_USAGE_AC_HMC && `_get_hmc_dbc2ctrl_sel(_tile_i) == "dbc2_to_local") || \
                                                                 (_lane_i == 3 && `_get_lane_usage(_tile_i, 3) == LANE_USAGE_AC_HMC && `_get_hmc_dbc2ctrl_sel(_tile_i) == "dbc3_to_local")) ? \
                                                                 core2l_wr_data_vld_ast[_tile_i][_lane_i] : 1'b0 )

`define _get_core2dbc_wr_ecc_info(_tile_i, _lane_i)           ( ((`_get_lane_usage(_tile_i, _lane_i) == LANE_USAGE_WRDATA) || \
                                                                 (_lane_i == 0 && `_get_lane_usage(_tile_i, 0) == LANE_USAGE_AC_HMC && `_get_hmc_dbc2ctrl_sel(_tile_i) == "dbc0_to_local") || \
                                                                 (_lane_i == 1 && `_get_lane_usage(_tile_i, 1) == LANE_USAGE_AC_HMC && `_get_hmc_dbc2ctrl_sel(_tile_i) == "dbc1_to_local") || \
                                                                 (_lane_i == 2 && `_get_lane_usage(_tile_i, 2) == LANE_USAGE_AC_HMC && `_get_hmc_dbc2ctrl_sel(_tile_i) == "dbc2_to_local") || \
                                                                 (_lane_i == 3 && `_get_lane_usage(_tile_i, 3) == LANE_USAGE_AC_HMC && `_get_hmc_dbc2ctrl_sel(_tile_i) == "dbc3_to_local")) ? \
                                                                  core2l_wr_ecc_info[_tile_i][_lane_i] : 13'b0 )

`define _get_core2dbc_rd_data_rdy(_tile_i, _lane_i)           ( ((`_get_lane_usage(_tile_i, _lane_i) == LANE_USAGE_WRDATA) || \
                                                                 (_lane_i == 0 && `_get_lane_usage(_tile_i, 0) == LANE_USAGE_AC_HMC && `_get_hmc_dbc2ctrl_sel(_tile_i) == "dbc0_to_local") || \
                                                                 (_lane_i == 1 && `_get_lane_usage(_tile_i, 1) == LANE_USAGE_AC_HMC && `_get_hmc_dbc2ctrl_sel(_tile_i) == "dbc1_to_local") || \
                                                                 (_lane_i == 2 && `_get_lane_usage(_tile_i, 2) == LANE_USAGE_AC_HMC && `_get_hmc_dbc2ctrl_sel(_tile_i) == "dbc2_to_local") || \
                                                                 (_lane_i == 3 && `_get_lane_usage(_tile_i, 3) == LANE_USAGE_AC_HMC && `_get_hmc_dbc2ctrl_sel(_tile_i) == "dbc3_to_local")) ? \
                                                                  core2l_rd_data_rdy_ast[_tile_i][_lane_i] : 1'b1 )

// core2dbc_rd_data_rdy needs to fanout to every data lane and also the lane denoted as shadow by _get_hmc_dbc2ctrl_sel
`define _get_center_tid(_tile_i)                         ( CENTER_TIDS[_tile_i * 9 +: 9] )
`define _get_hmc_tid(_tile_i)                            ( HMC_TIDS[_tile_i * 9 +: 9] )
`define _get_lane_tid(_tile_i, _lane_i)                  ( LANE_TIDS[(_tile_i * LANES_PER_TILE + _lane_i) * 9 +: 9] )

`define _get_preamble_track_dqs_enable_mode              ( PROTOCOL_ENUM == "PROTOCOL_DDR4"   ? "preamble_track_dqs_enable" : ( \
                                                           PROTOCOL_ENUM == "PROTOCOL_DDR3"   ? "preamble_track_dqs_enable" : ( \
                                                           PROTOCOL_ENUM == "PROTOCOL_LPDDR3" ? "preamble_track_dqs_enable" : ( \
                                                           PROTOCOL_ENUM == "PROTOCOL_RLD3"   ? "preamble_track_toggler" : ( \
                                                           PROTOCOL_ENUM == "PROTOCOL_QDR2"   ? "preamble_track_toggler" : ( \
                                                           PROTOCOL_ENUM == "PROTOCOL_QDR4"   ? "preamble_track_toggler" : ( \
                                                                                                "" )))))))

`define _get_pst_preamble_mode                           ( PROTOCOL_ENUM == "PROTOCOL_DDR4"   ? "ddr4_preamble" : ( \
                                                           PROTOCOL_ENUM == "PROTOCOL_DDR3"   ? "ddr3_preamble" : ( \
                                                           PROTOCOL_ENUM == "PROTOCOL_LPDDR3" ? "ddr3_preamble" : ( \
                                                           PROTOCOL_ENUM == "PROTOCOL_RLD3"   ? "ddr3_preamble" : ( \
                                                           PROTOCOL_ENUM == "PROTOCOL_QDR2"   ? "ddr3_preamble" : ( \
                                                           PROTOCOL_ENUM == "PROTOCOL_QDR4"   ? "ddr3_preamble" : ( \
                                                                                                "" )))))))
`define _get_pst_en_shrink                               ( PROTOCOL_ENUM == "PROTOCOL_DDR4"   ? "shrink_1_0" : ( \
                                                           PROTOCOL_ENUM == "PROTOCOL_DDR3"   ? "shrink_1_1" : ( \
                                                           PROTOCOL_ENUM == "PROTOCOL_LPDDR3" ? "shrink_1_1" : ( \
                                                           PROTOCOL_ENUM == "PROTOCOL_RLD3"   ? "shrink_0_1" : ( \
                                                           PROTOCOL_ENUM == "PROTOCOL_QDR2"   ? "shrink_0_1" : ( \
                                                           PROTOCOL_ENUM == "PROTOCOL_QDR4"   ? "shrink_0_1" : ( \
                                                                                              "" )))))))

`define _get_pa_filter_code                              ( "freq_1600" )

`define _get_a_filter_code                               ( "freq_16ghz" )

`define _get_pa_track_speed                              ( 5'h0c )

// Enable the per-lane hard DBI circuitry. Only intended to be used by DDR4 data lanes.
`define _get_dbi_wr_en(_tile_i, _lane_i)                 ((`_get_lane_usage(_tile_i, _lane_i) == LANE_USAGE_WRDATA) ? DBI_WR_ENABLE : "dbi_wr_dis")
`define _get_dbi_rd_en(_tile_i, _lane_i)                 ((`_get_lane_usage(_tile_i, _lane_i) == LANE_USAGE_WRDATA) ? DBI_RD_ENABLE : "dbi_rd_dis")

// Set it to enabled to data lanes (or multi-rank shadow would not work).
// Set it to disabled for address/command lanes.
`define _get_data_lane(_tile_i, _lane_i)                 ( ((`_get_lane_usage(_tile_i, _lane_i) == LANE_USAGE_WRDATA) || \
                                                            (`_get_lane_usage(_tile_i, _lane_i) == LANE_USAGE_WDATA) || \
                                                            (`_get_lane_usage(_tile_i, _lane_i) == LANE_USAGE_RDATA)) ? 1 : 0 )

`define _get_mrnk_write_mode(_tile_i, _lane_i)           ( (`_get_data_lane(_tile_i, _lane_i) == 1) ? "mrnk_write_enable" : "mrnk_write_disable" )

// Controls how early/late to enable Rt termination.
// Decimal to binary conversion required by Quartus.
`define _get_oct_size                                    ( (OCT_SIZE == 0 ) ? 4'b0000 : ( \
                                                           (OCT_SIZE == 1 ) ? 4'b0001 : ( \
                                                           (OCT_SIZE == 2 ) ? 4'b0010 : ( \
                                                           (OCT_SIZE == 3 ) ? 4'b0011 : ( \
                                                           (OCT_SIZE == 4 ) ? 4'b0100 : ( \
                                                           (OCT_SIZE == 5 ) ? 4'b0101 : ( \
                                                           (OCT_SIZE == 6 ) ? 4'b0110 : ( \
                                                           (OCT_SIZE == 7 ) ? 4'b0111 : ( \
                                                           (OCT_SIZE == 8 ) ? 4'b1000 : ( \
                                                           (OCT_SIZE == 9 ) ? 4'b1001 : ( \
                                                           (OCT_SIZE == 10) ? 4'b1010 : ( \
                                                           (OCT_SIZE == 11) ? 4'b1011 : ( \
                                                           (OCT_SIZE == 12) ? 4'b1100 : ( \
                                                           (OCT_SIZE == 13) ? 4'b1101 : ( \
                                                           (OCT_SIZE == 14) ? 4'b1110 : ( \
                                                                              4'b1111   ))))))))))))))))

`define _get_hmc_cb_tbp_reload_fix_en_n   ((PRI_HMC_3DS_EN == "enable") ? "disable" : "enable")
                                                                              
// Select primary or secondary HMC config
// For non-ping-pong and primary HMC of ping-pong, select primary
// For secondary HMC of ping-pong, select secondary
// For everything else, select primary
`define _sel_hmc_tile(_tile_i, _pri, _sec)            ( PHY_PING_PONG_EN ? (_tile_i <= SEC_AC_TILE_INDEX ? _sec : _pri) : _pri )

// Select primary/secondary/default HMC config
// For non-ping-pong and primary HMC of ping-pong, select primary
// For secondary HMC of ping-pong, select secondary
// For everything else, select default
`define _sel_hmc_default(_tile_i, _pri, _sec, _def)   (_tile_i == SEC_AC_TILE_INDEX) ? _sec : ((_tile_i == PRI_AC_TILE_INDEX) ? _pri : _def)

// Select primary or secondary HMC config, with lane dependence
// For non-ping-pong and primary HMC of ping-pong, select primary
// For secondary HMC of ping-pong, select primary or secondary based on lane affiliation
`define _sel_hmc_lane(_tile_i, _lane_i, _pri, _sec)   ( (PHY_PING_PONG_EN && (_tile_i < SEC_AC_TILE_INDEX || (_tile_i == SEC_AC_TILE_INDEX && _lane_i < 2))) ? _sec : _pri )

module altera_emif_arch_fm_io_tiles #(
   parameter DIAG_SYNTH_FOR_SIM                      = 0,
   parameter DIAG_CPA_OUT_1_EN                       = 0,
   parameter DIAG_FAST_SIM                           = 0,
   parameter DIAG_SEQ_RESET_AUTO_RELEASE             = "avl",
   parameter DIAG_DB_RESET_AUTO_RELEASE              = "avl_release",
   parameter IS_HPS                                  = 0,
   parameter SILICON_REV                             = "",
   parameter PROTOCOL_ENUM                           = "",
   parameter PHY_PING_PONG_EN                        = 0,
   parameter DQS_BUS_MODE_ENUM                       = "",
   parameter USER_CLK_RATIO                          = 1,
   parameter PHY_HMC_CLK_RATIO                       = 1,
   parameter C2P_P2C_CLK_RATIO                       = 1,
   parameter PLL_VCO_TO_MEM_CLK_FREQ_RATIO           = 1,
   parameter PLL_VCO_FREQ_MHZ_INT                    = 0,
   parameter PLL_MEM_CLK_FREQ_PS                     = 0,
   parameter MEM_BURST_LENGTH                        = 0,
   parameter MEM_DATA_MASK_EN                        = 1,
   parameter PINS_PER_LANE                           = 1,
   parameter LANES_PER_TILE                          = 1,
   parameter PINS_IN_RTL_TILES                       = 1,
   parameter LANES_IN_RTL_TILES                      = 1,
   parameter NUM_OF_RTL_TILES                        = 1,
   parameter AC_PIN_MAP_SCHEME                       = "",
   parameter PRI_AC_TILE_INDEX                       = -1,
   parameter PRI_RDATA_TILE_INDEX                    = -1,
   parameter PRI_RDATA_LANE_INDEX                    = -1,
   parameter PRI_WDATA_TILE_INDEX                    = -1,
   parameter PRI_WDATA_LANE_INDEX                    = -1,
   parameter SEC_AC_TILE_INDEX                       = -1,
   parameter SEC_RDATA_TILE_INDEX                    = -1,
   parameter SEC_RDATA_LANE_INDEX                    = -1,
   parameter SEC_WDATA_TILE_INDEX                    = -1,
   parameter SEC_WDATA_LANE_INDEX                    = -1,
   parameter PHY_MIMIC_HPS_EMIF                      = 0,
   parameter CPA_FB_MUX_1_SEL                        = "",

   parameter PRI_HMC_DBC_SHADOW_LANE_INDEX           = -1,
   parameter NUM_OF_HMC_PORTS                        = 1,
   parameter HMC_AVL_PROTOCOL_ENUM                   = "",
   parameter HMC_CTRL_DIMM_TYPE                      = "",
   parameter           PRI_HMC_CFG_PING_PONG_MODE              = "",
   parameter           PRI_HMC_CFG_CS_ADDR_WIDTH               = "",
   parameter           PRI_HMC_CFG_COL_ADDR_WIDTH              = "",
   parameter           PRI_HMC_CFG_ROW_ADDR_WIDTH              = "",
   parameter           PRI_HMC_CFG_BANK_ADDR_WIDTH             = "",
   parameter           PRI_HMC_CFG_BANK_GROUP_ADDR_WIDTH       = "",
   parameter           PRI_HMC_CFG_ADDR_ORDER                  = "",
   parameter           PRI_HMC_CFG_ARBITER_TYPE                = "",
   parameter           PRI_HMC_CFG_OPEN_PAGE_EN                = "",
   parameter           PRI_HMC_CFG_CTRL_ENABLE_RC              = "",
   parameter           PRI_HMC_CFG_DBC0_ENABLE_RC              = "",
   parameter           PRI_HMC_CFG_DBC1_ENABLE_RC              = "",
   parameter           PRI_HMC_CFG_DBC2_ENABLE_RC              = "",
   parameter           PRI_HMC_CFG_DBC3_ENABLE_RC              = "",
   parameter           PRI_HMC_CFG_CTRL_ENABLE_ECC             = "",
   parameter           PRI_HMC_CFG_DBC0_ENABLE_ECC             = "",
   parameter           PRI_HMC_CFG_DBC1_ENABLE_ECC             = "",
   parameter           PRI_HMC_CFG_DBC2_ENABLE_ECC             = "",
   parameter           PRI_HMC_CFG_DBC3_ENABLE_ECC             = "",
   parameter           PRI_HMC_CFG_REORDER_DATA                = "",
   parameter           PRI_HMC_CFG_REORDER_READ                = "",
   parameter           PRI_HMC_CFG_CTRL_REORDER_RDATA          = "",
   parameter           PRI_HMC_CFG_DBC0_REORDER_RDATA          = "",
   parameter           PRI_HMC_CFG_DBC1_REORDER_RDATA          = "",
   parameter           PRI_HMC_CFG_DBC2_REORDER_RDATA          = "",
   parameter           PRI_HMC_CFG_DBC3_REORDER_RDATA          = "",
   parameter [  1:  0] PRI_HMC_CFG_CTRL_SLOT_OFFSET            = 0,
   parameter [  1:  0] PRI_HMC_CFG_DBC0_SLOT_OFFSET            = 0,
   parameter [  1:  0] PRI_HMC_CFG_DBC1_SLOT_OFFSET            = 0,
   parameter [  1:  0] PRI_HMC_CFG_DBC2_SLOT_OFFSET            = 0,
   parameter [  1:  0] PRI_HMC_CFG_DBC3_SLOT_OFFSET            = 0,
   parameter           PRI_HMC_CFG_CTRL_SLOT_ROTATE_EN         = "",
   parameter           PRI_HMC_CFG_DBC0_SLOT_ROTATE_EN         = "",
   parameter           PRI_HMC_CFG_DBC1_SLOT_ROTATE_EN         = "",
   parameter           PRI_HMC_CFG_DBC2_SLOT_ROTATE_EN         = "",
   parameter           PRI_HMC_CFG_DBC3_SLOT_ROTATE_EN         = "",
   parameter [  3:  0] PRI_HMC_CFG_COL_CMD_SLOT                = 0,
   parameter [  3:  0] PRI_HMC_CFG_ROW_CMD_SLOT                = 0,
   parameter [ 31:  0] PRI_HMC_CFG_ROW_TO_COL_OFFSET           = 0,
   parameter [ 31:  0] PRI_HMC_CFG_ROW_TO_ROW_OFFSET           = 0,
   parameter [ 31:  0] PRI_HMC_CFG_COL_TO_COL_OFFSET           = 0,
   parameter [ 31:  0] PRI_HMC_CFG_COL_TO_DIFF_COL_OFFSET      = 0,
   parameter [ 31:  0] PRI_HMC_CFG_COL_TO_ROW_OFFSET           = 0,
   parameter [ 31:  0] PRI_HMC_CFG_SIDEBAND_OFFSET             = 0,
   parameter [ 15:  0] PRI_HMC_CFG_CS_TO_CHIP_MAPPING          = 0,
   parameter [ 31:  0] PRI_HMC_CFG_CTL_ODT_ENABLED             = 0,
   parameter [  5:  0] PRI_HMC_CFG_RD_ODT_ON                   = 0,
   parameter [  5:  0] PRI_HMC_CFG_RD_ODT_PERIOD               = 0,
   parameter [ 15:  0] PRI_HMC_CFG_READ_ODT_CHIP               = 0,
   parameter [  5:  0] PRI_HMC_CFG_WR_ODT_ON                   = 0,
   parameter [  5:  0] PRI_HMC_CFG_WR_ODT_PERIOD               = 0,
   parameter [ 15:  0] PRI_HMC_CFG_WRITE_ODT_CHIP              = 0,
   parameter           PRI_HMC_CFG_CMD_FIFO_RESERVE_EN         = "",
   parameter [  6:  0] PRI_HMC_CFG_RB_RESERVED_ENTRY           = 0,
   parameter [  6:  0] PRI_HMC_CFG_WB_RESERVED_ENTRY           = 0,
   parameter [  7:  0] PRI_HMC_CFG_STARVE_LIMIT                = 0,
   parameter [ 31:  0] PRI_HMC_CFG_PHY_DELAY_MISMATCH          = 0,
   parameter           PRI_HMC_CFG_DQSTRK_EN                   = "",
   parameter [  7:  0] PRI_HMC_CFG_DQSTRK_TO_VALID             = 0,
   parameter [  7:  0] PRI_HMC_CFG_DQSTRK_TO_VALID_LAST        = 0,
   parameter [ 31:  0] PRI_HMC_CFG_CTL_SHORT_DQSTRK_EN         = 0,
   parameter           PRI_HMC_CFG_PERIOD_DQSTRK_CTRL_EN       = "",
   parameter [ 15:  0] PRI_HMC_CFG_PERIOD_DQSTRK_INTERVAL      = 0,
   parameter           PRI_HMC_CFG_SHORT_DQSTRK_CTRL_EN        = "",
   parameter [ 31:  0] PRI_HMC_CFG_ENABLE_FAST_EXIT_PPD        = 0,
   parameter           PRI_HMC_CFG_USER_RFSH_EN                = "",
   parameter           PRI_HMC_CFG_GEAR_DOWN_EN                = "",
   parameter [ 31:  0] PRI_HMC_CFG_MEM_AUTO_PD_CYCLES          = 0,
   parameter [  5:  0] PRI_HMC_CFG_MEM_CLK_DISABLE_ENTRY_CYC   = 0,
   parameter [  7:  0] PRI_HMC_MEMCLKGATE_SETTING              = 0,
   parameter [  6:  0] PRI_HMC_CFG_TCL                         = 0,
   parameter [  7:  0] PRI_HMC_CFG_16_ACT_TO_ACT               = 0,
   parameter [  7:  0] PRI_HMC_CFG_4_ACT_TO_ACT                = 0,
   parameter [ 31:  0] PRI_HMC_MEM_IF_AL                       = 0,
   parameter [ 31:  0] PRI_HMC_MEM_IF_CS_PER_DIMM              = 0,
   parameter [ 31:  0] PRI_HMC_MEM_IF_RD_PREAMBLE              = 0,
   parameter [ 31:  0] PRI_HMC_MEM_IF_TCCD                     = 0,
   parameter [ 31:  0] PRI_HMC_MEM_IF_TCCD_S                   = 0,
   parameter [ 31:  0] PRI_HMC_MEM_IF_TCKESR                   = 0,
   parameter [ 31:  0] PRI_HMC_MEM_IF_TCKSRX                   = 0,
   parameter [ 31:  0] PRI_HMC_MEM_IF_TCL                      = 0,
   parameter [ 31:  0] PRI_HMC_MEM_IF_TCWL                     = 0,
   parameter [ 31:  0] PRI_HMC_MEM_IF_TDQSCKMAX                = 0,
   parameter [ 31:  0] PRI_HMC_MEM_IF_TFAW                     = 0,
   parameter [ 31:  0] PRI_HMC_MEM_IF_TMOD                     = 0,
   parameter [ 31:  0] PRI_HMC_MEM_IF_TPL                      = 0,
   parameter [ 31:  0] PRI_HMC_MEM_IF_TRAS                     = 0,
   parameter [ 31:  0] PRI_HMC_MEM_IF_TRC                      = 0,
   parameter [ 31:  0] PRI_HMC_MEM_IF_TRCD                     = 0,
   parameter [ 31:  0] PRI_HMC_MEM_IF_TREFI                    = 0,
   parameter [ 31:  0] PRI_HMC_MEM_IF_TRFC                     = 0,
   parameter [ 31:  0] PRI_HMC_MEM_IF_TRP                      = 0,
   parameter [ 31:  0] PRI_HMC_MEM_IF_TRRD                     = 0,
   parameter [ 31:  0] PRI_HMC_MEM_IF_TRRD_S                   = 0,
   parameter [ 31:  0] PRI_HMC_MEM_IF_TRTP                     = 0,
   parameter [ 31:  0] PRI_HMC_MEM_IF_TWR                      = 0,
   parameter [ 31:  0] PRI_HMC_MEM_IF_TWR_CRC_DM               = 0,
   parameter [ 31:  0] PRI_HMC_MEM_IF_TWTR                     = 0,
   parameter [ 31:  0] PRI_HMC_MEM_IF_TWTR_L_CRC_DM            = 0,
   parameter [ 31:  0] PRI_HMC_MEM_IF_TWTR_S                   = 0,
   parameter [ 31:  0] PRI_HMC_MEM_IF_TWTR_S_CRC_DM            = 0,
   parameter [ 31:  0] PRI_HMC_MEM_IF_TXP                      = 0,
   parameter [ 31:  0] PRI_HMC_MEM_IF_TXPDLL                   = 0,
   parameter [ 31:  0] PRI_HMC_MEM_IF_TXSR                     = 0,
   parameter [ 31:  0] PRI_HMC_MEM_IF_TZQCS                    = 0,
   parameter [ 31:  0] PRI_HMC_MEM_IF_TZQOPER                  = 0,
   parameter [ 31:  0] PRI_HMC_MEM_IF_WR_CRC                   = 0,
   parameter [ 31:  0] PRI_HMC_MEM_IF_WR_PREAMBLE              = 0,
   parameter [  5:  0] PRI_HMC_CFG_ACT_TO_ACT                  = 0,
   parameter [  5:  0] PRI_HMC_CFG_ACT_TO_ACT_DIFF_BANK        = 0,
   parameter [  5:  0] PRI_HMC_CFG_ACT_TO_ACT_DIFF_BG          = 0,
   parameter [  5:  0] PRI_HMC_CFG_ACT_TO_PCH                  = 0,
   parameter [  5:  0] PRI_HMC_CFG_ACT_TO_RDWR                 = 0,
   parameter [ 12:  0] PRI_HMC_CFG_ARF_PERIOD                  = 0,
   parameter [  9:  0] PRI_HMC_CFG_ARF_TO_VALID                = 0,
   parameter [  7:  0] PRI_HMC_CFG_MMR_CMD_TO_VALID            = 0,
   parameter [  4:  0] PRI_HMC_CFG_MPR_TO_VALID                = 0,
   parameter           PRI_HMC_CFG_MPS_DQSTRK_DISABLE          = "",
   parameter [  3:  0] PRI_HMC_CFG_MPS_EXIT_CKE_TO_CS          = 0,
   parameter [  3:  0] PRI_HMC_CFG_MPS_EXIT_CS_TO_CKE          = 0,
   parameter [  9:  0] PRI_HMC_CFG_MPS_TO_VALID                = 0,
   parameter           PRI_HMC_CFG_MPS_ZQCAL_DISABLE           = "",
   parameter [  3:  0] PRI_HMC_CFG_MRR_TO_VALID                = 0,
   parameter [  3:  0] PRI_HMC_CFG_MRS_TO_VALID                = 0,
   parameter [  5:  0] PRI_HMC_CFG_PCH_ALL_TO_VALID            = 0,
   parameter [  5:  0] PRI_HMC_CFG_PCH_TO_VALID                = 0,
   parameter [ 15:  0] PRI_HMC_CFG_PDN_PERIOD                  = 0,
   parameter [  5:  0] PRI_HMC_CFG_PDN_TO_VALID                = 0,
   parameter [  5:  0] PRI_HMC_CFG_POWER_SAVING_EXIT_CYC       = 0,
   parameter [  5:  0] PRI_HMC_CFG_RD_AP_TO_VALID              = 0,
   parameter [  5:  0] PRI_HMC_CFG_RD_TO_PCH                   = 0,
   parameter [  5:  0] PRI_HMC_CFG_RD_TO_RD                    = 0,
   parameter [  5:  0] PRI_HMC_CFG_RD_TO_RD_DIFF_BG            = 0,
   parameter [  5:  0] PRI_HMC_CFG_RD_TO_RD_DIFF_CHIP          = 0,
   parameter [  5:  0] PRI_HMC_CFG_RD_TO_WR                    = 0,
   parameter [  5:  0] PRI_HMC_CFG_RD_TO_WR_DIFF_BG            = 0,
   parameter [  5:  0] PRI_HMC_CFG_RD_TO_WR_DIFF_CHIP          = 0,
   parameter [  6:  0] PRI_HMC_CFG_RFSH_WARN_THRESHOLD         = 0,
   parameter [  2:  0] PRI_HMC_CFG_RLD3_MULTIBANK_REF_DELAY    = 0,
   parameter [ 15:  0] PRI_HMC_CFG_RLD3_REFRESH_SEQ0           = 0,
   parameter [ 15:  0] PRI_HMC_CFG_RLD3_REFRESH_SEQ1           = 0,
   parameter [ 15:  0] PRI_HMC_CFG_RLD3_REFRESH_SEQ2           = 0,
   parameter [ 15:  0] PRI_HMC_CFG_RLD3_REFRESH_SEQ3           = 0,
   parameter           PRI_HMC_CFG_SB_CG_DISABLE               = "",
   parameter [ 19:  0] PRI_HMC_CFG_SB_DDR4_MR3                 = 0,
   parameter [ 19:  0] PRI_HMC_CFG_SB_DDR4_MR4                 = 0,
   parameter [ 19:  0] PRI_HMC_CFG_SB_DDR4_MR5                 = 0,
   parameter           PRI_HMC_CFG_DDR4_MPS_ADDRMIRROR         = "",
   parameter           PRI_HMC_CFG_SRF_AUTOEXIT_EN             = "",
   parameter [  1:  0] PRI_HMC_CFG_SRF_ENTRY_EXIT_BLOCK        = 0,
   parameter [  9:  0] PRI_HMC_CFG_SRF_TO_VALID                = 0,
   parameter [  9:  0] PRI_HMC_CFG_SRF_TO_ZQ_CAL               = 0,
   parameter           PRI_HMC_CFG_SRF_ZQCAL_DISABLE           = "",
   parameter [ 31:  0] PRI_HMC_TEMP_4_ACT_TO_ACT               = 0,
   parameter [ 31:  0] PRI_HMC_TEMP_RD_TO_RD_DIFF_BG           = 0,
   parameter [ 31:  0] PRI_HMC_TEMP_WR_TO_RD                   = 0,
   parameter [ 31:  0] PRI_HMC_TEMP_WR_TO_RD_DIFF_BG           = 0,
   parameter [ 31:  0] PRI_HMC_TEMP_WR_TO_RD_DIFF_CHIP         = 0,
   parameter [ 31:  0] PRI_HMC_TEMP_WR_TO_WR_DIFF_BG           = 0,
   parameter [  5:  0] PRI_HMC_CFG_WR_AP_TO_VALID              = 0,
   parameter [  5:  0] PRI_HMC_CFG_WR_TO_PCH                   = 0,
   parameter [  5:  0] PRI_HMC_CFG_WR_TO_RD                    = 0,
   parameter [  5:  0] PRI_HMC_CFG_WR_TO_RD_DIFF_BG            = 0,
   parameter [  5:  0] PRI_HMC_CFG_WR_TO_RD_DIFF_CHIP          = 0,
   parameter [  5:  0] PRI_HMC_CFG_WR_TO_WR                    = 0,
   parameter [  5:  0] PRI_HMC_CFG_WR_TO_WR_DIFF_BG            = 0,
   parameter [  5:  0] PRI_HMC_CFG_WR_TO_WR_DIFF_CHIP          = 0,
   parameter [  8:  0] PRI_HMC_CFG_ZQCL_TO_VALID               = 0,
   parameter [  6:  0] PRI_HMC_CFG_ZQCS_TO_VALID               = 0,
   parameter           PRI_HMC_CFG_MAJOR_MODE_EN               = "",
   parameter [  1:  0] PRI_HMC_CFG_REFRESH_TYPE                = 0,
   parameter           PRI_HMC_CFG_POST_REFRESH_EN             = "",
   parameter [  4:  0] PRI_HMC_CFG_POST_REFRESH_LOWER_LIMIT    = 0,
   parameter [  4:  0] PRI_HMC_CFG_POST_REFRESH_UPPER_LIMIT    = 0,
   parameter           PRI_HMC_CFG_PRE_REFRESH_EN              = "",
   parameter [  3:  0] PRI_HMC_CFG_PRE_REFRESH_UPPER_LIMIT     = 0,
   parameter [  8:  0] PRI_HMC_CHIP_ID                         = 0,
   parameter [  1:  0] PRI_HMC_CID_ADDR_WIDTH                  = 0,
   parameter           PRI_HMC_3DS_EN                          = "",
   parameter [  3:  0] PRI_HMC_3DS_LR_NUM0                     = 0,
   parameter [  3:  0] PRI_HMC_3DS_LR_NUM1                     = 0,
   parameter [  3:  0] PRI_HMC_3DS_LR_NUM2                     = 0,
   parameter [  3:  0] PRI_HMC_3DS_LR_NUM3                     = 0,
   parameter           PRI_HMC_3DS_PR_STAG_ENABLE              = "",
   parameter [  6:  0] PRI_HMC_3DS_REF2REF_DLR                 = 0,
   parameter           PRI_HMC_3DSREF_ACK_ON_DONE              = "",
   parameter           SEC_HMC_CFG_PING_PONG_MODE              = "",
   parameter           SEC_HMC_CFG_CS_ADDR_WIDTH               = "",
   parameter           SEC_HMC_CFG_COL_ADDR_WIDTH              = "",
   parameter           SEC_HMC_CFG_ROW_ADDR_WIDTH              = "",
   parameter           SEC_HMC_CFG_BANK_ADDR_WIDTH             = "",
   parameter           SEC_HMC_CFG_BANK_GROUP_ADDR_WIDTH       = "",
   parameter           SEC_HMC_CFG_ADDR_ORDER                  = "",
   parameter           SEC_HMC_CFG_ARBITER_TYPE                = "",
   parameter           SEC_HMC_CFG_OPEN_PAGE_EN                = "",
   parameter           SEC_HMC_CFG_CTRL_ENABLE_RC              = "",
   parameter           SEC_HMC_CFG_DBC0_ENABLE_RC              = "",
   parameter           SEC_HMC_CFG_DBC1_ENABLE_RC              = "",
   parameter           SEC_HMC_CFG_DBC2_ENABLE_RC              = "",
   parameter           SEC_HMC_CFG_DBC3_ENABLE_RC              = "",
   parameter           SEC_HMC_CFG_CTRL_ENABLE_ECC             = "",
   parameter           SEC_HMC_CFG_DBC0_ENABLE_ECC             = "",
   parameter           SEC_HMC_CFG_DBC1_ENABLE_ECC             = "",
   parameter           SEC_HMC_CFG_DBC2_ENABLE_ECC             = "",
   parameter           SEC_HMC_CFG_DBC3_ENABLE_ECC             = "",
   parameter           SEC_HMC_CFG_REORDER_DATA                = "",
   parameter           SEC_HMC_CFG_REORDER_READ                = "",
   parameter           SEC_HMC_CFG_CTRL_REORDER_RDATA          = "",
   parameter           SEC_HMC_CFG_DBC0_REORDER_RDATA          = "",
   parameter           SEC_HMC_CFG_DBC1_REORDER_RDATA          = "",
   parameter           SEC_HMC_CFG_DBC2_REORDER_RDATA          = "",
   parameter           SEC_HMC_CFG_DBC3_REORDER_RDATA          = "",
   parameter [  1:  0] SEC_HMC_CFG_CTRL_SLOT_OFFSET            = 0,
   parameter [  1:  0] SEC_HMC_CFG_DBC0_SLOT_OFFSET            = 0,
   parameter [  1:  0] SEC_HMC_CFG_DBC1_SLOT_OFFSET            = 0,
   parameter [  1:  0] SEC_HMC_CFG_DBC2_SLOT_OFFSET            = 0,
   parameter [  1:  0] SEC_HMC_CFG_DBC3_SLOT_OFFSET            = 0,
   parameter           SEC_HMC_CFG_CTRL_SLOT_ROTATE_EN         = "",
   parameter           SEC_HMC_CFG_DBC0_SLOT_ROTATE_EN         = "",
   parameter           SEC_HMC_CFG_DBC1_SLOT_ROTATE_EN         = "",
   parameter           SEC_HMC_CFG_DBC2_SLOT_ROTATE_EN         = "",
   parameter           SEC_HMC_CFG_DBC3_SLOT_ROTATE_EN         = "",
   parameter [  3:  0] SEC_HMC_CFG_COL_CMD_SLOT                = 0,
   parameter [  3:  0] SEC_HMC_CFG_ROW_CMD_SLOT                = 0,
   parameter [ 31:  0] SEC_HMC_CFG_ROW_TO_COL_OFFSET           = 0,
   parameter [ 31:  0] SEC_HMC_CFG_ROW_TO_ROW_OFFSET           = 0,
   parameter [ 31:  0] SEC_HMC_CFG_COL_TO_COL_OFFSET           = 0,
   parameter [ 31:  0] SEC_HMC_CFG_COL_TO_DIFF_COL_OFFSET      = 0,
   parameter [ 31:  0] SEC_HMC_CFG_COL_TO_ROW_OFFSET           = 0,
   parameter [ 31:  0] SEC_HMC_CFG_SIDEBAND_OFFSET             = 0,
   parameter [ 15:  0] SEC_HMC_CFG_CS_TO_CHIP_MAPPING          = 0,
   parameter [ 31:  0] SEC_HMC_CFG_CTL_ODT_ENABLED             = 0,
   parameter [  5:  0] SEC_HMC_CFG_RD_ODT_ON                   = 0,
   parameter [  5:  0] SEC_HMC_CFG_RD_ODT_PERIOD               = 0,
   parameter [ 15:  0] SEC_HMC_CFG_READ_ODT_CHIP               = 0,
   parameter [  5:  0] SEC_HMC_CFG_WR_ODT_ON                   = 0,
   parameter [  5:  0] SEC_HMC_CFG_WR_ODT_PERIOD               = 0,
   parameter [ 15:  0] SEC_HMC_CFG_WRITE_ODT_CHIP              = 0,
   parameter           SEC_HMC_CFG_CMD_FIFO_RESERVE_EN         = "",
   parameter [  6:  0] SEC_HMC_CFG_RB_RESERVED_ENTRY           = 0,
   parameter [  6:  0] SEC_HMC_CFG_WB_RESERVED_ENTRY           = 0,
   parameter [  7:  0] SEC_HMC_CFG_STARVE_LIMIT                = 0,
   parameter [ 31:  0] SEC_HMC_CFG_PHY_DELAY_MISMATCH          = 0,
   parameter           SEC_HMC_CFG_DQSTRK_EN                   = "",
   parameter [  7:  0] SEC_HMC_CFG_DQSTRK_TO_VALID             = 0,
   parameter [  7:  0] SEC_HMC_CFG_DQSTRK_TO_VALID_LAST        = 0,
   parameter [ 31:  0] SEC_HMC_CFG_CTL_SHORT_DQSTRK_EN         = 0,
   parameter           SEC_HMC_CFG_PERIOD_DQSTRK_CTRL_EN       = "",
   parameter [ 15:  0] SEC_HMC_CFG_PERIOD_DQSTRK_INTERVAL      = 0,
   parameter           SEC_HMC_CFG_SHORT_DQSTRK_CTRL_EN        = "",
   parameter [ 31:  0] SEC_HMC_CFG_ENABLE_FAST_EXIT_PPD        = 0,
   parameter           SEC_HMC_CFG_USER_RFSH_EN                = "",
   parameter           SEC_HMC_CFG_GEAR_DOWN_EN                = "",
   parameter [ 31:  0] SEC_HMC_CFG_MEM_AUTO_PD_CYCLES          = 0,
   parameter [  5:  0] SEC_HMC_CFG_MEM_CLK_DISABLE_ENTRY_CYC   = 0,
   parameter [  7:  0] SEC_HMC_MEMCLKGATE_SETTING              = 0,
   parameter [  6:  0] SEC_HMC_CFG_TCL                         = 0,
   parameter [  7:  0] SEC_HMC_CFG_16_ACT_TO_ACT               = 0,
   parameter [  7:  0] SEC_HMC_CFG_4_ACT_TO_ACT                = 0,
   parameter [ 31:  0] SEC_HMC_MEM_IF_AL                       = 0,
   parameter [ 31:  0] SEC_HMC_MEM_IF_CS_PER_DIMM              = 0,
   parameter [ 31:  0] SEC_HMC_MEM_IF_RD_PREAMBLE              = 0,
   parameter [ 31:  0] SEC_HMC_MEM_IF_TCCD                     = 0,
   parameter [ 31:  0] SEC_HMC_MEM_IF_TCCD_S                   = 0,
   parameter [ 31:  0] SEC_HMC_MEM_IF_TCKESR                   = 0,
   parameter [ 31:  0] SEC_HMC_MEM_IF_TCKSRX                   = 0,
   parameter [ 31:  0] SEC_HMC_MEM_IF_TCL                      = 0,
   parameter [ 31:  0] SEC_HMC_MEM_IF_TCWL                     = 0,
   parameter [ 31:  0] SEC_HMC_MEM_IF_TDQSCKMAX                = 0,
   parameter [ 31:  0] SEC_HMC_MEM_IF_TFAW                     = 0,
   parameter [ 31:  0] SEC_HMC_MEM_IF_TMOD                     = 0,
   parameter [ 31:  0] SEC_HMC_MEM_IF_TPL                      = 0,
   parameter [ 31:  0] SEC_HMC_MEM_IF_TRAS                     = 0,
   parameter [ 31:  0] SEC_HMC_MEM_IF_TRC                      = 0,
   parameter [ 31:  0] SEC_HMC_MEM_IF_TRCD                     = 0,
   parameter [ 31:  0] SEC_HMC_MEM_IF_TREFI                    = 0,
   parameter [ 31:  0] SEC_HMC_MEM_IF_TRFC                     = 0,
   parameter [ 31:  0] SEC_HMC_MEM_IF_TRP                      = 0,
   parameter [ 31:  0] SEC_HMC_MEM_IF_TRRD                     = 0,
   parameter [ 31:  0] SEC_HMC_MEM_IF_TRRD_S                   = 0,
   parameter [ 31:  0] SEC_HMC_MEM_IF_TRTP                     = 0,
   parameter [ 31:  0] SEC_HMC_MEM_IF_TWR                      = 0,
   parameter [ 31:  0] SEC_HMC_MEM_IF_TWR_CRC_DM               = 0,
   parameter [ 31:  0] SEC_HMC_MEM_IF_TWTR                     = 0,
   parameter [ 31:  0] SEC_HMC_MEM_IF_TWTR_L_CRC_DM            = 0,
   parameter [ 31:  0] SEC_HMC_MEM_IF_TWTR_S                   = 0,
   parameter [ 31:  0] SEC_HMC_MEM_IF_TWTR_S_CRC_DM            = 0,
   parameter [ 31:  0] SEC_HMC_MEM_IF_TXP                      = 0,
   parameter [ 31:  0] SEC_HMC_MEM_IF_TXPDLL                   = 0,
   parameter [ 31:  0] SEC_HMC_MEM_IF_TXSR                     = 0,
   parameter [ 31:  0] SEC_HMC_MEM_IF_TZQCS                    = 0,
   parameter [ 31:  0] SEC_HMC_MEM_IF_TZQOPER                  = 0,
   parameter [ 31:  0] SEC_HMC_MEM_IF_WR_CRC                   = 0,
   parameter [ 31:  0] SEC_HMC_MEM_IF_WR_PREAMBLE              = 0,
   parameter [  5:  0] SEC_HMC_CFG_ACT_TO_ACT                  = 0,
   parameter [  5:  0] SEC_HMC_CFG_ACT_TO_ACT_DIFF_BANK        = 0,
   parameter [  5:  0] SEC_HMC_CFG_ACT_TO_ACT_DIFF_BG          = 0,
   parameter [  5:  0] SEC_HMC_CFG_ACT_TO_PCH                  = 0,
   parameter [  5:  0] SEC_HMC_CFG_ACT_TO_RDWR                 = 0,
   parameter [ 12:  0] SEC_HMC_CFG_ARF_PERIOD                  = 0,
   parameter [  9:  0] SEC_HMC_CFG_ARF_TO_VALID                = 0,
   parameter [  7:  0] SEC_HMC_CFG_MMR_CMD_TO_VALID            = 0,
   parameter [  4:  0] SEC_HMC_CFG_MPR_TO_VALID                = 0,
   parameter           SEC_HMC_CFG_MPS_DQSTRK_DISABLE          = "",
   parameter [  3:  0] SEC_HMC_CFG_MPS_EXIT_CKE_TO_CS          = 0,
   parameter [  3:  0] SEC_HMC_CFG_MPS_EXIT_CS_TO_CKE          = 0,
   parameter [  9:  0] SEC_HMC_CFG_MPS_TO_VALID                = 0,
   parameter           SEC_HMC_CFG_MPS_ZQCAL_DISABLE           = "",
   parameter [  3:  0] SEC_HMC_CFG_MRR_TO_VALID                = 0,
   parameter [  3:  0] SEC_HMC_CFG_MRS_TO_VALID                = 0,
   parameter [  5:  0] SEC_HMC_CFG_PCH_ALL_TO_VALID            = 0,
   parameter [  5:  0] SEC_HMC_CFG_PCH_TO_VALID                = 0,
   parameter [ 15:  0] SEC_HMC_CFG_PDN_PERIOD                  = 0,
   parameter [  5:  0] SEC_HMC_CFG_PDN_TO_VALID                = 0,
   parameter [  5:  0] SEC_HMC_CFG_POWER_SAVING_EXIT_CYC       = 0,
   parameter [  5:  0] SEC_HMC_CFG_RD_AP_TO_VALID              = 0,
   parameter [  5:  0] SEC_HMC_CFG_RD_TO_PCH                   = 0,
   parameter [  5:  0] SEC_HMC_CFG_RD_TO_RD                    = 0,
   parameter [  5:  0] SEC_HMC_CFG_RD_TO_RD_DIFF_BG            = 0,
   parameter [  5:  0] SEC_HMC_CFG_RD_TO_RD_DIFF_CHIP          = 0,
   parameter [  5:  0] SEC_HMC_CFG_RD_TO_WR                    = 0,
   parameter [  5:  0] SEC_HMC_CFG_RD_TO_WR_DIFF_BG            = 0,
   parameter [  5:  0] SEC_HMC_CFG_RD_TO_WR_DIFF_CHIP          = 0,
   parameter [  6:  0] SEC_HMC_CFG_RFSH_WARN_THRESHOLD         = 0,
   parameter [  2:  0] SEC_HMC_CFG_RLD3_MULTIBANK_REF_DELAY    = 0,
   parameter [ 15:  0] SEC_HMC_CFG_RLD3_REFRESH_SEQ0           = 0,
   parameter [ 15:  0] SEC_HMC_CFG_RLD3_REFRESH_SEQ1           = 0,
   parameter [ 15:  0] SEC_HMC_CFG_RLD3_REFRESH_SEQ2           = 0,
   parameter [ 15:  0] SEC_HMC_CFG_RLD3_REFRESH_SEQ3           = 0,
   parameter           SEC_HMC_CFG_SB_CG_DISABLE               = "",
   parameter [ 19:  0] SEC_HMC_CFG_SB_DDR4_MR3                 = 0,
   parameter [ 19:  0] SEC_HMC_CFG_SB_DDR4_MR4                 = 0,
   parameter [ 19:  0] SEC_HMC_CFG_SB_DDR4_MR5                 = 0,
   parameter           SEC_HMC_CFG_DDR4_MPS_ADDRMIRROR         = "",
   parameter           SEC_HMC_CFG_SRF_AUTOEXIT_EN             = "",
   parameter [  1:  0] SEC_HMC_CFG_SRF_ENTRY_EXIT_BLOCK        = 0,
   parameter [  9:  0] SEC_HMC_CFG_SRF_TO_VALID                = 0,
   parameter [  9:  0] SEC_HMC_CFG_SRF_TO_ZQ_CAL               = 0,
   parameter           SEC_HMC_CFG_SRF_ZQCAL_DISABLE           = "",
   parameter [ 31:  0] SEC_HMC_TEMP_4_ACT_TO_ACT               = 0,
   parameter [ 31:  0] SEC_HMC_TEMP_RD_TO_RD_DIFF_BG           = 0,
   parameter [ 31:  0] SEC_HMC_TEMP_WR_TO_RD                   = 0,
   parameter [ 31:  0] SEC_HMC_TEMP_WR_TO_RD_DIFF_BG           = 0,
   parameter [ 31:  0] SEC_HMC_TEMP_WR_TO_RD_DIFF_CHIP         = 0,
   parameter [ 31:  0] SEC_HMC_TEMP_WR_TO_WR_DIFF_BG           = 0,
   parameter [  5:  0] SEC_HMC_CFG_WR_AP_TO_VALID              = 0,
   parameter [  5:  0] SEC_HMC_CFG_WR_TO_PCH                   = 0,
   parameter [  5:  0] SEC_HMC_CFG_WR_TO_RD                    = 0,
   parameter [  5:  0] SEC_HMC_CFG_WR_TO_RD_DIFF_BG            = 0,
   parameter [  5:  0] SEC_HMC_CFG_WR_TO_RD_DIFF_CHIP          = 0,
   parameter [  5:  0] SEC_HMC_CFG_WR_TO_WR                    = 0,
   parameter [  5:  0] SEC_HMC_CFG_WR_TO_WR_DIFF_BG            = 0,
   parameter [  5:  0] SEC_HMC_CFG_WR_TO_WR_DIFF_CHIP          = 0,
   parameter [  8:  0] SEC_HMC_CFG_ZQCL_TO_VALID               = 0,
   parameter [  6:  0] SEC_HMC_CFG_ZQCS_TO_VALID               = 0,
   parameter           SEC_HMC_CFG_MAJOR_MODE_EN               = "",
   parameter [  1:  0] SEC_HMC_CFG_REFRESH_TYPE                = 0,
   parameter           SEC_HMC_CFG_POST_REFRESH_EN             = "",
   parameter [  4:  0] SEC_HMC_CFG_POST_REFRESH_LOWER_LIMIT    = 0,
   parameter [  4:  0] SEC_HMC_CFG_POST_REFRESH_UPPER_LIMIT    = 0,
   parameter           SEC_HMC_CFG_PRE_REFRESH_EN              = "",
   parameter [  3:  0] SEC_HMC_CFG_PRE_REFRESH_UPPER_LIMIT     = 0,
   parameter [  8:  0] SEC_HMC_CHIP_ID                         = 0,
   parameter [  1:  0] SEC_HMC_CID_ADDR_WIDTH                  = 0,
   parameter           SEC_HMC_3DS_EN                          = "",
   parameter [  3:  0] SEC_HMC_3DS_LR_NUM0                     = 0,
   parameter [  3:  0] SEC_HMC_3DS_LR_NUM1                     = 0,
   parameter [  3:  0] SEC_HMC_3DS_LR_NUM2                     = 0,
   parameter [  3:  0] SEC_HMC_3DS_LR_NUM3                     = 0,
   parameter           SEC_HMC_3DS_PR_STAG_ENABLE              = "",
   parameter [  6:  0] SEC_HMC_3DS_REF2REF_DLR                 = 0,
   parameter           SEC_HMC_3DSREF_ACK_ON_DONE              = "",

   parameter PORT_CALBUS_ADDRESS_WIDTH              = 1,
   parameter PORT_CALBUS_RDATA_WIDTH                = 1,
   parameter PORT_CALBUS_WDATA_WIDTH                = 1,
   parameter PORT_CALBUS_SEQ_PARAM_TBL_WIDTH        = 1,

   parameter SEQ_PT_CONTENT                          = "",
   parameter LANES_USAGE                             = 0,
   parameter PINS_USAGE                              = 0,
   parameter LANE_PIN_USAGE                          = 0,
   parameter PINS_RATE                               = 0,
   parameter DB_PINS_PROC_MODE                       = 0,
   parameter PINS_DATA_IN_MODE                       = 0,
   parameter PINS_OCT_MODE                           = 0,
   parameter PINS_DCC_SPLIT                          = 0,
   parameter CENTER_TIDS                             = 0,
   parameter HMC_TIDS                                = 0,
   parameter LANE_TIDS                               = 0,
   parameter DBC_EXTRA_PIPE_STAGE_EN                 = "",
   parameter DBC_PIPE_LATS                           = 0,
   parameter DB_PTR_PIPELINE_DEPTHS                  = 0,
   parameter DB_SEQ_RD_EN_FULL_PIPELINES             = 0,
   parameter PREAMBLE_MODE                           = "",
   parameter DBI_WR_ENABLE                           = "",
   parameter DBI_RD_ENABLE                           = "",
   parameter SWAP_DQS_A_B                            = "",
   parameter DQS_PACK_MODE                           = "",
   parameter OCT_SIZE                                = "",
   parameter DQSA_LGC_MODE                           = "",
   parameter DQSB_LGC_MODE                           = "",
   parameter [6:0] DBC_WB_RESERVED_ENTRY             = 4,
   parameter DLL_MODE                                = "",
   parameter [10:0] DLL_CODEWORD                      = 0,
   parameter PORT_MEM_DQ_WIDTH                       = 1,
   parameter PORT_MEM_DQS_WIDTH                      = 1,
   parameter PORT_DFT_ND_PA_DPRIO_REG_ADDR_WIDTH     = 1,
   parameter PORT_DFT_ND_PA_DPRIO_WRITEDATA_WIDTH    = 1,
   parameter PORT_DFT_ND_PA_DPRIO_READDATA_WIDTH     = 1,
   
   parameter DIAG_USE_ABSTRACT_PHY                   = 0
) (
   // Reset related
   input logic                                                                                   core2seq_reset_req,           // For abstract phy support
   
   // Signals for various signals from PLL
   input  logic                                                                                  pll_locked,                   // Indicates PLL lock status
   input  logic                                                                                  pll_dll_clk,                  // PLL -> DLL output clock
   input  logic [7:0]                                                                            phy_clk_phs,                  // FR PHY clock signals (8 phases, 45-deg apart)
   input  logic [1:0]                                                                            phy_clk,                      // {phy_clk[1], phy_clk[0]}
   input  logic                                                                                  phy_fb_clk_to_tile,           // PHY feedback clock (to tile)
   output logic                                                                                  phy_fb_clk_to_pll_nonabphy,   // PHY feedback clock (to PLL)

   output logic [1:0]                                                                            global_phy_clk,               // {phy_clk[1], phy_clk[0]}

   // Core clock signals from/to the Clock Phase Alignment (CPA) block
   output logic [1:0]                                                                            core_clks_from_cpa_pri_nonabphy,   // Core clock signals from the CPA of primary interface
   output logic [1:0]                                                                            core_clks_locked_cpa_pri_nonabphy, // Core clock locked signals from the CPA of primary interface
   input  logic [1:0]                                                                            core_clks_fb_to_cpa_pri,           // Core clock feedback signals to the CPA of primary interface
   output logic [1:0]                                                                            core_clks_from_cpa_sec_nonabphy,   // Core clock signals from the CPA of secondary interface (ping-pong only)
   output logic [1:0]                                                                            core_clks_locked_cpa_sec_nonabphy, // Core clock locked signals from the CPA of secondary interface (ping-pong only)
   input  logic [1:0]                                                                            core_clks_fb_to_cpa_sec,           // Core clock feedback signals to the CPA of secondary interface (ping-pong only)

   // Avalon interfaces between core and HMC
   input  logic [62:0]                                                                           core2ctl_avl_0,
   input  logic [62:0]                                                                           core2ctl_avl_1,
   input  logic                                                                                  core2ctl_avl_rd_data_ready_0,
   input  logic                                                                                  core2ctl_avl_rd_data_ready_1,
   output logic                                                                                  ctl2core_avl_cmd_ready_0_nonabphy,
   output logic                                                                                  ctl2core_avl_cmd_ready_1_nonabphy,
   output logic [12:0]                                                                           ctl2core_avl_rdata_id_0_nonabphy,
   output logic [12:0]                                                                           ctl2core_avl_rdata_id_1_nonabphy,

   // ECC signals between core and lanes
   input  logic [NUM_OF_RTL_TILES-1:0][LANES_PER_TILE-1:0]                                       core2l_wr_data_vld_ast,
   input  logic [NUM_OF_RTL_TILES-1:0][LANES_PER_TILE-1:0]                                       core2l_rd_data_rdy_ast,
   input  logic [NUM_OF_RTL_TILES-1:0][LANES_PER_TILE-1:0][12:0]                                 core2l_wr_ecc_info,

   output logic                                                                                  l2core_rd_type_nonabphy,
   output logic                                                                                  l2core_rd_data_vld_avl_nonabphy,
   output logic                                                                                  l2core_wr_data_rdy_ast_nonabphy,
   output logic [11:0]                                                                           l2core_wb_pointer_for_ecc_nonabphy,

   // Signals between core and data lanes
   input  logic [NUM_OF_RTL_TILES-1:0][LANES_PER_TILE-1:0][PINS_PER_LANE * 8 - 1:0]              core2l_data,
   output logic [NUM_OF_RTL_TILES-1:0][LANES_PER_TILE-1:0][PINS_PER_LANE * 8 - 1:0]              l2core_data_nonabphy,

   input  logic [NUM_OF_RTL_TILES-1:0][LANES_PER_TILE-1:0][47:0]                                 core2l_oe,
   input  logic [NUM_OF_RTL_TILES-1:0][LANES_PER_TILE-1:0][3:0]                                  core2l_rdata_en_full,
   input  logic [NUM_OF_RTL_TILES-1:0][LANES_PER_TILE-1:0][7:0]                                  core2l_mrnk_read,
   input  logic [NUM_OF_RTL_TILES-1:0][LANES_PER_TILE-1:0][7:0]                                  core2l_mrnk_write,

   output logic [3:0]                                                                            l2core_rdata_valid_nonabphy_pri,
   output logic [3:0]                                                                            l2core_rdata_valid_nonabphy_sec,
   output logic [5:0]                                                                            l2core_afi_rlat_nonabphy,
   output logic [5:0]                                                                            l2core_afi_wlat_nonabphy,

   // AFI signals between tile and core
   input  logic [17:0]                                                                           c2t_afi,
   output logic [26:0]                                                                           t2c_afi_nonabphy,

   // Side-band signals between core and HMC
   input  logic [41:0]                                                                           core2ctl_sideband_0,
   output logic [13:0]                                                                           ctl2core_sideband_0_nonabphy,
   input  logic [41:0]                                                                           core2ctl_sideband_1,
   output logic [13:0]                                                                           ctl2core_sideband_1_nonabphy,

   // MMR signals between core and HMC
   output logic [33:0]                                                                           ctl2core_mmr_0_nonabphy,
   input  logic [50:0]                                                                           core2ctl_mmr_0,
   output logic [33:0]                                                                           ctl2core_mmr_1_nonabphy,
   input  logic [50:0]                                                                           core2ctl_mmr_1,

   // Signals between I/O buffers and lanes/tiles
   output logic [PINS_IN_RTL_TILES-1:0]                                                          l2b_data_nonabphy,         // lane-to-buffer data
   output logic [PINS_IN_RTL_TILES-1:0]                                                          l2b_oe_nonabphy,           // lane-to-buffer output-enable
   output logic [PINS_IN_RTL_TILES-1:0]                                                          l2b_dtc_nonabphy,          // lane-to-buffer dynamic-termination-control
   input  logic [PINS_IN_RTL_TILES-1:0]                                                          b2l_data,                  // buffer-to-lane data
   input  logic [LANES_IN_RTL_TILES-1:0]                                                         b2t_dqs,                   // buffer-to-tile DQS
   input  logic [LANES_IN_RTL_TILES-1:0]                                                         b2t_dqsb,                  // buffer-to-tile DQSb

   // Avalon-MM bus for the calibration commands between IOSSM and tiles
   input  logic                                                                                  cal_bus_clk,
   input  logic                                                                                  cal_bus_avl_read,
   input  logic                                                                                  cal_bus_avl_write,
   input  logic [PORT_CALBUS_ADDRESS_WIDTH-1:0]                                                  cal_bus_avl_address,
   output logic [PORT_CALBUS_RDATA_WIDTH-1:0]                                                    cal_bus_avl_read_data,
   input  logic [PORT_CALBUS_WDATA_WIDTH-1:0]                                                    cal_bus_avl_write_data,
   output logic [PORT_CALBUS_SEQ_PARAM_TBL_WIDTH-1:0]                                            cal_bus_seq_param_tbl,

   // Ports for internal test and debug
   input  logic                                                                                  pa_dprio_clk,
   input  logic                                                                                  pa_dprio_read,
   input  logic [PORT_DFT_ND_PA_DPRIO_REG_ADDR_WIDTH-1:0]                                        pa_dprio_reg_addr,
   input  logic                                                                                  pa_dprio_rst_n,
   input  logic                                                                                  pa_dprio_write,
   input  logic [PORT_DFT_ND_PA_DPRIO_WRITEDATA_WIDTH-1:0]                                       pa_dprio_writedata,
   output logic                                                                                  pa_dprio_block_select_nonabphy,
   output logic [PORT_DFT_ND_PA_DPRIO_READDATA_WIDTH-1:0]                                        pa_dprio_readdata_nonabphy
);
   timeunit 1ns;
   timeprecision 1ps;

   // Enum that defines whether a lane is used or not, and in what mode.
   // This enum type is used to encode the LANES_USAGE_MODE parameter
   // passed into the io_tiles module.
   typedef enum bit [2:0] {
      LANE_USAGE_UNUSED  = 3'b000,
      LANE_USAGE_AC_HMC  = 3'b001,
      LANE_USAGE_AC_CORE = 3'b010,
      LANE_USAGE_RDATA   = 3'b011,
      LANE_USAGE_WDATA   = 3'b100,
      LANE_USAGE_WRDATA  = 3'b101
   } LANE_USAGE;

   // Enum that defines whether a pin is used by EMIF
   // This enum type is used to encode the PINS_USAGE parameter
   // passed into the io_tiles module.
   typedef enum bit [0:0] {
      PIN_USAGE_UNUSED   = 1'b0,
      PIN_USAGE_USED     = 1'b1
   } PIN_USAGE;

   // Enum that defines whether an EMIF pin operates at SDR or DDR.
   // This enum type is used to encode the PINS_RATE parameter
   // passed into the io_tiles module.
   typedef enum bit [0:0] {
      PIN_RATE_DDR       = 1'b0,
      PIN_RATE_SDR       = 1'b1
   } PIN_RATE;

   // Enum that defines the direction of an EMIF pin.
   typedef enum bit [0:0] {
      PIN_OCT_STATIC_OFF = 1'b0,
      PIN_OCT_DYNAMIC    = 1'b1
   } PIN_OCT_MODE;

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
 
   // Enum that defines the write data buffer procedural mode of an EMIF pin.
   // This enum type is used to encode the DB_PINS_PROC_MODE parameter
   // passed into the io_tiles module.
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

   // Enum that defines the pin data in mode of an EMIF pin.
   // This enum type is used to encode the PINS_DATA_IN_MODE parameter
   // passed into the io_tiles module.
   typedef enum bit [2:0] {
      PIN_DATA_IN_MODE_DISABLED             = 3'b000,
      PIN_DATA_IN_MODE_SSTL_IN              = 3'b001,
      PIN_DATA_IN_MODE_LOOPBACK_IN          = 3'b010,
      PIN_DATA_IN_MODE_XOR_LOOPBACK_IN      = 3'b011,
      PIN_DATA_IN_MODE_DIFF_IN              = 3'b100,
      PIN_DATA_IN_MODE_DIFF_IN_AVL_OUT      = 3'b101,
      PIN_DATA_IN_MODE_DIFF_IN_X12_OUT      = 3'b110,
      PIN_DATA_IN_MODE_DIFF_IN_AVL_X12_OUT  = 3'b111
   } PIN_DATA_IN_MODE;

   // Is HMC rate converter or dual-port feature turned on?
   // This can be inferred from the clock rates at core/periphery boundary and in HMC.
   localparam USE_HMC_RC_OR_DP = (C2P_P2C_CLK_RATIO == PHY_HMC_CLK_RATIO) ? 0 : 1;
   localparam LANE_DB_CLK_SEL = USE_HMC_RC_OR_DP ? "phy_clk1" : "phy_clk0";

   // The phase alignment blocks have synchronization signals between them
   logic [(NUM_OF_RTL_TILES * (LANES_PER_TILE + 1)):0] pa_sync_data_up_chain;
   logic [(NUM_OF_RTL_TILES * (LANES_PER_TILE + 1)):0] pa_sync_data_dn_chain;
   logic [(NUM_OF_RTL_TILES * (LANES_PER_TILE + 1)):0] pa_sync_clk_up_chain;
   logic [(NUM_OF_RTL_TILES * (LANES_PER_TILE + 1)):0] pa_sync_clk_dn_chain;
   assign pa_sync_data_dn_chain[NUM_OF_RTL_TILES * (LANES_PER_TILE + 1)] = 1'b1;
   assign pa_sync_clk_dn_chain [NUM_OF_RTL_TILES * (LANES_PER_TILE + 1)] = 1'b1;
   assign pa_sync_data_up_chain[0] = 1'b1;
   assign pa_sync_clk_up_chain [0] = 1'b1;

   // The Avalon command bus signal daisy-chains one tile to another
   // from bottom-to-top starting from the I/O aux.
   logic [NUM_OF_RTL_TILES-1:0][PORT_CALBUS_SEQ_PARAM_TBL_WIDTH-1:0] tile_param_tables;

   logic [(NUM_OF_RTL_TILES * (LANES_PER_TILE + 1)):0][54:0] cal_bus_avl_up_chain;
   assign cal_bus_avl_up_chain[0][19:0]  = cal_bus_avl_address;
   assign cal_bus_avl_up_chain[0][51:20] = cal_bus_avl_write_data;
   assign cal_bus_avl_up_chain[0][52]    = cal_bus_avl_write;
   assign cal_bus_avl_up_chain[0][53]    = cal_bus_avl_read;
   assign cal_bus_avl_up_chain[0][54]    = cal_bus_clk;

   // The Avalon read data signal daisy-chains one tile to another
   // from top-to-bottom ending at the I/O aux.
   logic [(NUM_OF_RTL_TILES * (LANES_PER_TILE + 1)):0][31:0] cal_bus_avl_read_data_dn_chain;
   assign cal_bus_avl_read_data = cal_bus_avl_read_data_dn_chain[0];
   assign cal_bus_avl_read_data_dn_chain[NUM_OF_RTL_TILES * (LANES_PER_TILE + 1)] = 32'b0;

   // Broadcast signals that daisy-chain all lanes in upward and downward directions.
   logic [(NUM_OF_RTL_TILES * LANES_PER_TILE):0][1:0] broadcast_up_chain;
   logic [(NUM_OF_RTL_TILES * LANES_PER_TILE):0][1:0] broadcast_dn_chain;
   assign broadcast_dn_chain[NUM_OF_RTL_TILES * LANES_PER_TILE] = 2'b11;
   assign broadcast_up_chain[0] = 2'b11;

   // HMC-to-DBC signals going from tiles to lanes and between tiles
   logic [NUM_OF_RTL_TILES:0][50:0] all_tiles_ctl2dbc0_dn_chain;
   logic [NUM_OF_RTL_TILES:0][50:0] all_tiles_ctl2dbc1_up_chain;
   assign all_tiles_ctl2dbc0_dn_chain[NUM_OF_RTL_TILES] = {51{1'b1}};
   assign all_tiles_ctl2dbc1_up_chain[0] = {51{1'b1}};

   // Ping-Pong signals going up the column
   logic [NUM_OF_RTL_TILES:0][101:0] all_tiles_ping_pong_up_chain;
   assign all_tiles_ping_pong_up_chain[0] = {102{1'b1}};

   // PHY clock signals going from tiles to lanes
   logic [NUM_OF_RTL_TILES-1:0][LANES_PER_TILE-1:0][7:0] all_tiles_t2l_phy_clk_phs;

   logic [LANES_PER_TILE-1:0][4:0] all_tiles_t2l_phy_clk;

   // DLL clock from tile_ctrl to lanes
   logic [NUM_OF_RTL_TILES-1:0][LANES_PER_TILE-1:0] all_tiles_dll_clk_out;

   // Outputs from the CPA inside each tile
   // In the following arrays, only elements at tile index PRI_AC_TILE_INDEX, corresponding to the addr/cmd tile, are used
   // In ping-pong configuration, the CPA inside the primary HMC tile is used, hence no need to account for secondary tile
   logic [NUM_OF_RTL_TILES-1:0][1:0] all_tiles_core_clks_out;
   logic [NUM_OF_RTL_TILES-1:0][1:0] all_tiles_core_clks_fb_in;
   logic [NUM_OF_RTL_TILES-1:0][1:0] all_tiles_core_clks_locked;

   assign core_clks_from_cpa_pri_nonabphy = {1'b0, all_tiles_core_clks_out[PRI_AC_TILE_INDEX][0]};
   assign core_clks_locked_cpa_pri_nonabphy = all_tiles_core_clks_locked[PRI_AC_TILE_INDEX];
   assign all_tiles_core_clks_fb_in[PRI_AC_TILE_INDEX] = core_clks_fb_to_cpa_pri;

   assign core_clks_from_cpa_sec_nonabphy = PHY_PING_PONG_EN ? {1'b0,all_tiles_core_clks_out[SEC_AC_TILE_INDEX][0]} : '0;
   assign core_clks_locked_cpa_sec_nonabphy = PHY_PING_PONG_EN ? all_tiles_core_clks_locked[SEC_AC_TILE_INDEX] : '0;
   generate
      if (PHY_PING_PONG_EN) begin
         assign all_tiles_core_clks_fb_in[SEC_AC_TILE_INDEX] = core_clks_fb_to_cpa_sec;
      end
   endgenerate

   // Outputs from PHY clock tree back to PLL
   // Physically, this connection needs to happen in every tile but
   // in RTL we only make this connection for the A/C tile (since we
   // only have one logical PLL)

   // Avalon signals between HMC and core
   // In the following arrays, only elements at tile index *_AC_TILE_INDEX, corresponding to the addr/cmd tile, are used
   logic [NUM_OF_RTL_TILES-1:0]       all_tiles_ctl2core_avl_cmd_ready;
   logic [NUM_OF_RTL_TILES-1:0][12:0] all_tiles_ctl2core_avl_rdata_id;

   assign ctl2core_avl_cmd_ready_0_nonabphy = all_tiles_ctl2core_avl_cmd_ready[PRI_AC_TILE_INDEX];
   assign ctl2core_avl_rdata_id_0_nonabphy  = all_tiles_ctl2core_avl_rdata_id[PRI_AC_TILE_INDEX];

   assign ctl2core_avl_cmd_ready_1_nonabphy = all_tiles_ctl2core_avl_cmd_ready[SEC_AC_TILE_INDEX];
   assign ctl2core_avl_rdata_id_1_nonabphy  = all_tiles_ctl2core_avl_rdata_id[SEC_AC_TILE_INDEX];

   // AFI signals between tile and core
   // In the following arrays, only elements at tile index PRI_AC_TILE_INDEX, corresponding to the addr/cmd tile, are used
   // Ping-Pong PHY doesn't support AFI interface so there's no need to account for SEC_AC_TILE_INDEX
   logic [NUM_OF_RTL_TILES-1:0][17:0] all_tiles_c2t_afi;
   logic [NUM_OF_RTL_TILES-1:0][26:0] all_tiles_t2c_afi;

   assign all_tiles_c2t_afi[PRI_AC_TILE_INDEX] = c2t_afi;
   assign t2c_afi_nonabphy = all_tiles_t2c_afi[PRI_AC_TILE_INDEX];

   // Sideband signals between HMC and core
   // In the following arrays, only elements at tile index *_AC_TILE_INDEX, corresponding to the addr/cmd tile, are used
   logic [NUM_OF_RTL_TILES-1:0][13:0] all_tiles_ctl2core_sideband;

   assign ctl2core_sideband_0_nonabphy = all_tiles_ctl2core_sideband[PRI_AC_TILE_INDEX];
   assign ctl2core_sideband_1_nonabphy = all_tiles_ctl2core_sideband[SEC_AC_TILE_INDEX];

   // MMR signals between HMC and core
   // In the following arrays, only elements at tile index *_AC_TILE_INDEX, corresponding to the addr/cmd tile, are used
   logic [NUM_OF_RTL_TILES-1:0][33:0] all_tiles_ctl2core_mmr;

   assign ctl2core_mmr_0_nonabphy = all_tiles_ctl2core_mmr[PRI_AC_TILE_INDEX];
   assign ctl2core_mmr_1_nonabphy = all_tiles_ctl2core_mmr[SEC_AC_TILE_INDEX];

   // CPA DPRIO signals (for internal debug)
   // In the following arrays, only elements at tile index PRI_AC_TILE_INDEX, corresponding to the addr/cmd tile, are used
   logic [NUM_OF_RTL_TILES-1:0]                                          all_tiles_pa_dprio_block_select;
   logic [NUM_OF_RTL_TILES-1:0][PORT_DFT_ND_PA_DPRIO_READDATA_WIDTH-1:0] all_tiles_pa_dprio_readdata;

   assign pa_dprio_readdata_nonabphy = all_tiles_pa_dprio_readdata[PRI_AC_TILE_INDEX];
   assign pa_dprio_block_select_nonabphy = all_tiles_pa_dprio_block_select[PRI_AC_TILE_INDEX];

   // FM Tile PHYCLK Atom 
   logic [2:0] phy_fbclk_pa;
   logic [1:0] phy_clk_hmc;

   // CPA DPRIO signals (for internal debug)
   logic [LANES_PER_TILE-1:0][1:0] phy_clk_local_early;
   logic [LANES_PER_TILE-1:0][1:0] phy_clk_local_late;

   logic       phy_rxloaden_tp_loopback, phy_rxloaden_btm_loopback;
   logic       phy_rxclk_tp_loopback, phy_rxclk_btm_loopback;
   logic       phy_fb_tp_loopback, phy_fb_btm_loopback;
   logic       phy_txloaden_tp_loopback, phy_txloaden_btm_loopback;
   logic       phy_txclk_tp_loopback, phy_txclk_btm_loopback;


   localparam VCO_FREQ_HZ_INT = PLL_VCO_FREQ_MHZ_INT * 1000000;

   `define cpa_clock_1_div_factor(vco_freq_mhz) \
       (vco_freq_mhz >=  600 && vco_freq_mhz <  800) ? "core_clk1_div2":   \
       (vco_freq_mhz >=  800 && vco_freq_mhz < 1000) ? "core_clk1_div2p5": \
       (vco_freq_mhz >= 1000 && vco_freq_mhz < 1200) ? "core_clk1_div3":   \
                                                       "core_clk1_div4"

   tennm_io48_phyclk phyclk_inst (
     .loaden_0               (phy_clk[0]),          // PHYCLK from the logical IOPLL
     .lvds_clk_0             (phy_clk[1]),          // PHYCLK from the logical IOPLL
     .fblvds                 (phy_fb_clk_to_tile),  // PLL signal going into PHY feedback clock; replaces tile_ctrl.pa_fbclk_in
     .loaden_1               (1'b0),                // Unused PHYCLK in an EMIF
     .lvds_clk_1             (1'b0),                // Unused PHYCLK in an EMIF

     // PHYCLK loopback timing paths
     .phy_fb_match_btm       (phy_fb_btm_loopback),
     .phy_fb_match_tp        (phy_fb_tp_loopback),
     .phy_rxclk_from_btm     (1'b0),
     .phy_rxclk_from_left    (1'b0),
     .phy_rxclk_from_right   (1'b0),
     .phy_rxclk_from_tp      (1'b0),
     .phy_rxclk_match_btm    (phy_rxclk_btm_loopback),
     .phy_rxclk_match_tp     (phy_rxclk_tp_loopback),
     .phy_rxloaden_from_btm  (1'b0),
     .phy_rxloaden_from_left (1'b0),
     .phy_rxloaden_from_right(1'b0),
     .phy_rxloaden_from_tp   (1'b0),
     .phy_rxloaden_match_btm (phy_rxloaden_btm_loopback),
     .phy_rxloaden_match_tp  (phy_rxloaden_tp_loopback),
     .phy_txclk_from_btm     (1'b0),
     .phy_txclk_from_left    (1'b0),
     .phy_txclk_from_right   (1'b0),
     .phy_txclk_from_tp      (1'b0),
     .phy_txclk_match_btm    (phy_txclk_btm_loopback),
     .phy_txclk_match_tp     (phy_txclk_tp_loopback),
     .phy_txloaden_from_btm  (1'b0),
     .phy_txloaden_from_left (1'b0),
     .phy_txloaden_from_right(1'b0),
     .phy_txloaden_from_tp   (1'b0),
     .phy_txloaden_match_btm (phy_txloaden_btm_loopback),
     .phy_txloaden_match_tp  (phy_txloaden_tp_loopback),
     
     .phy_clk_hmc          (phy_clk_hmc),  
     .fbclk_pa             (phy_fbclk_pa), 
     .fbclk_pll            (phy_fb_clk_to_pll_nonabphy), // to IOPLL feedback; we have one logical PLL

     .phy_clk_local_early0 (phy_clk_local_early[0]), 
     .phy_clk_local_early1 (phy_clk_local_early[1]), 
     .phy_clk_local_early2 (phy_clk_local_early[2]), 
     .phy_clk_local_early3 (phy_clk_local_early[3]), 
     .phy_clk_local_late0  (phy_clk_local_late[0]), 
     .phy_clk_local_late1  (phy_clk_local_late[1]), 
     .phy_clk_local_late2  (phy_clk_local_late[2]), 
     .phy_clk_local_late3  (phy_clk_local_late[3]), 

     .phy_clk_out_0        (all_tiles_t2l_phy_clk[0]), 
     .phy_clk_out_1        (all_tiles_t2l_phy_clk[1]), 
     .phy_clk_out_2        (all_tiles_t2l_phy_clk[2]), 
     .phy_clk_out_3        (all_tiles_t2l_phy_clk[3]), 

     .phy_clk_ufi_0        (global_phy_clk[0]),  // Global PHYCLK0 for C2P/P2C crossings
     .phy_clk_ufi_1        (global_phy_clk[1]),  // Global PHYCLK1 for C2P/P2C crossings
     .phy_clk_ufi_3        (/*open*/),           // Not used by EMIF (review NF EMIF Clock Topologies by Jimmy)

     // PHYCLK loopback timing paths
     .phy_fb_to_btm        (phy_fb_btm_loopback),
     .phy_fb_to_tp         (phy_fb_tp_loopback),
     .phy_rxclk_to_left    (/*open*/),
     .phy_rxclk_to_right   (/*open*/),
     .phy_rxclk_to_tp      (phy_rxclk_tp_loopback),
     .phy_rxclk_to_btm     (phy_rxclk_btm_loopback),
     .phy_rxloaden_to_left (/*open*/),
     .phy_rxloaden_to_right(/*open*/),
     .phy_rxloaden_to_tp   (phy_rxloaden_tp_loopback),
     .phy_rxloaden_to_btm  (phy_rxloaden_btm_loopback),
     .phy_txclk_to_left    (/*open*/),
     .phy_txclk_to_right   (/*open*/),
     .phy_txclk_to_tp      (phy_txclk_tp_loopback),
     .phy_txclk_to_btm     (phy_txclk_btm_loopback),
     .phy_txloaden_to_left (/*open*/),
     .phy_txloaden_to_right(/*open*/),
     .phy_txloaden_to_tp   (phy_txloaden_tp_loopback),
     .phy_txloaden_to_btm  (phy_txloaden_btm_loopback)
   );

                           
   ////////////////////////////////////////////////////////////////////////////
   // Generate tiles and lanes.
   ////////////////////////////////////////////////////////////////////////////

   logic [NUM_OF_RTL_TILES-1:0][LANES_PER_TILE-1:0][5:0]  l2vio_afi_rlat;
   logic [NUM_OF_RTL_TILES-1:0][LANES_PER_TILE-1:0][5:0]  l2vio_afi_wlat;
   logic [NUM_OF_RTL_TILES-1:0][LANES_PER_TILE-1:0][3:0]  l2vio_rdata_valid;
   logic [NUM_OF_RTL_TILES-1:0][LANES_PER_TILE-1:0]       l2vio_rd_type;

   logic [NUM_OF_RTL_TILES-1:0][LANES_PER_TILE-1:0]       l2vio_rd_data_vld_avl;
   logic [NUM_OF_RTL_TILES-1:0][LANES_PER_TILE-1:0]       l2vio_wr_data_rdy_ast;
   logic [NUM_OF_RTL_TILES-1:0][LANES_PER_TILE-1:0][11:0] l2vio_wb_pointer_for_ecc;



   localparam L2CORE_P2C_PER_IF_SIGS_TILE_INDEX = IS_HPS ? PRI_AC_TILE_INDEX : PRI_RDATA_TILE_INDEX;
   localparam L2CORE_P2C_PER_IF_SIGS_LANE_INDEX = IS_HPS ? PRI_HMC_DBC_SHADOW_LANE_INDEX : PRI_RDATA_LANE_INDEX;

   assign l2core_afi_rlat_nonabphy    = l2vio_afi_rlat[L2CORE_P2C_PER_IF_SIGS_TILE_INDEX][L2CORE_P2C_PER_IF_SIGS_LANE_INDEX];
   assign l2core_afi_wlat_nonabphy    = l2vio_afi_wlat[L2CORE_P2C_PER_IF_SIGS_TILE_INDEX][L2CORE_P2C_PER_IF_SIGS_LANE_INDEX];

   assign l2core_rdata_valid_nonabphy_pri    = l2vio_rdata_valid[L2CORE_P2C_PER_IF_SIGS_TILE_INDEX][L2CORE_P2C_PER_IF_SIGS_LANE_INDEX];
   assign l2core_rdata_valid_nonabphy_sec    = l2vio_rdata_valid[SEC_RDATA_TILE_INDEX][SEC_RDATA_LANE_INDEX];
   assign l2core_rd_data_vld_avl_nonabphy    = l2vio_rd_data_vld_avl[L2CORE_P2C_PER_IF_SIGS_TILE_INDEX][L2CORE_P2C_PER_IF_SIGS_LANE_INDEX];
   assign l2core_rd_type_nonabphy            = l2vio_rd_type[L2CORE_P2C_PER_IF_SIGS_TILE_INDEX][L2CORE_P2C_PER_IF_SIGS_LANE_INDEX];

   assign l2core_wr_data_rdy_ast_nonabphy    = l2vio_wr_data_rdy_ast[L2CORE_P2C_PER_IF_SIGS_TILE_INDEX][L2CORE_P2C_PER_IF_SIGS_LANE_INDEX];
   assign l2core_wb_pointer_for_ecc_nonabphy = l2vio_wb_pointer_for_ecc[L2CORE_P2C_PER_IF_SIGS_TILE_INDEX][L2CORE_P2C_PER_IF_SIGS_LANE_INDEX];

   localparam PRI_HMC_CFG_NO_OF_REF_FOR_SELF_RFSH = (PRI_HMC_CFG_REFRESH_TYPE == 2'b01 ? 4'h2 : (
                                                     PRI_HMC_CFG_REFRESH_TYPE == 2'b10 ? 4'h4 : (
                                                                                         4'h1   )));
   localparam SEC_HMC_CFG_NO_OF_REF_FOR_SELF_RFSH = (SEC_HMC_CFG_REFRESH_TYPE == 2'b01 ? 4'h2 : (
                                                     SEC_HMC_CFG_REFRESH_TYPE == 2'b10 ? 4'h4 : (
                                                                                         4'h1   )));

   // Select the param table data of the primary A/C tile
   assign cal_bus_seq_param_tbl = tile_param_tables[PRI_AC_TILE_INDEX];
   generate
      genvar tile_i, lane_i;
      for (tile_i = 0; tile_i < NUM_OF_RTL_TILES; ++tile_i)
      begin: tile_gen
         // DQS bus from tile to lanes
         logic [1:0]       t2l_dqsbus_x4 [LANES_PER_TILE-1:0];
         logic [1:0]       t2l_dqsbus_x8 [LANES_PER_TILE-1:0];
         logic [1:0]       t2l_dqsbus_x18 [LANES_PER_TILE-1:0];
         logic [1:0]       t2l_dqsbus_x36 [LANES_PER_TILE-1:0];

         // HMC AFI signals going to lanes.
         logic [3:0][95:0] t2l_ac_hmc;

         // HMC to Data buffer control blocks in the lanes
         logic [17:0]      t2l_cfg_dbc [LANES_PER_TILE-1:0];

         tennm_tile_ctrl # (
            .a_fmio96_hps_used                                                                    (IS_HPS ? "A_FMIO96_HPS_USED" : "A_FMIO96_HPS_UNUSED"),
            .mimic_hps                                                                            (PHY_MIMIC_HPS_EMIF ? "true" : "false"),
            .ioaux_param_table(SEQ_PT_CONTENT),
            .param_table_valid((tile_i == PRI_AC_TILE_INDEX) ? "true" : "false"),

            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_wdata_driver_sel_scalar          ("disable"),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_prbs_ctrl_sel_scalar             ("disable"),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_loopback_en_scalar               ("disable"),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_cmd_driver_sel_scalar            ("disable"),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_dbg_mode                         (4'b0000),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_dbg_ctrl                         (32'b00000000000000000000000000000000),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_bist_cmd0_u                      (32'b00000000000000000000000000000000),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_bist_cmd0_l                      (32'b00000000000000000000000000000000),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_bist_cmd1_u                      (32'b00000000000000000000000000000000),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_bist_cmd1_l                      (32'b00000000000000000000000000000000),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_dbg_out_sel                      (16'b0000000000000000),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_mem_type                         (`_get_hmc_ctrl_mem_type),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_dimm_type                        (HMC_CTRL_DIMM_TYPE),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_ac_pos                           (AC_PIN_MAP_SCHEME),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_addr_order                       (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_ADDR_ORDER , SEC_HMC_CFG_ADDR_ORDER )), // (hmc_addr_order V) Mapping of Avalon address to physical address of the memory device
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_ctrl_enable_ecc_scalar           (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_CTRL_ENABLE_ECC          , SEC_HMC_CFG_CTRL_ENABLE_ECC               )),  // Enable ECC
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_dbc0_enable_ecc_scalar           (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_DBC0_ENABLE_ECC          , SEC_HMC_CFG_DBC0_ENABLE_ECC               )),  // Enable ECC
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_dbc1_enable_ecc_scalar           (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_DBC1_ENABLE_ECC          , SEC_HMC_CFG_DBC1_ENABLE_ECC               )),  // Enable ECC
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_dbc2_enable_ecc_scalar           (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_DBC2_ENABLE_ECC          , SEC_HMC_CFG_DBC2_ENABLE_ECC               )),  // Enable ECC
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_dbc3_enable_ecc_scalar           (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_DBC3_ENABLE_ECC          , SEC_HMC_CFG_DBC3_ENABLE_ECC               )),  // Enable ECC
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_reorder_data_scalar              (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_REORDER_DATA             , SEC_HMC_CFG_REORDER_DATA                  )),  // Enable command reodering
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_ctrl_reorder_rdata_scalar        (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_CTRL_REORDER_RDATA       , SEC_HMC_CFG_CTRL_REORDER_RDATA            )),  // Enable in-order read data return when read command reordering is enabled
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_dbc0_reorder_rdata_scalar        (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_DBC0_REORDER_RDATA       , SEC_HMC_CFG_DBC0_REORDER_RDATA            )),  // Enable in-order read data return when read command reordering is enabled
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_dbc1_reorder_rdata_scalar        (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_DBC1_REORDER_RDATA       , SEC_HMC_CFG_DBC1_REORDER_RDATA            )),  // Enable in-order read data return when read command reordering is enabled
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_dbc2_reorder_rdata_scalar        (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_DBC2_REORDER_RDATA       , SEC_HMC_CFG_DBC2_REORDER_RDATA            )),  // Enable in-order read data return when read command reordering is enabled
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_dbc3_reorder_rdata_scalar        (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_DBC3_REORDER_RDATA       , SEC_HMC_CFG_DBC3_REORDER_RDATA            )),  // Enable in-order read data return when read command reordering is enabled
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_reorder_read_scalar              (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_REORDER_READ             , SEC_HMC_CFG_REORDER_READ                  )),  // Enable read command reordering if command reordering is enabled
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_starve_limit                     (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_STARVE_LIMIT             , SEC_HMC_CFG_STARVE_LIMIT                  )),  // When command reordering is enabled, specifies the number of commands that can be served before a starved command is starved.
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_dqstrk_en_scalar                 (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_DQSTRK_EN                , SEC_HMC_CFG_DQSTRK_EN                     )),  // Enable DQS tracking
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_ctrl_enable_dm_scalar            (MEM_DATA_MASK_EN ? "enable" : "disable"),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_dbc0_enable_dm_scalar            (MEM_DATA_MASK_EN ? "enable" : "disable"),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_dbc1_enable_dm_scalar            (MEM_DATA_MASK_EN ? "enable" : "disable"),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_dbc2_enable_dm_scalar            (MEM_DATA_MASK_EN ? "enable" : "disable"),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_dbc3_enable_dm_scalar            (MEM_DATA_MASK_EN ? "enable" : "disable"),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_ctrl2dbc_switch0                 (`_get_ctrl2dbc_switch_0(tile_i)),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_ctrl2dbc_switch1                 (`_get_ctrl2dbc_switch_1(tile_i)),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_dbc0_ctrl_sel_scalar             (`_get_ctrl2dbc_sel_0(tile_i)),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_dbc1_ctrl_sel_scalar             (`_get_ctrl2dbc_sel_1(tile_i)),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_dbc2_ctrl_sel_scalar             (`_get_ctrl2dbc_sel_2(tile_i)),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_dbc3_ctrl_sel_scalar             (`_get_ctrl2dbc_sel_3(tile_i)),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_dbc2ctrl_sel                     (`_get_hmc_dbc2ctrl_sel(tile_i)),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_dbc0_pipe_lat                    (3'(`_get_dbc_pipe_lat(tile_i, 0))),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_dbc1_pipe_lat                    (3'(`_get_dbc_pipe_lat(tile_i, 1))),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_dbc2_pipe_lat                    (3'(`_get_dbc_pipe_lat(tile_i, 2))),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_dbc3_pipe_lat                    (3'(`_get_dbc_pipe_lat(tile_i, 3))),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_ctrl_cmd_rate                    (`_get_hmc_cmd_rate),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_dbc0_cmd_rate                    (`_get_dbc0_cmd_rate),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_dbc1_cmd_rate                    (`_get_dbc1_cmd_rate),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_dbc2_cmd_rate                    (`_get_dbc2_cmd_rate),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_dbc3_cmd_rate                    (`_get_dbc3_cmd_rate),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_ctrl_in_protocol_scalar          (`_get_hmc_protocol),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_dbc0_in_protocol_scalar          (`_get_dbc0_protocol),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_dbc1_in_protocol_scalar          (`_get_dbc1_protocol),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_dbc2_in_protocol_scalar          (`_get_dbc2_protocol),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_dbc3_in_protocol_scalar          (`_get_dbc3_protocol),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_geardn_en_scalar                 (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_GEAR_DOWN_EN             , SEC_HMC_CFG_GEAR_DOWN_EN                  )),  // Gear-down (DDR4)
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_3dsref_ack_on_done_scalar        (`_sel_hmc_tile(tile_i, PRI_HMC_3DSREF_ACK_ON_DONE           , SEC_HMC_3DSREF_ACK_ON_DONE                )),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_cb_tbp_reload_fix_en_n_scalar    (`_get_hmc_cb_tbp_reload_fix_en_n),  
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_tile_id                          (tile_i[4:0]),                                       // HMC ID (0 for T0, 1 for T1, etc) - actual value set by Fitter based on placement
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_pingpong_mode                    ((tile_i == PRI_AC_TILE_INDEX) ? PRI_HMC_CFG_PING_PONG_MODE : ((tile_i == SEC_AC_TILE_INDEX ) ? SEC_HMC_CFG_PING_PONG_MODE : "pingpong_off")),  // Ping-Pong PHY mode
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_dbc0_slot_rotate_en              (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_DBC0_SLOT_ROTATE_EN      , SEC_HMC_CFG_DBC0_SLOT_ROTATE_EN           )),  // Command slot rotation
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_dbc1_slot_rotate_en              (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_DBC1_SLOT_ROTATE_EN      , SEC_HMC_CFG_DBC1_SLOT_ROTATE_EN           )),  // Command slot rotation
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_dbc2_slot_rotate_en              (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_DBC2_SLOT_ROTATE_EN      , SEC_HMC_CFG_DBC2_SLOT_ROTATE_EN           )),  // Command slot rotation
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_dbc3_slot_rotate_en              (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_DBC3_SLOT_ROTATE_EN      , SEC_HMC_CFG_DBC3_SLOT_ROTATE_EN           )),  // Command slot rotation
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_dbc0_slot_offset                 (`_sel_hmc_lane(tile_i, 0, PRI_HMC_CFG_DBC0_SLOT_OFFSET      , SEC_HMC_CFG_DBC0_SLOT_OFFSET              )),  // Command slot offset
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_dbc1_slot_offset                 (`_sel_hmc_lane(tile_i, 1, PRI_HMC_CFG_DBC1_SLOT_OFFSET      , SEC_HMC_CFG_DBC1_SLOT_OFFSET              )),  // Command slot offset
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_dbc2_slot_offset                 (`_sel_hmc_lane(tile_i, 2, PRI_HMC_CFG_DBC2_SLOT_OFFSET      , SEC_HMC_CFG_DBC2_SLOT_OFFSET              )),  // Command slot offset
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_dbc3_slot_offset                 (`_sel_hmc_lane(tile_i, 3, PRI_HMC_CFG_DBC3_SLOT_OFFSET      , SEC_HMC_CFG_DBC3_SLOT_OFFSET              )),  // Command slot offset
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_ctrl_rc_en_scalar                (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_CTRL_ENABLE_RC           , SEC_HMC_CFG_CTRL_ENABLE_RC                )),  // Enable rate-conversion feature
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_dbc0_rc_en_scalar                (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_DBC0_ENABLE_RC           , SEC_HMC_CFG_DBC0_ENABLE_RC                )),  // Enable rate-conversion feature
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_dbc1_rc_en_scalar                (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_DBC1_ENABLE_RC           , SEC_HMC_CFG_DBC1_ENABLE_RC                )),  // Enable rate-conversion feature
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_dbc2_rc_en_scalar                (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_DBC2_ENABLE_RC           , SEC_HMC_CFG_DBC2_ENABLE_RC                )),  // Enable rate-conversion feature
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_dbc3_rc_en_scalar                (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_DBC3_ENABLE_RC           , SEC_HMC_CFG_DBC3_ENABLE_RC                )),  // Enable rate-conversion feature
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_cs_chip                          (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_CS_TO_CHIP_MAPPING       , SEC_HMC_CFG_CS_TO_CHIP_MAPPING            )),  // Chip select mapping scheme
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_rb_reserved_entry                (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_RB_RESERVED_ENTRY        , SEC_HMC_CFG_RB_RESERVED_ENTRY             )),  // Number of entries reserved in read buffer before almost full is asserted. Should be set to 4 + 2 * user_pipe_stages
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_wb_reserved_entry                (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_WB_RESERVED_ENTRY        , SEC_HMC_CFG_WB_RESERVED_ENTRY             )),  // Number of entries reserved in write buffer before almost full is asserted. Should be set to 4 + 2 * user_pipe_stages
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_3ds_en_scalar                    (`_sel_hmc_tile(tile_i, PRI_HMC_3DS_EN                       , SEC_HMC_3DS_EN                            )),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_ck_inv_scalar                    ("disable"),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_dfx_bypass_en_scalar             ("disable"),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_tcl                              (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_TCL                      , SEC_HMC_CFG_TCL                           )),  // Memory CAS latency
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_mem_if_tcl                           (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_TCL                      , SEC_HMC_CFG_TCL                           )),  
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_power_saving_exit_cycles         (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_POWER_SAVING_EXIT_CYC    , SEC_HMC_CFG_POWER_SAVING_EXIT_CYC         )),  // The minimum number of cycles to stay in a low power state. This applies to both power down and self-refresh and should be set to the greater of tPD and tCKESR
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_mem_clk_disable_entry_cycles     (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_MEM_CLK_DISABLE_ENTRY_CYC, SEC_HMC_CFG_MEM_CLK_DISABLE_ENTRY_CYC     )),  // Set to a the number of clocks after the execution of an self-refresh to stop the clock.  This register is generally set based on PHY design latency and should generally not be changed
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_write_odt_chip                   (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_WRITE_ODT_CHIP           , SEC_HMC_CFG_WRITE_ODT_CHIP                )),  // ODT scheme setting for write command
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_read_odt_chip                    (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_READ_ODT_CHIP            , SEC_HMC_CFG_READ_ODT_CHIP                 )),  // ODT scheme setting for read command
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_rd_odt_on                        (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_RD_ODT_ON                , SEC_HMC_CFG_RD_ODT_ON                     )),  // Indicates number of memory clock cycle gap between read command and ODT signal rising edge
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_wr_odt_period                    (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_WR_ODT_PERIOD            , SEC_HMC_CFG_WR_ODT_PERIOD                 )),  // Indicates number of memory clock cycle write ODT signal should stay asserted after rising edge
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_rd_odt_period                    (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_RD_ODT_PERIOD            , SEC_HMC_CFG_RD_ODT_PERIOD                 )),  // Indicates number of memory clock cycle read ODT signal should stay asserted after rising edge
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_exit_pdn_for_dqstrk_scalar       ("disable"),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_cb_revert_ref_qual_scalar        ("disable"),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_self_rfsh_dqstrk_en_scalar       ("disable"),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_srf_zqcal_disable_scalar         (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_SRF_ZQCAL_DISABLE        , SEC_HMC_CFG_SRF_ZQCAL_DISABLE             )),  // Setting to disable ZQ Calibration after self refresh
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_mps_zqcal_disable_scalar         (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_MPS_ZQCAL_DISABLE        , SEC_HMC_CFG_MPS_ZQCAL_DISABLE             )),  // Setting to disable ZQ Calibration after Maximum Power Saving exit
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_mps_dqstrk_disable_scalar        (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_MPS_DQSTRK_DISABLE       , SEC_HMC_CFG_MPS_DQSTRK_DISABLE            )),  // Setting to disable DQS Tracking after Maximum Power Saving exit
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_sb_cg_disable_scalar             (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_SB_CG_DISABLE            , SEC_HMC_CFG_SB_CG_DISABLE                 )),  // Setting to disable mem_ck gating during self refresh and deep power down
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_user_rfsh_en_scalar              (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_USER_RFSH_EN             , SEC_HMC_CFG_USER_RFSH_EN                  )),  // Setting to enable user refresh
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_srf_autoexit_en_scalar           (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_SRF_AUTOEXIT_EN          , SEC_HMC_CFG_SRF_AUTOEXIT_EN               )),  // Setting to enable controller to exit Self Refresh when new command is detected
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_srf_entry_exit_block             (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_SRF_ENTRY_EXIT_BLOCK     , SEC_HMC_CFG_SRF_ENTRY_EXIT_BLOCK          )),  // Blocking arbiter from issuing commands
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_sb_ddr4_mr3                      (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_SB_DDR4_MR3              , SEC_HMC_CFG_SB_DDR4_MR3                   )),  // DDR4 MR3
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_sb_ddr4_mr4                      (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_SB_DDR4_MR4              , SEC_HMC_CFG_SB_DDR4_MR4                   )),  // DDR4 MR4
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_short_dqstrk_ctrl_en_scalar      (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_SHORT_DQSTRK_CTRL_EN     , SEC_HMC_CFG_SHORT_DQSTRK_CTRL_EN          )),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_period_dqstrk_ctrl_en_scalar     (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_PERIOD_DQSTRK_CTRL_EN    , SEC_HMC_CFG_PERIOD_DQSTRK_CTRL_EN         )),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_period_dqstrk_interval           (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_PERIOD_DQSTRK_INTERVAL   , SEC_HMC_CFG_PERIOD_DQSTRK_INTERVAL        )),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_t_param_dqstrk_to_valid_last     (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_DQSTRK_TO_VALID_LAST     , SEC_HMC_CFG_DQSTRK_TO_VALID_LAST          )),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_t_param_dqstrk_to_valid          (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_DQSTRK_TO_VALID          , SEC_HMC_CFG_DQSTRK_TO_VALID               )),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_rfsh_warn_threshold              (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_RFSH_WARN_THRESHOLD      , SEC_HMC_CFG_RFSH_WARN_THRESHOLD           )),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_t_param_act_to_rdwr              (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_ACT_TO_RDWR              , SEC_HMC_CFG_ACT_TO_RDWR                   )),  // Activate to Read/write command timing (e.g. tRCD)
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_t_param_act_to_pch               (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_ACT_TO_PCH               , SEC_HMC_CFG_ACT_TO_PCH                    )),  // Active to precharge (e.g. tRAS)
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_t_param_act_to_act               (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_ACT_TO_ACT               , SEC_HMC_CFG_ACT_TO_ACT                    )),  // Active to activate timing on same bank (e.g. tRC)
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_t_param_act_to_act_diff_bank     (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_ACT_TO_ACT_DIFF_BANK     , SEC_HMC_CFG_ACT_TO_ACT_DIFF_BANK          )),  // Active to activate timing on different banks, for DDR4 same bank group (e.g. tRRD)
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_t_param_act_to_act_diff_bg       (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_ACT_TO_ACT_DIFF_BG       , SEC_HMC_CFG_ACT_TO_ACT_DIFF_BG            )),  // Active to activate timing on different bank groups, DDR4 only
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_t_param_rd_to_rd                 (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_RD_TO_RD                 , SEC_HMC_CFG_RD_TO_RD                      )),  // Read to read command timing on same bank (e.g. tCCD)
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_t_param_rd_to_rd_diff_chip       (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_RD_TO_RD_DIFF_CHIP       , SEC_HMC_CFG_RD_TO_RD_DIFF_CHIP            )),  // Read to read command timing on different chips
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_t_param_rd_to_rd_diff_bg         (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_RD_TO_RD_DIFF_BG         , SEC_HMC_CFG_RD_TO_RD_DIFF_BG              )),  // Read to read command timing on different chips
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_t_param_rd_to_wr                 (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_RD_TO_WR                 , SEC_HMC_CFG_RD_TO_WR                      )),  // Read to write command timing on same bank
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_t_param_rd_to_wr_diff_chip       (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_RD_TO_WR_DIFF_CHIP       , SEC_HMC_CFG_RD_TO_WR_DIFF_CHIP            )),  // Read to write command timing on different chips
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_t_param_rd_to_wr_diff_bg         (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_RD_TO_WR_DIFF_BG         , SEC_HMC_CFG_RD_TO_WR_DIFF_BG              )),  // Read to write command timing on different bank groups
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_t_param_rd_to_pch                (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_RD_TO_PCH                , SEC_HMC_CFG_RD_TO_PCH                     )),  // Read to precharge command timing (e.g. tRTP)
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_t_param_rd_ap_to_valid           (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_RD_AP_TO_VALID           , SEC_HMC_CFG_RD_AP_TO_VALID                )),  // Read command with autoprecharge to data valid timing
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_t_param_wr_to_wr                 (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_WR_TO_WR                 , SEC_HMC_CFG_WR_TO_WR                      )),  // Write to write command timing on same bank. (e.g. tCCD)
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_t_param_wr_to_wr_diff_chip       (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_WR_TO_WR_DIFF_CHIP       , SEC_HMC_CFG_WR_TO_WR_DIFF_CHIP            )),  // Write to write command timing on different chips.
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_t_param_wr_to_wr_diff_bg         (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_WR_TO_WR_DIFF_BG         , SEC_HMC_CFG_WR_TO_WR_DIFF_BG              )),  // Write to write command timing on different bank groups.
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_t_param_wr_to_rd                 (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_WR_TO_RD                 , SEC_HMC_CFG_WR_TO_RD                      )),  // Write to read command timing. (e.g. tWTR)
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_t_param_wr_to_rd_diff_chip       (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_WR_TO_RD_DIFF_CHIP       , SEC_HMC_CFG_WR_TO_RD_DIFF_CHIP            )),  // Write to read command timing on different chips.
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_t_param_wr_to_rd_diff_bg         (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_WR_TO_RD_DIFF_BG         , SEC_HMC_CFG_WR_TO_RD_DIFF_BG              )),  // Write to read command timing on different bank groups
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_t_param_wr_to_pch                (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_WR_TO_PCH                , SEC_HMC_CFG_WR_TO_PCH                     )),  // Write to precharge command timing. (e.g. tWR)
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_t_param_wr_ap_to_valid           (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_WR_AP_TO_VALID           , SEC_HMC_CFG_WR_AP_TO_VALID                )),  // Write with autoprecharge to valid command timing.
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_t_param_pch_to_valid             (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_PCH_TO_VALID             , SEC_HMC_CFG_PCH_TO_VALID                  )),  // Precharge to valid command timing. (e.g. tRP)
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_t_param_pch_all_to_valid         (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_PCH_ALL_TO_VALID         , SEC_HMC_CFG_PCH_ALL_TO_VALID              )),  // Precharge all to banks being ready for bank activation command.
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_t_param_arf_to_valid             (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_ARF_TO_VALID             , SEC_HMC_CFG_ARF_TO_VALID                  )),  // Auto Refresh to valid DRAM command window.
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_t_param_pdn_to_valid             (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_PDN_TO_VALID             , SEC_HMC_CFG_PDN_TO_VALID                  )),  // Power down to valid bank command window.
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_t_param_srf_to_valid             (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_SRF_TO_VALID             , SEC_HMC_CFG_SRF_TO_VALID                  )),  // Self-refresh to valid bank command window. (e.g. tRFC)
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_t_param_srf_to_zq_cal            (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_SRF_TO_ZQ_CAL            , SEC_HMC_CFG_SRF_TO_ZQ_CAL                 )),  // Self refresh to ZQ calibration window
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_t_param_arf_period               (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_ARF_PERIOD               , SEC_HMC_CFG_ARF_PERIOD                    )),  // Auto-refresh period (e.g. tREFI)
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_t_param_pdn_period               (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_PDN_PERIOD               , SEC_HMC_CFG_PDN_PERIOD                    )),  // Number of controller cycles before automatic power down.
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_t_param_zqcl_to_valid            (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_ZQCL_TO_VALID            , SEC_HMC_CFG_ZQCL_TO_VALID                 )),  // Long ZQ calibration to valid
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_t_param_zqcs_to_valid            (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_ZQCS_TO_VALID            , SEC_HMC_CFG_ZQCS_TO_VALID                 )),  // Short ZQ calibration to valid
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_t_param_mrs_to_valid             (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_MRS_TO_VALID             , SEC_HMC_CFG_MRS_TO_VALID                  )),  // Mode Register Setting to valid (e.g. tMRD)
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_t_param_mps_to_valid             (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_MPS_TO_VALID             , SEC_HMC_CFG_MPS_TO_VALID                  )),  // Max Power Saving to Valid
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_t_param_mrr_to_valid             (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_MRR_TO_VALID             , SEC_HMC_CFG_MRR_TO_VALID                  )),  // Mode Register Read to Valid
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_t_param_mpr_to_valid             (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_MPR_TO_VALID             , SEC_HMC_CFG_MPR_TO_VALID                  )),  // Multi Purpose Register Read to Valid
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_t_param_mps_exit_cs_to_cke       (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_MPS_EXIT_CS_TO_CKE       , SEC_HMC_CFG_MPS_EXIT_CS_TO_CKE            )),  // Max Power Saving CS to CKE
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_t_param_mps_exit_cke_to_cs       (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_MPS_EXIT_CKE_TO_CS       , SEC_HMC_CFG_MPS_EXIT_CKE_TO_CS            )),  // Max Power Saving CKE to CS
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_t_param_mmr_cmd_to_valid         (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_MMR_CMD_TO_VALID         , SEC_HMC_CFG_MMR_CMD_TO_VALID              )),  // MMR cmd to valid delay
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_t_param_4_act_to_act             (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_4_ACT_TO_ACT             , SEC_HMC_CFG_4_ACT_TO_ACT                  )),  // The four-activate window timing parameter. (e.g. tFAW)
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_col_addr_width                   (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_COL_ADDR_WIDTH           , SEC_HMC_CFG_COL_ADDR_WIDTH                )),  // Column address width
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_row_addr_width                   (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_ROW_ADDR_WIDTH           , SEC_HMC_CFG_ROW_ADDR_WIDTH                )),  // Row address width
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_bank_addr_width                  (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_BANK_ADDR_WIDTH          , SEC_HMC_CFG_BANK_ADDR_WIDTH               )),  // Bank address width
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_bank_group_addr_width            (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_BANK_GROUP_ADDR_WIDTH    , SEC_HMC_CFG_BANK_GROUP_ADDR_WIDTH         )),  // Bank group address width
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_cs_addr_width                    (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_CS_ADDR_WIDTH            , SEC_HMC_CFG_CS_ADDR_WIDTH                 )),  // Address width in bits required to access every CS in interface
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_sb_ddr4_mr5                      (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_SB_DDR4_MR5              , SEC_HMC_CFG_SB_DDR4_MR5                   )),  // DDR4 MR5
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_ddr4_mps_addrmirror_scalar       (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_DDR4_MPS_ADDRMIRROR      , SEC_HMC_CFG_DDR4_MPS_ADDRMIRROR           )),  // DDR4 MPS Address Mirror
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_3ds_lr_num0                      (`_sel_hmc_tile(tile_i, PRI_HMC_3DS_LR_NUM0                  , SEC_HMC_3DS_LR_NUM0                       )),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_3ds_lr_num1                      (`_sel_hmc_tile(tile_i, PRI_HMC_3DS_LR_NUM1                  , SEC_HMC_3DS_LR_NUM1                       )),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_3ds_lr_num2                      (`_sel_hmc_tile(tile_i, PRI_HMC_3DS_LR_NUM2                  , SEC_HMC_3DS_LR_NUM2                       )),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_3ds_lr_num3                      (`_sel_hmc_tile(tile_i, PRI_HMC_3DS_LR_NUM3                  , SEC_HMC_3DS_LR_NUM3                       )),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_cid_addr_width                   (`_sel_hmc_tile(tile_i, PRI_HMC_CID_ADDR_WIDTH               , SEC_HMC_CID_ADDR_WIDTH                    )),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_3ds_pr_stag_enable_scalar        (`_sel_hmc_tile(tile_i, PRI_HMC_3DS_PR_STAG_ENABLE           , SEC_HMC_3DS_PR_STAG_ENABLE                )),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_3ds_ref2ref_dlr                  (`_sel_hmc_tile(tile_i, PRI_HMC_3DS_REF2REF_DLR              , SEC_HMC_3DS_REF2REF_DLR                   )),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_chip_id                          (`_sel_hmc_tile(tile_i, PRI_HMC_CHIP_ID                      , SEC_HMC_CHIP_ID                           )),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_arbiter_reg_ena_scalar           ("disable"),                                               // Unused
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_wb_ptr_reg_ena_scalar            ("disable"),                                               // Intended for hard circuitry timing closure, but currently not necessary
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_rb_ptr_reg_ena_scalar            ("disable"),                                               // Intended for hard circuitry timing closure, but currently not necessary
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_ctl2dbc_reg_ena_scalar           ("enable"),                                               // Unused
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_ctl2dbc_tile_reg_ena_scalar      ("enable"),                                               // Intended for hard circuitry timing closure, but currently not necessary
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_ac_tile_reg_ena_scalar           ("disable"),                                               // Intended for hard circuitry timing closure, but currently not necessary
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_mem_if_tcwl                          (`_sel_hmc_tile(tile_i, PRI_HMC_MEM_IF_TCWL                  , SEC_HMC_MEM_IF_TCWL                       )),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_mem_if_al                            (`_sel_hmc_tile(tile_i, PRI_HMC_MEM_IF_AL                    , SEC_HMC_MEM_IF_AL                         )),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_mem_if_tpl                           (`_sel_hmc_tile(tile_i, PRI_HMC_MEM_IF_TPL                   , SEC_HMC_MEM_IF_TPL                        )),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_mem_if_trcd                          (`_sel_hmc_tile(tile_i, PRI_HMC_MEM_IF_TRCD                  , SEC_HMC_MEM_IF_TRCD                       )),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_mem_if_tras                          (`_sel_hmc_tile(tile_i, PRI_HMC_MEM_IF_TRAS                  , SEC_HMC_MEM_IF_TRAS                       )),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_mem_if_trp                           (`_sel_hmc_tile(tile_i, PRI_HMC_MEM_IF_TRP                   , SEC_HMC_MEM_IF_TRP                        )),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_mem_if_trp_ab                        (32'd0),                                                   // DON'T CARE; drive to default
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_mem_if_trc                           (`_sel_hmc_tile(tile_i, PRI_HMC_MEM_IF_TRC                   , SEC_HMC_MEM_IF_TRC                        )),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_mem_if_trrd                          (`_sel_hmc_tile(tile_i, PRI_HMC_MEM_IF_TRRD                  , SEC_HMC_MEM_IF_TRRD                       )),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_mem_if_tfaw                          (`_sel_hmc_tile(tile_i, PRI_HMC_MEM_IF_TFAW                  , SEC_HMC_MEM_IF_TFAW                       )),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_mem_if_trfc                          (`_sel_hmc_tile(tile_i, PRI_HMC_MEM_IF_TRFC                  , SEC_HMC_MEM_IF_TRFC                       )),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_mem_if_3ds_trfc_dlr                  (32'd0),                                                   // DON'T CARE; drive to default
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_mem_if_txpdll                        (`_sel_hmc_tile(tile_i, PRI_HMC_MEM_IF_TXPDLL                , SEC_HMC_MEM_IF_TXPDLL                     )),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_mem_if_txsr                          (`_sel_hmc_tile(tile_i, PRI_HMC_MEM_IF_TXSR                  , SEC_HMC_MEM_IF_TXSR                       )),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_mem_if_tckesr                        (`_sel_hmc_tile(tile_i, PRI_HMC_MEM_IF_TCKESR                , SEC_HMC_MEM_IF_TCKESR                     )),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_mem_if_tcksrx                        (`_sel_hmc_tile(tile_i, PRI_HMC_MEM_IF_TCKSRX                , SEC_HMC_MEM_IF_TCKSRX                     )),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_mem_if_tccd                          (`_sel_hmc_tile(tile_i, PRI_HMC_MEM_IF_TCCD                  , SEC_HMC_MEM_IF_TCCD                       )),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_mem_if_twr                           (`_sel_hmc_tile(tile_i, PRI_HMC_MEM_IF_TWR                   , SEC_HMC_MEM_IF_TWR                        )),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_mem_if_tzqcs                         (`_sel_hmc_tile(tile_i, PRI_HMC_MEM_IF_TZQCS                 , SEC_HMC_MEM_IF_TZQCS                      )),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_mem_if_tzqoper                       (`_sel_hmc_tile(tile_i, PRI_HMC_MEM_IF_TZQOPER               , SEC_HMC_MEM_IF_TZQOPER                    )),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_mem_if_tmod                          (`_sel_hmc_tile(tile_i, PRI_HMC_MEM_IF_TMOD                  , SEC_HMC_MEM_IF_TMOD                       )),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_mem_if_trefi                         (`_sel_hmc_tile(tile_i, PRI_HMC_MEM_IF_TREFI                 , SEC_HMC_MEM_IF_TREFI                      )),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_mem_auto_pd_cycles                   (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_MEM_AUTO_PD_CYCLES       , SEC_HMC_CFG_MEM_AUTO_PD_CYCLES            )),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_mem_if_trtp                          (`_sel_hmc_tile(tile_i, PRI_HMC_MEM_IF_TRTP                  , SEC_HMC_MEM_IF_TRTP                       )),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_mem_if_twtr                          (`_sel_hmc_tile(tile_i, PRI_HMC_MEM_IF_TWTR                  , SEC_HMC_MEM_IF_TWTR                       )),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_mem_if_trrd_s                        (`_sel_hmc_tile(tile_i, PRI_HMC_MEM_IF_TRRD_S                , SEC_HMC_MEM_IF_TRRD_S                     )),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_mem_if_tccd_s                        (`_sel_hmc_tile(tile_i, PRI_HMC_MEM_IF_TCCD_S                , SEC_HMC_MEM_IF_TCCD_S                     )),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_mem_if_wr_preamble                   (`_sel_hmc_tile(tile_i, PRI_HMC_MEM_IF_WR_PREAMBLE           , SEC_HMC_MEM_IF_WR_PREAMBLE                )),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_mem_if_rd_preamble                   (`_sel_hmc_tile(tile_i, PRI_HMC_MEM_IF_RD_PREAMBLE           , SEC_HMC_MEM_IF_RD_PREAMBLE                )),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_mem_if_wr_crc                        (`_sel_hmc_tile(tile_i, PRI_HMC_MEM_IF_WR_CRC                , SEC_HMC_MEM_IF_WR_CRC                     )),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_mem_if_twtr_l_crc_dm                 (`_sel_hmc_tile(tile_i, PRI_HMC_MEM_IF_TWTR_L_CRC_DM         , SEC_HMC_MEM_IF_TWTR_L_CRC_DM              )),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_mem_if_twtr_s_crc_dm                 (`_sel_hmc_tile(tile_i, PRI_HMC_MEM_IF_TWTR_S_CRC_DM         , SEC_HMC_MEM_IF_TWTR_S_CRC_DM              )),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_mem_if_twr_crc_dm                    (`_sel_hmc_tile(tile_i, PRI_HMC_MEM_IF_TWR_CRC_DM            , SEC_HMC_MEM_IF_TWR_CRC_DM                 )),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_mem_if_twtr_s                        (`_sel_hmc_tile(tile_i, PRI_HMC_MEM_IF_TWTR_S                , SEC_HMC_MEM_IF_TWTR_S                     )),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_mem_if_txp                           (`_sel_hmc_tile(tile_i, PRI_HMC_MEM_IF_TXP                   , SEC_HMC_MEM_IF_TXP                        )),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_mem_if_tdqsckmax                     (`_sel_hmc_tile(tile_i, PRI_HMC_MEM_IF_TDQSCKMAX             , SEC_HMC_MEM_IF_TDQSCKMAX                  )),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_ctl_odt_enabled                      (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_CTL_ODT_ENABLED          , SEC_HMC_CFG_CTL_ODT_ENABLED               )),  // ODT enabled
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_mem_if_cs_per_dimm                   (`_sel_hmc_tile(tile_i, PRI_HMC_MEM_IF_CS_PER_DIMM           , SEC_HMC_MEM_IF_CS_PER_DIMM                )),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_enable_fast_exit_ppd                 (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_ENABLE_FAST_EXIT_PPD     , SEC_HMC_CFG_ENABLE_FAST_EXIT_PPD          )),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_ctl_short_dqstrk_en                  (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_CTL_SHORT_DQSTRK_EN      , SEC_HMC_CFG_CTL_SHORT_DQSTRK_EN           )),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_hmc_phy_delay_mismatch               (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_PHY_DELAY_MISMATCH       , SEC_HMC_CFG_PHY_DELAY_MISMATCH            )),

            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_va_cfg_hmc_mode                      ("prod"),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_cmd_fifo_reserve_entry           (0),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_ctl2dbc_io_pipeline_en_scalar    (DBC_EXTRA_PIPE_STAGE_EN),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_livelock_breaker_en_scalar       ("enable"),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_memclkgate_setting               (0),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_opportunistic_rfsh_en_scalar     ("disable"),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_rfsh_idle_threshold              (0),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_core_wr_pipeline_wdata               (0),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_mem_if_lpasr                         (0),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_ufi_pipeline_wdata                   (0),

            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_col_cmd_slot                     (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_COL_CMD_SLOT             , SEC_HMC_CFG_COL_CMD_SLOT                  )),  // Command slot for column commands
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_row_cmd_slot                     (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_ROW_CMD_SLOT             , SEC_HMC_CFG_ROW_CMD_SLOT                  )),  // Command slot for row commands
            .iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_col_to_row_offset                            (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_COL_TO_ROW_OFFSET        , SEC_HMC_CFG_COL_TO_ROW_OFFSET             )),  // Command slot offset from col to row command
            .iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_row_to_col_offset                            (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_ROW_TO_COL_OFFSET        , SEC_HMC_CFG_ROW_TO_COL_OFFSET             )),  // Command slot offset from row to col command
            .iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_col_to_col_offset                            (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_COL_TO_COL_OFFSET        , SEC_HMC_CFG_COL_TO_COL_OFFSET             )),  // Command slot offset from col to col command
            .iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_col_to_diff_col_offset                       (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_COL_TO_DIFF_COL_OFFSET   , SEC_HMC_CFG_COL_TO_DIFF_COL_OFFSET        )),  // Command slot offset from col to col command (different columns)
            .iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_row_to_row_offset                            (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_ROW_TO_ROW_OFFSET        , SEC_HMC_CFG_ROW_TO_ROW_OFFSET             )),  // Command slot offset from row to row commandr
            .iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_ctl_width_ratio                              (PHY_HMC_CLK_RATIO == 2 ? 32'd4 : 32'd8),                  // Virtual setting. Unused
             
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_temp_cfg_t_param_wr_to_rd            (`_sel_hmc_tile(tile_i, PRI_HMC_TEMP_WR_TO_RD                , SEC_HMC_TEMP_WR_TO_RD                     )),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_temp_cfg_t_param_wr_to_rd_diff_chip  (`_sel_hmc_tile(tile_i, PRI_HMC_TEMP_WR_TO_RD_DIFF_CHIP      , SEC_HMC_TEMP_WR_TO_RD_DIFF_CHIP           )),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_temp_cfg_t_param_wr_to_rd_diff_bg    (`_sel_hmc_tile(tile_i, PRI_HMC_TEMP_WR_TO_RD_DIFF_BG        , SEC_HMC_TEMP_WR_TO_RD_DIFF_BG             )),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_temp_cfg_t_param_wr_to_wr_diff_bg    (`_sel_hmc_tile(tile_i, PRI_HMC_TEMP_WR_TO_WR_DIFF_BG        , SEC_HMC_TEMP_WR_TO_WR_DIFF_BG             )),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_temp_cfg_t_param_rd_to_rd_diff_bg    (`_sel_hmc_tile(tile_i, PRI_HMC_TEMP_RD_TO_RD_DIFF_BG        , SEC_HMC_TEMP_RD_TO_RD_DIFF_BG             )),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_temp_cfg_t_param_4_act_to_act        (`_sel_hmc_tile(tile_i, PRI_HMC_TEMP_4_ACT_TO_ACT            , SEC_HMC_TEMP_4_ACT_TO_ACT                 )),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_pipeline_wdata_path                  ("disable"), 
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_pipeline_rdata_path                  ("disable"), 
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_rd_to_rd_extra                       (32'd0),     
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_wr_to_wr_extra                       (32'd0),     
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_rd_to_wr_extra                       (32'd0),     
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_wr_to_rd_extra                       (32'd0),     
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_rd_to_rd_diff_chip_extra             (32'd0),     
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_wr_to_wr_diff_chip_extra             (32'd0),     
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_rd_to_wr_diff_chip_extra             (32'd0),     
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_wr_to_rd_diff_chip_extra             (32'd0),     
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_rd_to_rd_diff_bg_extra               (32'd0),     
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_wr_to_wr_diff_bg_extra               (32'd0),     
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_rd_to_wr_diff_bg_extra               (32'd0),     
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_wr_to_rd_diff_bg_extra               (32'd0),     
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_num_of_mem_clk_pair                  (32'd1),     

            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_periodic_refresh_type                (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_REFRESH_TYPE               , SEC_HMC_CFG_REFRESH_TYPE)),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_no_of_ref_for_self_rfsh          (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_NO_OF_REF_FOR_SELF_RFSH    , SEC_HMC_CFG_NO_OF_REF_FOR_SELF_RFSH)),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_major_mode_en_scalar             (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_MAJOR_MODE_EN              , SEC_HMC_CFG_MAJOR_MODE_EN)),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_post_rfsh_en_scalar              (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_POST_REFRESH_EN            , SEC_HMC_CFG_POST_REFRESH_EN)),  
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_rfsh_post_upper_limit            (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_POST_REFRESH_UPPER_LIMIT   , SEC_HMC_CFG_POST_REFRESH_UPPER_LIMIT)),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_rfsh_post_lower_limit            (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_POST_REFRESH_LOWER_LIMIT   , SEC_HMC_CFG_POST_REFRESH_LOWER_LIMIT)),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_pre_rfsh_en_scalar               (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_PRE_REFRESH_EN             , SEC_HMC_CFG_PRE_REFRESH_EN)),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_rfsh_pre_upper_limit             (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_PRE_REFRESH_UPPER_LIMIT    , SEC_HMC_CFG_PRE_REFRESH_UPPER_LIMIT)),
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_cb_3ds_pdown_exit_for_ref_scalar ("disable"), 
            .u4_0_x0_iohmc_ctrl_inst_iohmc_ctrl_mmr_top_inst_cfg_dual_ping_pong_en_scalar         ("disable"), 

            .u4_0_x0_iophyseq_inst_a_rb_tile_id                                                   (`_get_center_tid(tile_i)),
            .u4_0_x0_iophyseq_inst_a_rb_avl_ena                                                   ("avl_enable"),
            .u4_0_x0_iophyseq_inst_a_rb_hmc_or_core                                               (`_get_hmc_or_core_physeq),
            .u4_0_x0_iophyseq_inst_a_rb_trk_mgr_mrnk_mode                                         ("one_rank"),
            .u4_0_x0_iophyseq_inst_a_rb_trk_mgr_read_monitor_ena                                  ("disable"),                                         // Must be disabled to avoid an issue with tracking manager (ICD)
            .u4_0_x0_iophyseq_inst_a_rb_hmc_id                                                    (`_get_hmc_tid(tile_i)),                             // HMC tile ID - actual value is set by fitter based on placement
            .u4_0_x0_iophyseq_inst_a_rb_reset_auto_release                                        (DIAG_SEQ_RESET_AUTO_RELEASE),                       // Reset sequencer controlled via Avalon by Nios
            .u4_0_x0_iophyseq_inst_a_rb_rwlat_mode                                                ("avl_vlu"),                                         // wlat/rlat set dynamically via Avalon by Nios (instead of through CSR)
            .u4_0_x0_iophyseq_inst_a_rb_afi_rlat_vlu                                              (6'b000000),                                         // Unused - wlat set dynamically via Avalon by Nios
            .u4_0_x0_iophyseq_inst_a_rb_afi_wlat_vlu                                              (6'b000000),                                         // Unused - rlat set dynamically via Avalon by Nios
            .u4_0_x0_iophyseq_inst_a_rb_core_clk_sel                                              (USE_HMC_RC_OR_DP ? "clk1" : "clk0"),                // Use clk1 in rate-converter or dual-port mode, and clk0 otherwise
            .u4_0_x0_iophyseq_inst_a_afi_seq_busy_extend                                          ("extend_8cycles"),
            .u4_0_x0_powermode_ac                                                                 (tile_i == PRI_AC_TILE_INDEX ? "ac_tile" : "data_tile"),   //
            .u4_0_x0_powermode_dc                                                                 ("powerup"),                                               // Power-up this HMC

            .u1_0_x0_powermode_dc                                                                 ("powerup"),

            .powermode_freq_hz_phs_clk                                                            (VCO_FREQ_HZ_INT),  

            .u1_0_x0_xio_phase_align_pnr_a_rbpa_phase_offset_0                                    (12'b0),                 // Output clock phase degree = phase_offset / 128 * 360
            .u1_0_x0_xio_phase_align_pnr_a_rbpa_phase_offset_1                                    (12'b0),                 // Output clock phase degree = phase_offset / 128 * 360
            .u1_0_x0_xio_phase_align_pnr_a_rbpa_core_control_en_0                                 ("core_disable_0"),      
            .u1_0_x0_xio_phase_align_pnr_a_rbpa_core_control_en_1                                 ("core_disable_1"),      
            .u1_0_x0_xio_phase_align_pnr_a_rbpa_pa_reset_enable                                   ("pa_reset_en"),      
            .u1_0_x0_xio_phase_align_pnr_a_dprio_base_addr                                        (9'b000000000),
            .u1_0_x0_xio_phase_align_pnr_a_rbpa_filter_code                                       (`_get_pa_filter_code),
            .u1_0_x0_xio_phase_align_pnr_a_support_dpa                                            ("not_support_dpa"),     // VALID only for LVDS

            .u1_0_x0_xio_phase_align_pnr_a_core_clk0_pll_vco_freq_divide                          (`_get_cpa_0_clk_divider),
            .u1_0_x0_xio_phase_adjust_xio_pa_peri_fb_mux_0_a_rbpa_feedback_mux_sel                ((PRI_HMC_CFG_CTRL_ENABLE_RC == "enable") ? "fb1_p_clk" : "fb0_p_clk"),

            .u1_0_x0_xio_phase_align_pnr_a_core_clk1_pll_vco_freq_divide                          (`cpa_clock_1_div_factor(PLL_VCO_FREQ_MHZ_INT)),
            .u1_0_x0_xio_phase_align_pnr_a_dpa_clk_pll_vco_freq_divide                            ("dpa_clk_div1"), 
            .u1_0_x0_xio_phase_align_pnr_a_fb_core_clk0_phy_clk0_freq_divide                      (`_get_pa_feedback_divider_p0),
            .u1_0_x0_xio_phase_adjust_xio_pa_peri_fb_mux_1_a_rbpa_feedback_mux_sel                (CPA_FB_MUX_1_SEL),
            .u1_0_x0_xio_phase_adjust_xio_pa_feedback_path_1_a_rbpa_feedback_path                 ("feedback_path_0"),     
            .u1_0_x0_xio_phase_adjust_xio_pa_feedback_gate_1_a_rbpa_feedback_gate_sel             ("gate_skew_periphery"), 
            .u1_0_x0_xio_phase_adjust_xio_pa_feedback_gate_1_a_rbpa_feedback_gate                 ("feedback_gate_dly_0")  
            
/*
*   Untouched ND params
*            .hmc_dbc0_burst_length                    (`_get_hmc_burst_length),
*            .hmc_dbc1_burst_length                    (`_get_hmc_burst_length),
*            .hmc_dbc2_burst_length                    (`_get_hmc_burst_length),
*            .hmc_dbc3_burst_length                    (`_get_hmc_burst_length),
*            .hmc_wr_odt_on                            (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_WR_ODT_ON                , SEC_HMC_CFG_WR_ODT_ON                     )),  // Indicates number of memory clock cycle gap between write command and ODT signal rising edge
*            .silicon_rev                              (SILICON_REV),
*            .hps_ctrl_en                              (IS_HPS ? "hps_ctrl_en" : "hps_ctrl_dis"),
*            .pa_exponent_0                            (`_get_pa_exponent_0),                               // Output clock freq = VCO Freq / 2^exponent
*            .pa_exponent_1                            (`_get_pa_exponent_1),                               // Output clock freq = VCO Freq / 2^exponent
*            .pa_feedback_divider_c0                   (`_get_pa_feedback_divider_c0),                      // Core clock 0 divider (either 1 or 2)
*            .pa_feedback_divider_c1                   ("div_by_1"),                                        // Core clock 1 divider (always 1)
*            .pa_feedback_divider_p0                   (`_get_pa_feedback_divider_p0),                      // PHY clock 0 divider (either 1 or 2)
*            .pa_feedback_divider_p1                   ("div_by_1"),                                        // PHY clock 1 divider (always 1)
*            .pa_feedback_mux_sel_0                    ("fb2_p_clk"),                                       // Use phy_clk[2] as feedback
*            .pa_feedback_mux_sel_1                    (DIAG_CPA_OUT_1_EN ? "fb0_p_clk" : "fb2_p_clk"),     // Use phy_clk[2] as feedback, unless in dual-CPA characterization mode
*            .pa_freq_track_speed                      (4'hd),
*            .pa_track_speed                           (`_get_pa_track_speed),
*            .pa_sync_control                          ("no_sync"),
*            .pa_sync_latency                          (4'b0000),
*            .pa_coreclk_override                      ("non_override"),                                    // Override mechanism to use test clock as input
*            .pa_couple_enable                         ("couple_en"),
*            .pa_hps_clk_en                            (IS_HPS ? "fb_clk_hps" : "fb_clk_core"),             // HPS or not?
*            .physeq_bc_id_ena                         ("bc_enable"),                                       // Enable broadcast mechanism
*            .physeq_seq_feature                       (21'b000000000000000000000),
*            .hmc_ac_pos                               (AC_PIN_MAP_SCHEME),
*            .hmc_ctrl_output_regd                     ("disable"),                       // Engineering option. Unused.
*            .hmc_dbc0_output_regd                     ("disable"),                       // Engineering option. Unused.
*            .hmc_dbc1_output_regd                     ("disable"),                       // Engineering option. Unused.
*            .hmc_dbc2_output_regd                     ("disable"),                       // Engineering option. Unused.
*            .hmc_dbc3_output_regd                     ("disable"),                       // Engineering option. Unused.
*            .hmc_ctrl_dualport_en                     ("disable"),                       // No dual-port mode support
*            .hmc_dbc0_dualport_en                     ("disable"),                       // No dual-port mode support
*            .hmc_dbc1_dualport_en                     ("disable"),                       // No dual-port mode support
*            .hmc_dbc2_dualport_en                     ("disable"),                       // No dual-port mode support
*            .hmc_dbc3_dualport_en                     ("disable"),                       // No dual-port mode support
*            .hmc_avl_scg_en                           ("disable"),                       // Static clock gating
*            .hmc_dbc_sw_scg_en                        ("disable"),                       // Static clock gating
*            .hmc_core_scg_en                          ("disable"),                       // Static clock gating
*            .hmc_dbg_scg_en                           ("disable"),                       // Static clock gating
*            .hmc_scg_en                               ("disable"),                       // Static clock gating
*            .hmc_mmr_scg_en                           ("disable"),                       // Static clock gating
*            .hmc_pipe_scg_en                          ("disable"),                       // Static clock gating
*            .hmc_seq_scg_en                           ("disable"),                       // Static clock gating
*            
*            .cfg_cb_3ds_mixed_height_ref_ack_disable  ("disable"),                       // Set to 0 (same as "disable") to enable fix (case:384958)
*            .cfg_cb_3ds_mixed_height_req_fix          ("disable"),                       // Set to 0 (same as "disable") to enable fix (case:384958)
*            .hmc_cb_seq_en_fix_en_n                   ("enable"),                        // Set to 0 (same as "enable") to enable fix  (case:384958)
*            .cfg_cb_memclk_gate_default               ("disable"),                       // Set to 0 (same as "disable") to enable fix (case:384958)
*            .cfg_cb_en_cmd_valid_ungate_fix           ("enable"),                        // Set to 1 (same as "enable") to enable fix  (case:384958)
*            .cfg_cb_en_mrnk_rd_fix                    ("enable"),                        // Set to 1 (same as "enable") to enable fix  (case:384958)
*            .cfg_cb_pdqs_perf_fix_disable             ("disable"),                       // Set to 0 (same as "disable") to enable fix (case:384958)
*
*            
*            .hmc_arbiter_type                 (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_ARBITER_TYPE             , SEC_HMC_CFG_ARBITER_TYPE                  )),  // Arbiter Type
*            .hmc_open_page_en                 (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_OPEN_PAGE_EN             , SEC_HMC_CFG_OPEN_PAGE_EN                  )),  // Unused
*            .hmc_ctrl_slot_rotate_en          (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_CTRL_SLOT_ROTATE_EN      , SEC_HMC_CFG_CTRL_SLOT_ROTATE_EN           )),  // Command slot rotation
*            .hmc_cmd_fifo_reserve_en          (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_CMD_FIFO_RESERVE_EN      , SEC_HMC_CFG_CMD_FIFO_RESERVE_EN           )),  // Command FIFO reserve enable
*            .hmc_memclkgate_setting           (`_sel_hmc_tile(tile_i, PRI_HMC_MEMCLKGATE_SETTING           , SEC_HMC_MEMCLKGATE_SETTING                )),
*            .hmc_16_act_to_act                (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_16_ACT_TO_ACT            , SEC_HMC_CFG_16_ACT_TO_ACT                 )),  // The 16-activate window timing parameter (RLD3) (e.g. tSAW)
*            .hmc_rld3_multibank_ref_delay     (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_RLD3_MULTIBANK_REF_DELAY , SEC_HMC_CFG_RLD3_MULTIBANK_REF_DELAY      )),  // RLD3 multi-bank ref delay
*            .hmc_rld3_refresh_seq0            (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_RLD3_REFRESH_SEQ0        , SEC_HMC_CFG_RLD3_REFRESH_SEQ0             )),  // Banks to refresh for RLD3 in sequence 0. Must not be more than 4 banks
*            .hmc_rld3_refresh_seq1            (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_RLD3_REFRESH_SEQ1        , SEC_HMC_CFG_RLD3_REFRESH_SEQ1             )),  // Banks to refresh for RLD3 in sequence 1. Must not be more than 4 banks
*            .hmc_rld3_refresh_seq2            (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_RLD3_REFRESH_SEQ2        , SEC_HMC_CFG_RLD3_REFRESH_SEQ2             )),  // Banks to refresh for RLD3 in sequence 2. Must not be more than 4 banks
*            .hmc_rld3_refresh_seq3            (`_sel_hmc_tile(tile_i, PRI_HMC_CFG_RLD3_REFRESH_SEQ3        , SEC_HMC_CFG_RLD3_REFRESH_SEQ3             )),  // Banks to refresh for RLD3 in sequence 3. Must not be more than 4 banks
*            .mode                             ("tile_ddr")
*/
         ) tile_ctrl_inst (
            // Reset
            .global_reset_n                   (DIAG_USE_ABSTRACT_PHY == 1 ? (~core2seq_reset_req) : 1'b1),

            // PLL -> Tiles
            .pll_locked_in                    (pll_locked),
            .pll_vco_in                       (phy_clk_phs),                        // FR clocks routed on PHY clock tree
            .phy_clk_in                       (phy_clk_hmc),                        // PHY clock tree inputs

            // Clock Phase Alignment
            .pa_core_clk_in                   ({1'b0,all_tiles_core_clks_fb_in[tile_i][0]}),  // Input to CPA through feedback path
            .pa_core_clk_out                  (all_tiles_core_clks_out[tile_i]),    // Output from CPA to core clock networks
            .pa_locked                        (all_tiles_core_clks_locked[tile_i]), // Lock signal from CPA to core
            .pa_reset_n                       (DIAG_USE_ABSTRACT_PHY == 1 ? (~core2seq_reset_req) : 1'b1),       // Connected to global reset from core in non-HPS mode
            .pa_core_in                       (12'b000000000000),                   // Control code word

            // ND_2_FM delta => PA feedback port expanded to 3 bits
            .pa_fbclk_in                      (phy_fbclk_pa),                       // PLL signal going into PHY feedback clock

            .pa_sync_data_bot_in              (pa_sync_data_up_chain[`_get_chain_index_for_tile(tile_i)]),
            .pa_sync_data_top_out             (pa_sync_data_up_chain[`_get_chain_index_for_tile(tile_i) + 1]),
            .pa_sync_data_top_in              (pa_sync_data_dn_chain[`_get_chain_index_for_tile(tile_i) + 1]),
            .pa_sync_data_bot_out             (pa_sync_data_dn_chain[`_get_chain_index_for_tile(tile_i)]),
            .pa_sync_clk_bot_in               (pa_sync_clk_up_chain [`_get_chain_index_for_tile(tile_i)]),
            .pa_sync_clk_top_out              (pa_sync_clk_up_chain [`_get_chain_index_for_tile(tile_i) + 1]),
            .pa_sync_clk_top_in               (pa_sync_clk_dn_chain [`_get_chain_index_for_tile(tile_i) + 1]),
            .pa_sync_clk_bot_out              (pa_sync_clk_dn_chain [`_get_chain_index_for_tile(tile_i)]),
            .pa_dprio_rst_n                   ((tile_i == PRI_AC_TILE_INDEX ? pa_dprio_rst_n : 1'b0)),
            .pa_dprio_clk                     ((tile_i == PRI_AC_TILE_INDEX ? pa_dprio_clk : 1'b0)),
            .pa_dprio_read                    ((tile_i == PRI_AC_TILE_INDEX ? pa_dprio_read : 1'b0)),
            .pa_dprio_reg_addr                ((tile_i == PRI_AC_TILE_INDEX ? pa_dprio_reg_addr : 9'b0)),
            .pa_dprio_write                   ((tile_i == PRI_AC_TILE_INDEX ? pa_dprio_write : 1'b0)),
            .pa_dprio_writedata               ((tile_i == PRI_AC_TILE_INDEX ? pa_dprio_writedata : 8'b0)),
            .pa_dprio_block_select            (all_tiles_pa_dprio_block_select[tile_i]),
            .pa_dprio_readdata                (all_tiles_pa_dprio_readdata[tile_i]),

            // PHY clock signals going from tiles to lanes
            .phy_clk_phs_out0                 (all_tiles_t2l_phy_clk_phs[tile_i][0]), // PHY vco clocks to lane 0
            .phy_clk_phs_out1                 (all_tiles_t2l_phy_clk_phs[tile_i][1]), // PHY vco clocks to lane 1
            .phy_clk_phs_out2                 (all_tiles_t2l_phy_clk_phs[tile_i][2]), // PHY vco clocks to lane 2
            .phy_clk_phs_out3                 (all_tiles_t2l_phy_clk_phs[tile_i][3]), // PHY vco clocks to lane 3
 
            // DLL Interface
            .dll_clk_in                       (pll_dll_clk),                       // PLL clock feeding to DLL
            .dll_clk_out0                     (all_tiles_dll_clk_out[tile_i][0]),  // DLL clock to lane 0
            .dll_clk_out1                     (all_tiles_dll_clk_out[tile_i][1]),  // DLL clock to lane 1
            .dll_clk_out2                     (all_tiles_dll_clk_out[tile_i][2]),  // DLL clock to lane 2
            .dll_clk_out3                     (all_tiles_dll_clk_out[tile_i][3]),  // DLL clock to lane 3

            // Calibration bus between Nios and sequencer (a.k.a slow Avalon-MM bus)
            .param_table_data                 (tile_param_tables[tile_i]),
            .cal_avl_in                       (cal_bus_avl_up_chain          [`_get_chain_index_for_tile(tile_i)]),
            .cal_avl_out                      (cal_bus_avl_up_chain          [`_get_chain_index_for_tile(tile_i) + 1]),
            .cal_avl_rdata_in                 (cal_bus_avl_read_data_dn_chain[`_get_chain_index_for_tile(tile_i) + 1]),
            .cal_avl_rdata_out                (cal_bus_avl_read_data_dn_chain[`_get_chain_index_for_tile(tile_i)]),

            .core2ctl_avl                     ((tile_i == PRI_AC_TILE_INDEX) ? core2ctl_avl_0 : ((tile_i == SEC_AC_TILE_INDEX ) ? core2ctl_avl_1 : 63'd0)),
            .core2ctl_avl_rd_data_ready       ((tile_i == PRI_AC_TILE_INDEX) ? core2ctl_avl_rd_data_ready_0 : ((tile_i == SEC_AC_TILE_INDEX ) ? core2ctl_avl_rd_data_ready_1 : 1'b0)),
            .ctl2core_avl_cmd_ready           (all_tiles_ctl2core_avl_cmd_ready[tile_i]),
            .ctl2core_avl_rdata_id            (all_tiles_ctl2core_avl_rdata_id[tile_i]),

            .core2ctl_sideband                ((tile_i == PRI_AC_TILE_INDEX) ? core2ctl_sideband_0 : ((tile_i == SEC_AC_TILE_INDEX ) ? core2ctl_sideband_1 : 42'd0)),
            .ctl2core_sideband                (all_tiles_ctl2core_sideband[tile_i]),

            // Interface between HMC and lanes
            .afi_cmd_bus                      (t2l_ac_hmc),

            // DQS buses
            // There are 8 x4 DQS buses per tile, with two pairs of input DQS per lane.
            .dqs_in_x4_a_0                    (DQS_BUS_MODE_ENUM == "DQS_BUS_MODE_X4" ? b2t_dqs[(tile_i * LANES_PER_TILE) + 0]  : 1'b0),
            .dqs_in_x4_a_1                    (DQS_BUS_MODE_ENUM == "DQS_BUS_MODE_X4" ? b2t_dqs[(tile_i * LANES_PER_TILE) + 1]  : 1'b0),
            .dqs_in_x4_a_2                    (DQS_BUS_MODE_ENUM == "DQS_BUS_MODE_X4" ? b2t_dqs[(tile_i * LANES_PER_TILE) + 2]  : 1'b0),
            .dqs_in_x4_a_3                    (DQS_BUS_MODE_ENUM == "DQS_BUS_MODE_X4" ? b2t_dqs[(tile_i * LANES_PER_TILE) + 3]  : 1'b0),
            .dqs_in_x4_b_0                    (DQS_BUS_MODE_ENUM == "DQS_BUS_MODE_X4" ? b2t_dqsb[(tile_i * LANES_PER_TILE) + 0] : 1'b0),
            .dqs_in_x4_b_1                    (DQS_BUS_MODE_ENUM == "DQS_BUS_MODE_X4" ? b2t_dqsb[(tile_i * LANES_PER_TILE) + 1] : 1'b0),
            .dqs_in_x4_b_2                    (DQS_BUS_MODE_ENUM == "DQS_BUS_MODE_X4" ? b2t_dqsb[(tile_i * LANES_PER_TILE) + 2] : 1'b0),
            .dqs_in_x4_b_3                    (DQS_BUS_MODE_ENUM == "DQS_BUS_MODE_X4" ? b2t_dqsb[(tile_i * LANES_PER_TILE) + 3] : 1'b0),
            .dqs_out_x4_a_lane0               (t2l_dqsbus_x4[0][0]),
            .dqs_out_x4_b_lane0               (t2l_dqsbus_x4[0][1]),
            .dqs_out_x4_a_lane1               (t2l_dqsbus_x4[1][0]),
            .dqs_out_x4_b_lane1               (t2l_dqsbus_x4[1][1]),
            .dqs_out_x4_a_lane2               (t2l_dqsbus_x4[2][0]),
            .dqs_out_x4_b_lane2               (t2l_dqsbus_x4[2][1]),
            .dqs_out_x4_a_lane3               (t2l_dqsbus_x4[3][0]),
            .dqs_out_x4_b_lane3               (t2l_dqsbus_x4[3][1]),

            // There are 4 x8/x9 DQS buses per tile, with one pair of input DQS per lane.
            .dqs_in_x8_0                      ((DQS_BUS_MODE_ENUM == "DQS_BUS_MODE_X8_X9" || DQS_BUS_MODE_ENUM == "DQS_BUS_MODE_X9_DINV")? {b2t_dqsb[(tile_i * LANES_PER_TILE) + 0], b2t_dqs[(tile_i * LANES_PER_TILE) + 0]} : 2'b0),
            .dqs_in_x8_1                      ((DQS_BUS_MODE_ENUM == "DQS_BUS_MODE_X8_X9" || DQS_BUS_MODE_ENUM == "DQS_BUS_MODE_X9_DINV")? {b2t_dqsb[(tile_i * LANES_PER_TILE) + 1], b2t_dqs[(tile_i * LANES_PER_TILE) + 1]} : 2'b0),
            .dqs_in_x8_2                      ((DQS_BUS_MODE_ENUM == "DQS_BUS_MODE_X8_X9" || DQS_BUS_MODE_ENUM == "DQS_BUS_MODE_X9_DINV")? {b2t_dqsb[(tile_i * LANES_PER_TILE) + 2], b2t_dqs[(tile_i * LANES_PER_TILE) + 2]} : 2'b0),
            .dqs_in_x8_3                      ((DQS_BUS_MODE_ENUM == "DQS_BUS_MODE_X8_X9" || DQS_BUS_MODE_ENUM == "DQS_BUS_MODE_X9_DINV")? {b2t_dqsb[(tile_i * LANES_PER_TILE) + 3], b2t_dqs[(tile_i * LANES_PER_TILE) + 3]} : 2'b0),
            .dqs_out_x8_lane0                 (t2l_dqsbus_x8[0]),
            .dqs_out_x8_lane1                 (t2l_dqsbus_x8[1]),
            .dqs_out_x8_lane2                 (t2l_dqsbus_x8[2]),
            .dqs_out_x8_lane3                 (t2l_dqsbus_x8[3]),

            // There are 2 x16/x18 DQS buses per tile, and the input DQS must originate from lane 0 and 2 (Follow-on)
            .dqs_in_x18_0                     ((DQS_BUS_MODE_ENUM == "DQS_BUS_MODE_X16_X18" || DQS_BUS_MODE_ENUM == "DQS_BUS_MODE_X18_DINV")? {b2t_dqsb[(tile_i * LANES_PER_TILE) + 0], b2t_dqs[(tile_i * LANES_PER_TILE) + 0]} : 2'b0),
            .dqs_in_x18_1                     ((DQS_BUS_MODE_ENUM == "DQS_BUS_MODE_X16_X18" || DQS_BUS_MODE_ENUM == "DQS_BUS_MODE_X18_DINV")? {b2t_dqsb[(tile_i * LANES_PER_TILE) + 2], b2t_dqs[(tile_i * LANES_PER_TILE) + 2]} : 2'b0),
            .dqs_out_x18_lane0                (t2l_dqsbus_x18[0]),
            .dqs_out_x18_lane1                (t2l_dqsbus_x18[1]),
            .dqs_out_x18_lane2                (t2l_dqsbus_x18[2]),
            .dqs_out_x18_lane3                (t2l_dqsbus_x18[3]),

            // There is 1 x32/x36 DQS bus per tile, and the input DQS must originate from lane 1
            .dqs_in_x36                       (DQS_BUS_MODE_ENUM == "DQS_BUS_MODE_X32_X36" ? {b2t_dqsb[(tile_i * LANES_PER_TILE) + 1], b2t_dqs[(tile_i * LANES_PER_TILE) + 1]} : 2'b0),
            .dqs_out_x36_lane0                (t2l_dqsbus_x36[0]),
            .dqs_out_x36_lane1                (t2l_dqsbus_x36[1]),
            .dqs_out_x36_lane2                (t2l_dqsbus_x36[2]),
            .dqs_out_x36_lane3                (t2l_dqsbus_x36[3]),

            // Data buffer control signals
            .ctl2dbc0                         (all_tiles_ctl2dbc0_dn_chain[tile_i]),
            .ctl2dbc1                         (all_tiles_ctl2dbc1_up_chain[tile_i + 1]),
            .ctl2dbc_in_up                    (all_tiles_ctl2dbc0_dn_chain[tile_i + 1]),
            .ctl2dbc_in_down                  (all_tiles_ctl2dbc1_up_chain[tile_i]),
            .cfg_dbc0                         (t2l_cfg_dbc[0]),
            .cfg_dbc1                         (t2l_cfg_dbc[1]),
            .cfg_dbc2                         (t2l_cfg_dbc[2]),
            .cfg_dbc3                         (t2l_cfg_dbc[3]),

            // Ping-Pong PHY related signals
            .ping_pong_in                     (all_tiles_ping_pong_up_chain[tile_i]),
            .ping_pong_out                    (all_tiles_ping_pong_up_chain[tile_i + 1]),

            // MMR-related signals
            .mmr_in                           ((tile_i == PRI_AC_TILE_INDEX) ? core2ctl_mmr_0 : ((tile_i == SEC_AC_TILE_INDEX ) ? core2ctl_mmr_1 : 51'b0)),
            .mmr_out                          (all_tiles_ctl2core_mmr[tile_i]),

            // Miscellaneous signals
            .afi_core2ctl                     (all_tiles_c2t_afi[tile_i]),
            .afi_ctl2core                     (all_tiles_t2c_afi[tile_i]),
            .seq2core_reset_n                 (),
            .ctl_mem_clk_disable              (),
            .rdata_en_full_core               (4'b0),   
            .mrnk_read_core                   (16'b0),  
            .test_dbg_in                      (48'b000000000000000000000000000000000000000000000000),
            .test_dbg_out                     ()        
         );
         

         for (lane_i = 0; lane_i < LANES_PER_TILE; ++lane_i)
         begin: lane_gen
            (* altera_attribute = "-name MAX_WIRES_FOR_CORE_PERIPHERY_TRANSFER 1; -name MAX_WIRES_FOR_PERIPHERY_CORE_TRANSFER 1" *)
            altera_emif_arch_fm_io_lane_remap #(
               .memory_standard                             (`_get_memory_standard),
               .memory_controller                           (`_get_hmc_or_smc),
               .mode_rate_in                                (`_get_lane_mode_rate_in),
               .mode_rate_out                               (`_get_lane_mode_rate_out),
               .memory_burst_length                         (`_get_memory_burst_length),
               .memory_width                                (`_get_dqs_group_width),

               .clock_period_ps                             ((`_get_lane_usage(tile_i, lane_i) == LANE_USAGE_UNUSED) ? 16'd0 : PLL_MEM_CLK_FREQ_PS),                  
               .phy_clk_sel                                 (0),                          
               .calibration                                 ("run"),                     
               .lock_speed                                  (3'h7),                       

               .db_dbc_ctrl_rc_en_scalar                    ((PRI_HMC_CFG_CTRL_ENABLE_RC == "enable") ? "dbc_rc_scalar_enable" : "dbc_rc_scalar_disable"),
               .db_avl_base_addr                            (`_get_lane_tid(tile_i, lane_i)),
               .db_avl_broadcast_en                         ("bc_enable"),
               .db_avl_ena                                  ("avl_enable"),                     
               .dqs_select_a                                (DQSA_LGC_MODE),
               .dqs_select_b                                (DQSB_LGC_MODE),

               .lane_ddr_mode                               (`_get_lane_ddr_mode_str(tile_i, lane_i)),

               .lane_pin0_ddr_mode                          (`_get_lane_pin_ddr_mode_str(tile_i, lane_i, 0) ),
               .lane_pin1_ddr_mode                          (`_get_lane_pin_ddr_mode_str(tile_i, lane_i, 1) ),
               .lane_pin2_ddr_mode                          (`_get_lane_pin_ddr_mode_str(tile_i, lane_i, 2) ),
               .lane_pin3_ddr_mode                          (`_get_lane_pin_ddr_mode_str(tile_i, lane_i, 3) ),
               .lane_pin4_ddr_mode                          (`_get_lane_pin_ddr_mode_str(tile_i, lane_i, 4) ),
               .lane_pin5_ddr_mode                          (`_get_lane_pin_ddr_mode_str(tile_i, lane_i, 5) ),
               .lane_pin6_ddr_mode                          (`_get_lane_pin_ddr_mode_str(tile_i, lane_i, 6) ),
               .lane_pin7_ddr_mode                          (`_get_lane_pin_ddr_mode_str(tile_i, lane_i, 7) ),
               .lane_pin8_ddr_mode                          (`_get_lane_pin_ddr_mode_str(tile_i, lane_i, 8) ),
               .lane_pin9_ddr_mode                          (`_get_lane_pin_ddr_mode_str(tile_i, lane_i, 9) ),
               .lane_pin10_ddr_mode                         (`_get_lane_pin_ddr_mode_str(tile_i, lane_i, 10)),
               .lane_pin11_ddr_mode                         (`_get_lane_pin_ddr_mode_str(tile_i, lane_i, 11)),

               .lane_mode                                   ((`_get_lane_usage(tile_i, lane_i) == LANE_USAGE_UNUSED) ? "lane_unused" : "lane_ddr"),
               .lane_pin0_mode                              (`_get_lane_pin_mode_str(tile_i, lane_i, 0) ),
               .lane_pin1_mode                              (`_get_lane_pin_mode_str(tile_i, lane_i, 1) ),
               .lane_pin2_mode                              (`_get_lane_pin_mode_str(tile_i, lane_i, 2) ),
               .lane_pin3_mode                              (`_get_lane_pin_mode_str(tile_i, lane_i, 3) ),
               .lane_pin4_mode                              (`_get_lane_pin_mode_str(tile_i, lane_i, 4) ),
               .lane_pin5_mode                              (`_get_lane_pin_mode_str(tile_i, lane_i, 5) ),
               .lane_pin6_mode                              (`_get_lane_pin_mode_str(tile_i, lane_i, 6) ),
               .lane_pin7_mode                              (`_get_lane_pin_mode_str(tile_i, lane_i, 7) ),
               .lane_pin8_mode                              (`_get_lane_pin_mode_str(tile_i, lane_i, 8) ),
               .lane_pin9_mode                              (`_get_lane_pin_mode_str(tile_i, lane_i, 9) ),
               .lane_pin10_mode                             (`_get_lane_pin_mode_str(tile_i, lane_i, 10)),
               .lane_pin11_mode                             (`_get_lane_pin_mode_str(tile_i, lane_i, 11)),


               .db_hmc_or_core                              (`_get_hmc_or_core),
               .db_db2core_registered                       ("registered"),
               .db_preamble_mode                            (PREAMBLE_MODE),
               .db_data_alignment_mode                      (`_get_db_data_alignment_mode),                      // Data alignment mode (enabled IFF HMC)

               .db_pin0_mode                                (`_get_db_pin_proc_mode_str(tile_i, lane_i, 0) ),
               .db_pin1_mode                                (`_get_db_pin_proc_mode_str(tile_i, lane_i, 1) ),
               .db_pin2_mode                                (`_get_db_pin_proc_mode_str(tile_i, lane_i, 2) ),
               .db_pin3_mode                                (`_get_db_pin_proc_mode_str(tile_i, lane_i, 3) ),
               .db_pin4_mode                                (`_get_db_pin_proc_mode_str(tile_i, lane_i, 4) ),
               .db_pin5_mode                                (`_get_db_pin_proc_mode_str(tile_i, lane_i, 5) ),
               .db_pin6_mode                                (`_get_db_pin_proc_mode_str(tile_i, lane_i, 6) ),
               .db_pin7_mode                                (`_get_db_pin_proc_mode_str(tile_i, lane_i, 7) ),
               .db_pin8_mode                                (`_get_db_pin_proc_mode_str(tile_i, lane_i, 8) ),
               .db_pin9_mode                                (`_get_db_pin_proc_mode_str(tile_i, lane_i, 9) ),
               .db_pin10_mode                               (`_get_db_pin_proc_mode_str(tile_i, lane_i, 10)),
               .db_pin11_mode                               (`_get_db_pin_proc_mode_str(tile_i, lane_i, 11)),

               .pin0_oct_rt                                 (`_get_pin_oct_rt_str(tile_i, lane_i, 0) ),
               .pin1_oct_rt                                 (`_get_pin_oct_rt_str(tile_i, lane_i, 1) ),
               .pin2_oct_rt                                 (`_get_pin_oct_rt_str(tile_i, lane_i, 2) ),
               .pin3_oct_rt                                 (`_get_pin_oct_rt_str(tile_i, lane_i, 3) ),
               .pin4_oct_rt                                 (`_get_pin_oct_rt_str(tile_i, lane_i, 4) ),
               .pin5_oct_rt                                 (`_get_pin_oct_rt_str(tile_i, lane_i, 5) ),
               .pin6_oct_rt                                 (`_get_pin_oct_rt_str(tile_i, lane_i, 6) ),
               .pin7_oct_rt                                 (`_get_pin_oct_rt_str(tile_i, lane_i, 7) ),
               .pin8_oct_rt                                 (`_get_pin_oct_rt_str(tile_i, lane_i, 8) ),
               .pin9_oct_rt                                 (`_get_pin_oct_rt_str(tile_i, lane_i, 9) ),
               .pin10_oct_rt                                (`_get_pin_oct_rt_str(tile_i, lane_i, 10)),
               .pin11_oct_rt                                (`_get_pin_oct_rt_str(tile_i, lane_i, 11)),

               .pin0_dyn_oct                                (`_get_pin_dyn_oct_str(tile_i, lane_i, 0) ),
               .pin1_dyn_oct                                (`_get_pin_dyn_oct_str(tile_i, lane_i, 1) ),
               .pin2_dyn_oct                                (`_get_pin_dyn_oct_str(tile_i, lane_i, 2) ),
               .pin3_dyn_oct                                (`_get_pin_dyn_oct_str(tile_i, lane_i, 3) ),
               .pin4_dyn_oct                                (`_get_pin_dyn_oct_str(tile_i, lane_i, 4) ),
               .pin5_dyn_oct                                (`_get_pin_dyn_oct_str(tile_i, lane_i, 5) ),
               .pin6_dyn_oct                                (`_get_pin_dyn_oct_str(tile_i, lane_i, 6) ),
               .pin7_dyn_oct                                (`_get_pin_dyn_oct_str(tile_i, lane_i, 7) ),
               .pin8_dyn_oct                                (`_get_pin_dyn_oct_str(tile_i, lane_i, 8) ),
               .pin9_dyn_oct                                (`_get_pin_dyn_oct_str(tile_i, lane_i, 9) ),
               .pin10_dyn_oct                               (`_get_pin_dyn_oct_str(tile_i, lane_i, 10)),
               .pin11_dyn_oct                               (`_get_pin_dyn_oct_str(tile_i, lane_i, 11)),

               .pin0_initial_out                            ("initial_out_z"),
               .pin1_initial_out                            ("initial_out_z"),
               .pin2_initial_out                            ("initial_out_z"),
               .pin3_initial_out                            ("initial_out_z"),
               .pin4_initial_out                            ("initial_out_z"),
               .pin5_initial_out                            ("initial_out_z"),
               .pin6_initial_out                            ("initial_out_z"),
               .pin7_initial_out                            ("initial_out_z"),
               .pin8_initial_out                            ("initial_out_z"),
               .pin9_initial_out                            ("initial_out_z"),
               .pin10_initial_out                           ("initial_out_z"),
               .pin11_initial_out                           ("initial_out_z"),

               .pin0_mode_ddr                               (`_get_pin_ddr_str(tile_i, lane_i, 0) ),
               .pin1_mode_ddr                               (`_get_pin_ddr_str(tile_i, lane_i, 1) ),
               .pin2_mode_ddr                               (`_get_pin_ddr_str(tile_i, lane_i, 2) ),
               .pin3_mode_ddr                               (`_get_pin_ddr_str(tile_i, lane_i, 3) ),
               .pin4_mode_ddr                               (`_get_pin_ddr_str(tile_i, lane_i, 4) ),
               .pin5_mode_ddr                               (`_get_pin_ddr_str(tile_i, lane_i, 5) ),
               .pin6_mode_ddr                               (`_get_pin_ddr_str(tile_i, lane_i, 6) ),
               .pin7_mode_ddr                               (`_get_pin_ddr_str(tile_i, lane_i, 7) ),
               .pin8_mode_ddr                               (`_get_pin_ddr_str(tile_i, lane_i, 8) ),
               .pin9_mode_ddr                               (`_get_pin_ddr_str(tile_i, lane_i, 9) ),
               .pin10_mode_ddr                              (`_get_pin_ddr_str(tile_i, lane_i, 10)),
               .pin11_mode_ddr                              (`_get_pin_ddr_str(tile_i, lane_i, 11)),

               .pin0_dqs_mode                               (`_get_pin_dqs_mode_str(tile_i, lane_i, 0) ),
               .pin1_dqs_mode                               (`_get_pin_dqs_mode_str(tile_i, lane_i, 1) ),
               .pin2_dqs_mode                               (`_get_pin_dqs_mode_str(tile_i, lane_i, 2) ),
               .pin3_dqs_mode                               (`_get_pin_dqs_mode_str(tile_i, lane_i, 3) ),
               .pin4_dqs_mode                               (`_get_pin_dqs_mode_str(tile_i, lane_i, 4) ),
               .pin5_dqs_mode                               (`_get_pin_dqs_mode_str(tile_i, lane_i, 5) ),
               .pin6_dqs_mode                               (`_get_pin_dqs_mode_str(tile_i, lane_i, 6) ),
               .pin7_dqs_mode                               (`_get_pin_dqs_mode_str(tile_i, lane_i, 7) ),
               .pin8_dqs_mode                               (`_get_pin_dqs_mode_str(tile_i, lane_i, 8) ),
               .pin9_dqs_mode                               (`_get_pin_dqs_mode_str(tile_i, lane_i, 9) ),
               .pin10_dqs_mode                              (`_get_pin_dqs_mode_str(tile_i, lane_i, 10)),
               .pin11_dqs_mode                              (`_get_pin_dqs_mode_str(tile_i, lane_i, 11)),

               .pin0_data_in_mode                           (`_get_pin_data_in_mode_str(tile_i, lane_i, 0) ),
               .pin1_data_in_mode                           (`_get_pin_data_in_mode_str(tile_i, lane_i, 1) ),
               .pin2_data_in_mode                           (`_get_pin_data_in_mode_str(tile_i, lane_i, 2) ),
               .pin3_data_in_mode                           (`_get_pin_data_in_mode_str(tile_i, lane_i, 3) ),
               .pin4_data_in_mode                           (`_get_pin_data_in_mode_str(tile_i, lane_i, 4) ),
               .pin5_data_in_mode                           (`_get_pin_data_in_mode_str(tile_i, lane_i, 5) ),
               .pin6_data_in_mode                           (`_get_pin_data_in_mode_str(tile_i, lane_i, 6) ),
               .pin7_data_in_mode                           (`_get_pin_data_in_mode_str(tile_i, lane_i, 7) ),
               .pin8_data_in_mode                           (`_get_pin_data_in_mode_str(tile_i, lane_i, 8) ),
               .pin9_data_in_mode                           (`_get_pin_data_in_mode_str(tile_i, lane_i, 9) ),
               .pin10_data_in_mode                          (`_get_pin_data_in_mode_str(tile_i, lane_i, 10)),
               .pin11_data_in_mode                          (`_get_pin_data_in_mode_str(tile_i, lane_i, 11)),

               .db_afi_rlat_vlu                             (6'b000000),                                            // Unused - rlat set dynamically via Avalon by Nios
               .db_afi_wlat_vlu                             (6'b000000),                                            // Unused - wlat set dynamically via Avalon by Nios

               // Use phy_clk1 if HMC dual-port or rate-converter is used, use phy_clk0 otherwise
               .db_sel_core_clk                             ((`_get_lane_usage(tile_i, lane_i) == LANE_USAGE_UNUSED) ? "core_clk_disable" : LANE_DB_CLK_SEL ),
               .db_dbi_wr_en                                (`_get_dbi_wr_en(tile_i, lane_i)),
               .db_dbi_rd_en                                (`_get_dbi_rd_en(tile_i, lane_i)),
               .db_dbi_sel                                  ("dbi_dq6"),                                             
               .db_ptr_pipeline_depth                       (`_get_db_ptr_pipe_depth_str(tile_i, lane_i)),           // Additional latency to compensate for distance from HMC
               .db_seq_rd_en_full_pipeline                  (`_get_db_seq_rd_en_full_pipeline_str(tile_i, lane_i)),  // Additional latency to compensate for distance from sequencer
               .db_mrnk_write_mode                          (`_get_mrnk_write_mode(tile_i, lane_i)),
               .dbc_wb_reserved_entry                       (DBC_WB_RESERVED_ENTRY[4:0]),
               .db_dbc_rb_readylat_en                       (DBC_WB_RESERVED_ENTRY[6] ? "dbc_rb_readylat_enable" : "dbc_rb_readylat_disable"),
               .db_dbc_wb_readylat_en                       (DBC_WB_RESERVED_ENTRY[5] ? "dbc_wb_readylat_enable" : "dbc_wb_readylat_disable"),
               .oct_size                                    (`_get_oct_size),
               .rd_valid_delay                              (7'b0000000),                           // Don't-care - always set by calibration software
               .dqs_enable_delay                            (6'b000000),                            // Don't-care - always set by calibration software
               .dqs_phase_shift_b                           (13'b00000_0000_0000),                  // Delay to read clock/strobe gating signal. Overriden by Nios during calibration.
               .dqs_phase_shift_a                           (13'b00000_0000_0000),                  // Delay to read clock/strobe gating signal. Overriden by Nios during calibration.
               .dll_rst_en                                  (IS_HPS ? "dll_rst_dis" : "dll_rst_en"),
               .dll_core_updnen                             ("dll_core_updn_dis"),
               .dll_ctlsel                                  (DLL_MODE),
               .dll_ctl_static                              (DLL_CODEWORD),
               .enable_toggler                              (`_get_preamble_track_dqs_enable_mode) // Tracking Mode
            ) lane_inst (

               // PLL/DLL/PVT interface
               .pll_locked                               (pll_locked),
               .dll_ref_clk                              (all_tiles_dll_clk_out[tile_i][lane_i]),
               .core_dll                                 (3'b100),    
               .dll_core                                 (),          
               .ioereg_locked                            (),

               // Clocks
               .phy_clk                                  (all_tiles_t2l_phy_clk[lane_i][1:0]),
               .phy_clk_phs                              (all_tiles_t2l_phy_clk_phs[tile_i][lane_i]),
               .phy_clk_local_early                      (phy_clk_local_early[lane_i]),
               .phy_clk_local_late                       (phy_clk_local_late[lane_i]),

               // Clock Phase Alignment
               .sync_data_bot_in                         (pa_sync_data_up_chain[`_get_chain_index_for_lane(tile_i, lane_i)]),
               .sync_data_top_out                        (pa_sync_data_up_chain[`_get_chain_index_for_lane(tile_i, lane_i) + 1]),
               .sync_data_top_in                         (pa_sync_data_dn_chain[`_get_chain_index_for_lane(tile_i, lane_i) + 1]),
               .sync_data_bot_out                        (pa_sync_data_dn_chain[`_get_chain_index_for_lane(tile_i, lane_i)]),
               .sync_clk_bot_in                          (pa_sync_clk_up_chain [`_get_chain_index_for_lane(tile_i, lane_i)]),
               .sync_clk_top_out                         (pa_sync_clk_up_chain [`_get_chain_index_for_lane(tile_i, lane_i) + 1]),
               .sync_clk_top_in                          (pa_sync_clk_dn_chain [`_get_chain_index_for_lane(tile_i, lane_i) + 1]),
               .sync_clk_bot_out                         (pa_sync_clk_dn_chain [`_get_chain_index_for_lane(tile_i, lane_i)]),

               // DQS bus from tile. Connections are only made for the data lanes (as captured by the macro)
               .dqs_in                                   (`_get_dqsin(tile_i, lane_i)),

               // Interface to I/O bufers
               .oct_enable                               (l2b_dtc_nonabphy [tile_i * PINS_PER_LANE * LANES_PER_TILE + lane_i * PINS_PER_LANE +: PINS_PER_LANE]),
               .data_oe                                  (l2b_oe_nonabphy  [tile_i * PINS_PER_LANE * LANES_PER_TILE + lane_i * PINS_PER_LANE +: PINS_PER_LANE]),
               .data_in                                  (b2l_data[tile_i * PINS_PER_LANE * LANES_PER_TILE + lane_i * PINS_PER_LANE +: PINS_PER_LANE]),
               .data_out                                 (l2b_data_nonabphy[tile_i * PINS_PER_LANE * LANES_PER_TILE + lane_i * PINS_PER_LANE +: PINS_PER_LANE]),

               // Interface to core
               .data_from_core                           (core2l_data[tile_i][lane_i]),
               .data_to_core                             (l2core_data_nonabphy[tile_i][lane_i]),

               // core2l_oe is inverted before feeding into the lane because
               // oe_invert is always set to true as required by HMC and sequencer
               .oe_from_core                             (core2l_oe[tile_i][lane_i]),
               .rdata_en_full_core                       (core2l_rdata_en_full[tile_i][lane_i]),

               // mrnk_(read|write)
               .mrnk_read_core                           ((`_get_data_lane(tile_i,lane_i) == 1'b1 || PROTOCOL_ENUM == "PROTOCOL_QDR4" ) ? {8'd0, core2l_mrnk_read[tile_i][lane_i]} : 16'b0),
               .mrnk_write_core                          ((`_get_data_lane(tile_i,lane_i) == 1'b1 || PROTOCOL_ENUM == "PROTOCOL_QDR4" ) ? {8'd0, core2l_mrnk_write[tile_i][lane_i]} : 16'b0),

               .rdata_valid_core                         (l2vio_rdata_valid[tile_i][lane_i]),
               .afi_wlat_core                            (l2vio_afi_wlat[tile_i][lane_i]),
               .afi_rlat_core                            (l2vio_afi_rlat[tile_i][lane_i]),

               // ECC signals between core and lanes
               .dbc2core_rd_data_vld0                    (l2vio_rd_data_vld_avl[tile_i][lane_i]),
               .core2dbc_wr_data_vld0                    (`_get_core2dbc_wr_data_vld(tile_i, lane_i)),
               .dbc2core_wr_data_rdy                     (l2vio_wr_data_rdy_ast[tile_i][lane_i]),
               .core2dbc_rd_data_rdy                     (`_get_core2dbc_rd_data_rdy(tile_i, lane_i)),
               .dbc2core_wb_pointer                      (l2vio_wb_pointer_for_ecc[tile_i][lane_i]),
               .core2dbc_wr_ecc_info                     (`_get_core2dbc_wr_ecc_info(tile_i, lane_i)),
               .dbc2core_rd_type                         (l2vio_rd_type[tile_i][lane_i]),

               // Calibration bus between Nios and sequencer (a.k.a slow Avalon-MM bus)
               .reset_n                                  (DIAG_USE_ABSTRACT_PHY == 1 ? (~core2seq_reset_req) : 1'b1),
               .cal_avl_in                               (cal_bus_avl_up_chain          [`_get_chain_index_for_lane(tile_i, lane_i)]),
               .cal_avl_out                              (cal_bus_avl_up_chain          [`_get_chain_index_for_lane(tile_i, lane_i) + 1]),
               .cal_avl_readdata_in                      (cal_bus_avl_read_data_dn_chain[`_get_chain_index_for_lane(tile_i, lane_i) + 1]),
               .cal_avl_readdata_out                     (cal_bus_avl_read_data_dn_chain[`_get_chain_index_for_lane(tile_i, lane_i)]),

               // HMC interface
               .ac_hmc                                   (`_get_ac_hmc(tile_i, lane_i)),
               .ctl2dbc0                                 (all_tiles_ctl2dbc0_dn_chain[tile_i]),
               .ctl2dbc1                                 (all_tiles_ctl2dbc1_up_chain[tile_i + 1]),
               .cfg_dbc                                  (t2l_cfg_dbc[lane_i]),

               // Broadcast signals
               .broadcast_in_bot                         (broadcast_up_chain[`_get_broadcast_chain_index(tile_i, lane_i)]),
               .broadcast_out_top                        (broadcast_up_chain[`_get_broadcast_chain_index(tile_i, lane_i) + 1]),
               .broadcast_in_top                         (broadcast_dn_chain[`_get_broadcast_chain_index(tile_i, lane_i) + 1]),
               .broadcast_out_bot                        (broadcast_dn_chain[`_get_broadcast_chain_index(tile_i, lane_i)]),

               // Unused signals
               .dft_phy_clk                              (/*open*/)
            );

         end
      end
   endgenerate

endmodule
`ifdef QUESTA_INTEL_OEM
`pragma questa_oem_00 "EVeqkz9MvDzapiiVw7+udc++m43wu2P9R6Bkf/lfBn9ZttFzW71hzuu9P3yzPlvUUu1GESHEht8oUjkuxH5nYF5m2Y4yEaZOsor1W+qakklkcNM5gczDB8G/zUljAitcohcjlH9xX4F5r3RrLLQB1HrtXmnxKKrsVs2RsxKt4plRYJGUCxRjs6twKgr6lps1q22taZT7+7dZh7dYE0uKJfWB1PYeKR+rbOxvrAyMNm17Ies0Vsl/kcZ66hCa0cxXw4w0Fyjibd+1pmoa3KnGaTBErSNL1IdeYka0p/TnGQ4ny7EFj5kJWtiwMSWR77bb4RT4tneNfK8718tMGMCEFpnRfZt30Yov386tAL2EAtTvraGyRSnxswOaEM0Euq2RjTsYuUbDi3aIVMuM42NLmideJE3+qwxDbdlSsMKgL3mo3Gi0GC4+gK9WlKm83RIfmGU05QKXIW2H1WIAZGopr4HOg7vHShQgncu77Se1cRmI3JaQNNcZRcLkaCjGITBoBw1QHhDKcdePaqSYxf00G+4yT/HdROXWNd3pP1UNh8nfhvohVcHuVO5tydrpfWP1TP227pkZ+bkHe+aLHtx1qIbTg3KDF/48Jg4ZWRcWTC/Uoo1AqviAeOBrNH+zCoqQaUgZB9x0Clma48SPv3I3ZCDDD2JBxC+Cf+QXyVgX8obb27SRlxyIYMwUH88ohSg2RnlEM2xJDs1NXtIr1m/PhYPGFmI0pNQLApemuSi3bi5RTpa78Kpz4R3xmpJf8qiH57IBA9Yd1MDe4YOLbNZ9SPU2C2PbIYUHD4aHjPNDo4dz7JgZ+VUwSNUs0tZDTEyITg4TcEEFrzcDFBRlYeZzj0rGfa7ypkHecOfkGuiLkkKT2uYbr+RcJ2mqLYhj43BAZ0PwrUvIIYuiSDmGALWnPBp7xv/hO4ApUDCZEhAIm4pWFGmafrlADKhOnmxxBQv4cRN7Mk5RiPPDGpyCsmyU/X71RgZoYGMTEeNWwsZFyLcaQuWBzWu5R2O+ds7khwfU"
`endif