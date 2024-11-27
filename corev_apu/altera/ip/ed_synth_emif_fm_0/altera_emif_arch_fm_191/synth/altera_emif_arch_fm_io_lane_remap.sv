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
// This module instantiates one lane withina a tile
// This file remaps the parameter to uniquify the names for easy reading
// at the top level
//
///////////////////////////////////////////////////////////////////////////////

`define TO_STRING(S)  `"S`"

`define _map_pin_octrt(X) ( pin``X``_oct_rt == "static_oct_on" ? `TO_STRING(pin``X``_static_oct_on) : ( \
                                                                 `TO_STRING(pin``X``_static_oct_off)  ))

`define _map_pin_initial_out(X) ( pin``X``_initial_out == "initial_out_z" ? `TO_STRING(pin``X``_initial_out_z) : ( \
                                  pin``X``_initial_out == "initial_out_0" ? `TO_STRING(pin``X``_initial_out_0) : ( \
                                  pin``X``_initial_out == "initial_out_1" ? `TO_STRING(pin``X``_initial_out_1) : ( \
                                                                            `TO_STRING(pin``X``_initial_out_x) ))))

`define _map_lane_pin_mode(X) ( lane_pin``X``_mode == "pin_ddr"  ? `TO_STRING(lane_pin``X``_ddr) : ( \
                                                                   `TO_STRING(lane_pin``X``_unused) ))

`define _map_pin_dynoct(X) ( pin``X``_dyn_oct == "dyn_oct_on" ? `TO_STRING(pin``X``_dyn_oct_on) : ( \
                                                                `TO_STRING(pin``X``_dyn_oct_off) ))

`define _map_db_pin_mode(X) ( \
                              db_pin``X``_mode == "ac_hmc"         ? `TO_STRING(pin``X``_ac_wdb_ddr4_hmc) : ( \
                              db_pin``X``_mode == "dq_wdb_mode"    ? `TO_STRING(pin``X``_dq_wdb_ddr4_mode) : ( \
                              db_pin``X``_mode == "dm_wdb_mode"    ? `TO_STRING(pin``X``_dm_wdb_ddr4_mode) : ( \
                              db_pin``X``_mode == "dbi_wdb_mode"   ? `TO_STRING(pin``X``_dbi_wdb_ddr4_mode) : ( \
                              db_pin``X``_mode == "clk_wdb_mode"   ? `TO_STRING(pin``X``_clk_wdb_ddr4_mode) : ( \
                              db_pin``X``_mode == "clkb_wdb_mode"  ? `TO_STRING(pin``X``_clkb_wdb_ddr4_mode) : ( \
                              db_pin``X``_mode == "dqs_wdb_mode"   ? `TO_STRING(pin``X``_dqs_wdb_ddr4_mode) : ( \
                              db_pin``X``_mode == "dqsb_wdb_mode"  ? `TO_STRING(pin``X``_dqsb_wdb_ddr4_mode) : ( \
                              db_pin``X``_mode == "ac_in_core"     ? `TO_STRING(pin``X``_ac_in_core) : ( \
                              db_pin``X``_mode == "ac_core"        ? `TO_STRING(pin``X``_ac_core) : ( \
                              db_pin``X``_mode == "dq_mode"        ? `TO_STRING(pin``X``_dq_mode) : ( \
                              db_pin``X``_mode == "dm_mode"        ? `TO_STRING(pin``X``_dm_mode) : ( \
                              db_pin``X``_mode == "dbi_mode"       ? `TO_STRING(pin``X``_dbi_mode) : ( \
                              db_pin``X``_mode == "clk_mode"       ? `TO_STRING(pin``X``_clk_mode) : ( \
                              db_pin``X``_mode == "clkb_mode"      ? `TO_STRING(pin``X``_clkb_mode) : ( \
                              db_pin``X``_mode == "dqs_mode"       ? `TO_STRING(pin``X``_dqs_mode) : ( \
                              db_pin``X``_mode == "dqsb_mode"      ? `TO_STRING(pin``X``_dqsb_mode) : ( \
                              db_pin``X``_mode == "dqs_ddr4_mode"  ? `TO_STRING(pin``X``_dqs_ddr4_mode) : ( \
                              db_pin``X``_mode == "dqsb_ddr4_mode" ? `TO_STRING(pin``X``_dqsb_ddr4_mode) : ( \
                              db_pin``X``_mode == "rdq_mode"       ? `TO_STRING(pin``X``_rdq_mode) : ( \
                              db_pin``X``_mode == "rdqs_mode"      ? `TO_STRING(pin``X``_rdqs_mode) : ( \
                              db_pin``X``_mode == "gpio_mode"      ? `TO_STRING(pin``X``_gpio_mode) : ( \
                                                  "UNMATCHED_DB_PIN_MODE" )))))))))))))))))))))))

`define _map_pin_mode_ddr(X) ( pin``X``_mode_ddr == "mode_sdr" ? `TO_STRING(pin``X``_mode_sdr) : ( \
                                                                             `TO_STRING(pin``X``_mode_ddr) ))

`define _map_pin_dqs_mode(X) ( pin``X``_dqs_mode == "dqs_sampler_a" ? `TO_STRING(pin``X``_dqs_sampler_a) : ( \
                               pin``X``_dqs_mode == "dqs_sampler_b" ? `TO_STRING(pin``X``_dqs_sampler_b) : ( \
                                                                      `TO_STRING(pin``X``_dqs_sampler_b_a_rise) )))

`define _map_pin_data_in_mode(X) ( pin``X``_data_in_mode  == "ca"                 ? `TO_STRING(pin``X``_ca) : ( \
                                   pin``X``_data_in_mode  == "clock"              ? `TO_STRING(pin``X``_clock) : ( \
                                   pin``X``_data_in_mode  == "dq"                 ? `TO_STRING(pin``X``_dq) : ( \
                                   pin``X``_data_in_mode  == "dqs"                ? `TO_STRING(pin``X``_dqs) : ( \
                                   pin``X``_data_in_mode  == "dpa_slave"          ? `TO_STRING(pin``X``_dpa_slave) : ( \
                                   pin``X``_data_in_mode  == "dpa_master"         ? `TO_STRING(pin``X``_dpa_master) : ( \
                                   pin``X``_data_in_mode  == "dq_xor_a_loopback"  ? `TO_STRING(pin``X``_dq_xor_a_loopback) : ( \
                                   pin``X``_data_in_mode  == "dq_xor_b_loopback"  ? `TO_STRING(pin``X``_dq_xor_b_loopback) : ( \
                                                                                    `TO_STRING(pin``X``_dqs_xor_loopback) )))))))))

`define _map_pin_gpio_differential(X) ( pin``X``_gpio_differential == "gpio_single_ended" ? `TO_STRING(pin``X``_gpio_single_ended) : ( \
                                                                                            `TO_STRING(pin``X``_gpio_differential) ))

`define _map_pin_dq_in_select(X) ( pin``X``_dq_in_select == "dq_sstl_in"         ? `TO_STRING(pin``X``_dq_sstl_in) : ( \
                                   pin``X``_dq_in_select == "dq_loopback_in"     ? `TO_STRING(pin``X``_dq_loopback_in) : ( \
                                   pin``X``_dq_in_select == "dq_xor_loopback_in" ? `TO_STRING(pin``X``_dq_xor_loopback_in) : ( \
                                   pin``X``_dq_in_select == "dq_differential_in" ? `TO_STRING(pin``X``_dq_differential_in) : ( \
                                                                                   `TO_STRING(pin``X``_dq_disabled) )))))

`define _map_lane_pin_ddr_mode(X) ( lane_pin``X``_ddr_mode == "ddr_notddr"          ? `TO_STRING(lane_pin``X``_ddr_notddr) : ( \
                                    lane_pin``X``_ddr_mode == "ddr_dq"              ? `TO_STRING(lane_pin``X``_ddr_dq) : ( \
                                    lane_pin``X``_ddr_mode == "ddr_dqs"             ? `TO_STRING(lane_pin``X``_ddr_dqs) : ( \
                                    lane_pin``X``_ddr_mode == "ddr_dqsb"            ? `TO_STRING(lane_pin``X``_ddr_dqsb) : ( \
                                    lane_pin``X``_ddr_mode == "ddr_dm"              ? `TO_STRING(lane_pin``X``_ddr_dm) : ( \
                                    lane_pin``X``_ddr_mode == "ddr_ca_ddr"          ? `TO_STRING(lane_pin``X``_ddr_ca_ddr) : ( \
                                    lane_pin``X``_ddr_mode == "ddr_ca_sdr"          ? `TO_STRING(lane_pin``X``_ddr_ca_sdr) : ( \
                                    lane_pin``X``_ddr_mode == "ddr_phylite_data_qr" ? `TO_STRING(lane_pin``X``_ddr_phylite_data_qr) : ( \
                                                                                      `TO_STRING(lane_pin``X``_ddr_phylite_data_hr) )))))))))

module altera_emif_arch_fm_io_lane_remap (
   input  [1:0] phy_clk,
   input  [1:0] phy_clk_local_early,
   input  [1:0] phy_clk_local_late,
   input  [7:0] phy_clk_phs,

   input        reset_n,
   input        pll_locked,
   input        dll_ref_clk,
   output [5:0] ioereg_locked,

   input  [47:0] oe_from_core,
   input  [95:0] data_from_core,
   output [95:0] data_to_core,
   input  [15:0] mrnk_read_core,
   input  [15:0] mrnk_write_core,
   input   [3:0] rdata_en_full_core,
   output  [3:0] rdata_valid_core,

   input         core2dbc_rd_data_rdy,
   input         core2dbc_wr_data_vld0,
   input  [12:0] core2dbc_wr_ecc_info,
   output        dbc2core_rd_data_vld0,
   output        dbc2core_rd_type,
   output [11:0] dbc2core_wb_pointer,
   output        dbc2core_wr_data_rdy,

   input  [95:0] ac_hmc,
   output  [5:0] afi_rlat_core,
   output  [5:0] afi_wlat_core,
   input  [17:0] cfg_dbc,
   input  [50:0] ctl2dbc0,
   input  [50:0] ctl2dbc1,
   output [22:0] dbc2ctl,

   input  [54:0] cal_avl_in,
   output [31:0] cal_avl_readdata_out,
   output [54:0] cal_avl_out,
   input  [31:0] cal_avl_readdata_in,

   input [1:0]   dqs_in,
   input [1:0]   broadcast_in_bot,
   input [1:0]   broadcast_in_top,
   output [1:0]  broadcast_out_bot,
   output [1:0]  broadcast_out_top,

   input  [11:0] data_in,
   output [11:0] data_out,
   output [11:0] data_oe,
   output [11:0] oct_enable,

   input   [2:0] core_dll,
   output [12:0] dll_core,

   input    sync_clk_bot_in,
   output   sync_clk_bot_out,
   input    sync_clk_top_in,
   output   sync_clk_top_out,
   input    sync_data_bot_in,
   output   sync_data_bot_out,
   input    sync_data_top_in,
   output   sync_data_top_out,

   output [1:0]   dft_phy_clk
);
timeunit 1ps;
timeprecision 1ps;


parameter memory_controller = "smc";
parameter memory_standard = "ddr4";
parameter memory_burst_length = "bl8";
parameter memory_width = "x8";
parameter phy_clk_sel = 0;
parameter lane_mode = "lane_unused";
parameter lane_ddr_mode = "lane_ddr_notddr";
parameter logic [15:0] clock_period_ps = 'd0;

parameter dqs_enable_delay = 6'd0;
parameter dqs_phase_shift_b = 13'd0;
parameter dqs_phase_shift_a = 13'd0;
parameter oct_size = 4'd0;
parameter rd_valid_delay = 7'd0;

parameter mode_rate_in = "in_rate_1_4";
parameter mode_rate_out = "out_rate_full";
parameter logic [2:0] lock_speed = 3'h6;
parameter calibration = "skip";

parameter lane_pin0_mode  = "lane_pin_unused";
parameter lane_pin1_mode  = "lane_pin_unused";
parameter lane_pin2_mode  = "lane_pin_unused";
parameter lane_pin3_mode  = "lane_pin_unused";
parameter lane_pin4_mode  = "lane_pin_unused";
parameter lane_pin5_mode  = "lane_pin_unused";
parameter lane_pin6_mode  = "lane_pin_unused";
parameter lane_pin7_mode  = "lane_pin_unused";
parameter lane_pin8_mode  = "lane_pin_unused";
parameter lane_pin9_mode  = "lane_pin_unused";
parameter lane_pin10_mode = "lane_pin_unused";
parameter lane_pin11_mode = "lane_pin_unused";

parameter lane_pin0_ddr_mode = "lane_pin_unused";
parameter lane_pin1_ddr_mode = "lane_pin_unused";
parameter lane_pin2_ddr_mode = "lane_pin_unused";
parameter lane_pin3_ddr_mode = "lane_pin_unused";
parameter lane_pin4_ddr_mode = "lane_pin_unused";
parameter lane_pin5_ddr_mode = "lane_pin_unused";
parameter lane_pin6_ddr_mode = "lane_pin_unused";
parameter lane_pin7_ddr_mode = "lane_pin_unused";
parameter lane_pin8_ddr_mode = "lane_pin_unused";
parameter lane_pin9_ddr_mode = "lane_pin_unused";
parameter lane_pin10_ddr_mode = "lane_pin_unused";
parameter lane_pin11_ddr_mode = "lane_pin_unused";

parameter pin0_oct_rt = "static_oct_off";
parameter pin1_oct_rt = "static_oct_off";
parameter pin2_oct_rt = "static_oct_off";
parameter pin3_oct_rt = "static_oct_off";
parameter pin4_oct_rt = "static_oct_off";
parameter pin5_oct_rt = "static_oct_off";
parameter pin6_oct_rt = "static_oct_off";
parameter pin7_oct_rt = "static_oct_off";
parameter pin8_oct_rt = "static_oct_off";
parameter pin9_oct_rt = "static_oct_off";
parameter pin10_oct_rt = "static_oct_off";
parameter pin11_oct_rt = "static_oct_off";

parameter pin0_initial_out = "initial_out_z";
parameter pin1_initial_out = "initial_out_z";
parameter pin2_initial_out = "initial_out_z";
parameter pin3_initial_out = "initial_out_z";
parameter pin4_initial_out = "initial_out_z";
parameter pin5_initial_out = "initial_out_z";
parameter pin6_initial_out = "initial_out_z";
parameter pin7_initial_out = "initial_out_z";
parameter pin8_initial_out = "initial_out_z";
parameter pin9_initial_out = "initial_out_z";
parameter pin10_initial_out = "initial_out_z";
parameter pin11_initial_out = "initial_out_z";

parameter pin0_dyn_oct = "dyn_oct_off";
parameter pin1_dyn_oct = "dyn_oct_off";
parameter pin2_dyn_oct = "dyn_oct_off";
parameter pin3_dyn_oct = "dyn_oct_off";
parameter pin4_dyn_oct = "dyn_oct_off";
parameter pin5_dyn_oct = "dyn_oct_off";
parameter pin6_dyn_oct = "dyn_oct_off";
parameter pin7_dyn_oct = "dyn_oct_off";
parameter pin8_dyn_oct = "dyn_oct_off";
parameter pin9_dyn_oct = "dyn_oct_off";
parameter pin10_dyn_oct = "dyn_oct_off";
parameter pin11_dyn_oct = "dyn_oct_off";

parameter pin0_dq_in_select = "dq_disabled";
parameter pin1_dq_in_select = "dq_disabled";
parameter pin2_dq_in_select = "dq_disabled";
parameter pin3_dq_in_select = "dq_disabled";
parameter pin4_dq_in_select = "dq_disabled";
parameter pin5_dq_in_select = "dq_disabled";
parameter pin6_dq_in_select = "dq_disabled";
parameter pin7_dq_in_select = "dq_disabled";
parameter pin8_dq_in_select = "dq_disabled";
parameter pin9_dq_in_select = "dq_disabled";
parameter pin10_dq_in_select = "dq_disabled";
parameter pin11_dq_in_select = "dq_disabled";

parameter pin0_mode_ddr = "mode_ddr";
parameter pin1_mode_ddr = "mode_ddr";
parameter pin2_mode_ddr = "mode_ddr";
parameter pin3_mode_ddr = "mode_ddr";
parameter pin4_mode_ddr = "mode_ddr";
parameter pin5_mode_ddr = "mode_ddr";
parameter pin6_mode_ddr = "mode_ddr";
parameter pin7_mode_ddr = "mode_ddr";
parameter pin8_mode_ddr = "mode_ddr";
parameter pin9_mode_ddr = "mode_ddr";
parameter pin10_mode_ddr = "mode_ddr";
parameter pin11_mode_ddr = "mode_ddr";

parameter pin0_dqs_mode = "dqs_sampler_a";
parameter pin1_dqs_mode = "dqs_sampler_a";
parameter pin2_dqs_mode = "dqs_sampler_a";
parameter pin3_dqs_mode = "dqs_sampler_a";
parameter pin4_dqs_mode = "dqs_sampler_a";
parameter pin5_dqs_mode = "dqs_sampler_a";
parameter pin6_dqs_mode = "dqs_sampler_a";
parameter pin7_dqs_mode = "dqs_sampler_a";
parameter pin8_dqs_mode = "dqs_sampler_a";
parameter pin9_dqs_mode = "dqs_sampler_a";
parameter pin10_dqs_mode = "dqs_sampler_a";
parameter pin11_dqs_mode = "dqs_sampler_a";

parameter pin0_data_in_mode = "ca";
parameter pin1_data_in_mode = "ca";
parameter pin2_data_in_mode = "ca";
parameter pin3_data_in_mode = "ca";
parameter pin4_data_in_mode = "ca";
parameter pin5_data_in_mode = "ca";
parameter pin6_data_in_mode = "ca";
parameter pin7_data_in_mode = "ca";
parameter pin8_data_in_mode = "ca";
parameter pin9_data_in_mode = "ca";
parameter pin10_data_in_mode = "ca";
parameter pin11_data_in_mode = "ca";

parameter db_pin0_mode = "pin_gpio_mode";
parameter db_pin1_mode = "pin_gpio_mode";
parameter db_pin2_mode = "pin_gpio_mode";
parameter db_pin3_mode = "pin_gpio_mode";
parameter db_pin4_mode = "pin_gpio_mode";
parameter db_pin5_mode = "pin_gpio_mode";
parameter db_pin6_mode = "pin_gpio_mode";
parameter db_pin7_mode = "pin_gpio_mode";
parameter db_pin8_mode = "pin_gpio_mode";
parameter db_pin9_mode = "pin_gpio_mode";
parameter db_pin10_mode = "pin_gpio_mode";
parameter db_pin11_mode = "pin_gpio_mode";

parameter pin0_gpio_differential = "gpio_single_ended";
parameter pin1_gpio_differential = "gpio_single_ended";
parameter pin2_gpio_differential = "gpio_single_ended";
parameter pin3_gpio_differential = "gpio_single_ended";
parameter pin4_gpio_differential = "gpio_single_ended";
parameter pin5_gpio_differential = "gpio_single_ended";
parameter pin6_gpio_differential = "gpio_single_ended";
parameter pin7_gpio_differential = "gpio_single_ended";
parameter pin8_gpio_differential = "gpio_single_ended";
parameter pin9_gpio_differential = "gpio_single_ended";
parameter pin10_gpio_differential = "gpio_single_ended";
parameter pin11_gpio_differential = "gpio_single_ended";

parameter db_hmc_or_core = "core";
parameter db_dbi_sel = "dbi_dq0";
parameter db_dbi_wr_en = "dbi_wr_dis";
parameter db_dbi_rd_en = "dbi_rd_dis";

parameter db_avl_ena = "avl_disable";
parameter db_avl_base_addr = 9'd0;
parameter db_avl_broadcast_en = "bc_disable";

parameter db_sel_core_clk = "phy_clk0";

parameter db_rwlat_mode = "avl_vlu";
parameter db_ptr_pipeline_depth = "db_ptr_pipeline_depth_0";
parameter db_preamble_mode = "preamble_one_cycle";
parameter db_data_alignment_mode = "align_disable";
parameter db_db2core_registered = "registered";
parameter db_seq_rd_en_full_pipeline = "db_seq_rd_en_full_pipeline_0";
parameter dll_rst_en = "dll_rst_dis";
parameter dll_core_updnen = "core_updn_en";
parameter dll_ctlsel = "ctl_static";
parameter enable_toggler = "preamble_track_dqs_enable";

parameter dqs_select_a = "dqs_diff_in_1_a";
parameter dqs_select_b = "dqs_diff_in_1_b";

parameter db_afi_wlat_vlu = 6'd0;
parameter db_afi_rlat_vlu = 6'd0;
parameter dbc_wb_reserved_entry = 5'd0;
parameter dll_ctl_static = 11'd0;
parameter db_mrnk_write_mode = "mrnk_write_enable";

parameter db_dbc_rb_readylat_en = "dbc_rb_readylat_disable";
parameter db_dbc_wb_readylat_en = "dbc_wb_readylat_disable";
parameter db_dbc_ctrl_rc_en_scalar = "dbc_rc_scalar_disable";

localparam l_phy_clk_sel = (phy_clk_sel == 0) ? "phy_clk_0" : "phy_clk_1";

localparam [15:0] clock_period_remap = clock_period_ps * 10;

`define a_db_seq_rd_en_full_pipeline_remap(a_db_seq_rd_en_full_pipeline) \
    (a_db_seq_rd_en_full_pipeline == "db_seq_rd_en_full_pipeline_0") ?        "db_seq_rd_en_full_pipeline_1": \
    (a_db_seq_rd_en_full_pipeline == "db_seq_rd_en_full_pipeline_1") ?        "db_seq_rd_en_full_pipeline_2": \
    (a_db_seq_rd_en_full_pipeline == "db_seq_rd_en_full_pipeline_2") ?        "db_seq_rd_en_full_pipeline_3": \
    (a_db_seq_rd_en_full_pipeline == "db_seq_rd_en_full_pipeline_3") ?        "db_seq_rd_en_full_pipeline_4": \
    (a_db_seq_rd_en_full_pipeline == "db_seq_rd_en_full_pipeline_4") ?        "db_seq_rd_en_full_pipeline_5": \
    (a_db_seq_rd_en_full_pipeline == "db_seq_rd_en_full_pipeline_5") ?        "db_seq_rd_en_full_pipeline_6": \
    (a_db_seq_rd_en_full_pipeline == "db_seq_rd_en_full_pipeline_6") ?        "db_seq_rd_en_full_pipeline_7": \
    (a_db_seq_rd_en_full_pipeline == "db_seq_rd_en_full_pipeline_7") ?        "db_seq_rd_en_full_pipeline_8": \
    (a_db_seq_rd_en_full_pipeline == "db_seq_rd_en_full_pipeline_8") ?        "db_seq_rd_en_full_pipeline_9": \
    (a_db_seq_rd_en_full_pipeline == "db_seq_rd_en_full_pipeline_9") ?        "db_seq_rd_en_full_pipeline_10": \
                                                                              "db_seq_rd_en_full_pipeline_2"

   tennm_io_12_lane #(
      .a_memory_standard             (memory_standard),
      .a_memory_burst_length         (memory_burst_length),
      .a_memory_controller           (memory_controller),
      .a_memory_width                (memory_width),

      .a_mode_rate_in                (mode_rate_in),
      .a_mode_rate_out               (mode_rate_out),
      .a_clock_period                (clock_period_remap),
      .a_phy_clk_mode                (l_phy_clk_sel),
      .a_calibration                 (calibration),
      .a_lock_speed                  (lock_speed),
      .a_db_dbc_ctrl_rc_en_scalar    (db_dbc_ctrl_rc_en_scalar),
      .a_db_avl_base_addr            (db_avl_base_addr),
      .a_db_avl_broadcast_en         (db_avl_broadcast_en),
      .a_db_avl_ena                  (db_avl_ena),
      .a_dqs_select_a                (dqs_select_a),
      .a_dqs_select_b                (dqs_select_b),

      .a_memory_rank_size           ("rank1"), 
      .a_output_phase               (0),
      .a_io_out_delay               (0),
      .a_board_delay                (0),
      .a_io_in_delay                (0),
      .a_pipe_latency               (0),
      .a_cas_latency                (0),
      .a_wl_latency                 (0),
      .a_al_latency                 (0),
      .a_register_latency           (0),
      .a_parity_latency             (0),
      .a_phy_wlat                   (0),
      .a_dq_wl_remainder            (0),
      .a_ck_cmd                     (0),
      .a_dqss                       (12'h40),
      .a_dq_read_latency            (0),
      .a_dq_write_latency           (0),
      .a_cmd_core_to_codin          (0),
      .a_dq_min_core_to_codin       (0),
      .a_dq_rem_core_to_codin       (0),
      .a_struct_gate_delay          (8'h0b),
      .a_cmd_pipe_latency           (0),
      .a_cmd_add_phy_delay          (0),
      .a_mode_output                ("oct_delayed"),
      .a_dq_min_output_phase        (0),
      .a_cmd_min_output_phase       (0),

      .a_lane_ddr_mode               (lane_ddr_mode),
      .a_lane_pin0_ddr_mode          (`_map_lane_pin_ddr_mode(0)),
      .a_lane_pin1_ddr_mode          (`_map_lane_pin_ddr_mode(1)),
      .a_lane_pin2_ddr_mode          (`_map_lane_pin_ddr_mode(2)),
      .a_lane_pin3_ddr_mode          (`_map_lane_pin_ddr_mode(3)),
      .a_lane_pin4_ddr_mode          (`_map_lane_pin_ddr_mode(4)),
      .a_lane_pin5_ddr_mode          (`_map_lane_pin_ddr_mode(5)),
      .a_lane_pin6_ddr_mode          (`_map_lane_pin_ddr_mode(6)),
      .a_lane_pin7_ddr_mode          (`_map_lane_pin_ddr_mode(7)),
      .a_lane_pin8_ddr_mode          (`_map_lane_pin_ddr_mode(8)),
      .a_lane_pin9_ddr_mode          (`_map_lane_pin_ddr_mode(9)),
      .a_lane_pin10_ddr_mode         (`_map_lane_pin_ddr_mode(10)),
      .a_lane_pin11_ddr_mode         (`_map_lane_pin_ddr_mode(11)),
      
      .a_lane_mode                   (lane_mode), 
      .a_lane_pin0_mode              (`_map_lane_pin_mode(0)),
      .a_lane_pin1_mode              (`_map_lane_pin_mode(1)),
      .a_lane_pin2_mode              (`_map_lane_pin_mode(2)),
      .a_lane_pin3_mode              (`_map_lane_pin_mode(3)),
      .a_lane_pin4_mode              (`_map_lane_pin_mode(4)),
      .a_lane_pin5_mode              (`_map_lane_pin_mode(5)),
      .a_lane_pin6_mode              (`_map_lane_pin_mode(6)),
      .a_lane_pin7_mode              (`_map_lane_pin_mode(7)),
      .a_lane_pin8_mode              (`_map_lane_pin_mode(8)),
      .a_lane_pin9_mode              (`_map_lane_pin_mode(9)),
      .a_lane_pin10_mode             (`_map_lane_pin_mode(10)),
      .a_lane_pin11_mode             (`_map_lane_pin_mode(11)),

      .a_lane_lvds0_mode             ("lane_lvds0_notlvds"),
      .a_lane_lvds1_mode             ("lane_lvds1_notlvds"),
      .a_lane_lvds2_mode             ("lane_lvds2_notlvds"),
      .a_lane_lvds3_mode             ("lane_lvds3_notlvds"),
      .a_lane_lvds4_mode             ("lane_lvds4_notlvds"),
      .a_lane_lvds5_mode             ("lane_lvds5_notlvds"),

      .a_db_hmc_or_core              (db_hmc_or_core),
      .a_db_db2core_registered       (db_db2core_registered),
      .a_db_preamble_mode            (db_preamble_mode),
      .a_db_data_alignment_mode      (db_data_alignment_mode),

      .a_db_pin0_mode                (`_map_db_pin_mode(0)),
      .a_db_pin1_mode                (`_map_db_pin_mode(1)),
      .a_db_pin2_mode                (`_map_db_pin_mode(2)),
      .a_db_pin3_mode                (`_map_db_pin_mode(3)),
      .a_db_pin4_mode                (`_map_db_pin_mode(4)),
      .a_db_pin5_mode                (`_map_db_pin_mode(5)),
      .a_db_pin6_mode                (`_map_db_pin_mode(6)),
      .a_db_pin7_mode                (`_map_db_pin_mode(7)),
      .a_db_pin8_mode                (`_map_db_pin_mode(8)),
      .a_db_pin9_mode                (`_map_db_pin_mode(9)),
      .a_db_pin10_mode               (`_map_db_pin_mode(10)),
      .a_db_pin11_mode               (`_map_db_pin_mode(11)),


      .a_pin0_octrt                  (`_map_pin_octrt(0)),
      .a_pin1_octrt                  (`_map_pin_octrt(1)),
      .a_pin2_octrt                  (`_map_pin_octrt(2)),
      .a_pin3_octrt                  (`_map_pin_octrt(3)),
      .a_pin4_octrt                  (`_map_pin_octrt(4)),
      .a_pin5_octrt                  (`_map_pin_octrt(5)),
      .a_pin6_octrt                  (`_map_pin_octrt(6)),
      .a_pin7_octrt                  (`_map_pin_octrt(7)),
      .a_pin8_octrt                  (`_map_pin_octrt(8)),
      .a_pin9_octrt                  (`_map_pin_octrt(9)),
      .a_pin10_octrt                 (`_map_pin_octrt(10)),
      .a_pin11_octrt                 (`_map_pin_octrt(11)),

      .a_pin0_initial_out            (`_map_pin_initial_out(0)),
      .a_pin1_initial_out            (`_map_pin_initial_out(1)),
      .a_pin2_initial_out            (`_map_pin_initial_out(2)),
      .a_pin3_initial_out            (`_map_pin_initial_out(3)),
      .a_pin4_initial_out            (`_map_pin_initial_out(4)),
      .a_pin5_initial_out            (`_map_pin_initial_out(5)),
      .a_pin6_initial_out            (`_map_pin_initial_out(6)),
      .a_pin7_initial_out            (`_map_pin_initial_out(7)),
      .a_pin8_initial_out            (`_map_pin_initial_out(8)),
      .a_pin9_initial_out            (`_map_pin_initial_out(9)),
      .a_pin10_initial_out           (`_map_pin_initial_out(10)),
      .a_pin11_initial_out           (`_map_pin_initial_out(11)),

      .a_pin0_dynoct                 (`_map_pin_dynoct(0)),
      .a_pin1_dynoct                 (`_map_pin_dynoct(1)),
      .a_pin2_dynoct                 (`_map_pin_dynoct(2)),
      .a_pin3_dynoct                 (`_map_pin_dynoct(3)),
      .a_pin4_dynoct                 (`_map_pin_dynoct(4)),
      .a_pin5_dynoct                 (`_map_pin_dynoct(5)),
      .a_pin6_dynoct                 (`_map_pin_dynoct(6)),
      .a_pin7_dynoct                 (`_map_pin_dynoct(7)),
      .a_pin8_dynoct                 (`_map_pin_dynoct(8)),
      .a_pin9_dynoct                 (`_map_pin_dynoct(9)),
      .a_pin10_dynoct                (`_map_pin_dynoct(10)),
      .a_pin11_dynoct                (`_map_pin_dynoct(11)),

      .a_pin0_mode_ddr               (`_map_pin_mode_ddr(0)),
      .a_pin1_mode_ddr               (`_map_pin_mode_ddr(1)),
      .a_pin2_mode_ddr               (`_map_pin_mode_ddr(2)),
      .a_pin3_mode_ddr               (`_map_pin_mode_ddr(3)),
      .a_pin4_mode_ddr               (`_map_pin_mode_ddr(4)),
      .a_pin5_mode_ddr               (`_map_pin_mode_ddr(5)),
      .a_pin6_mode_ddr               (`_map_pin_mode_ddr(6)),
      .a_pin7_mode_ddr               (`_map_pin_mode_ddr(7)),
      .a_pin8_mode_ddr               (`_map_pin_mode_ddr(8)),
      .a_pin9_mode_ddr               (`_map_pin_mode_ddr(9)),
      .a_pin10_mode_ddr              (`_map_pin_mode_ddr(10)),
      .a_pin11_mode_ddr              (`_map_pin_mode_ddr(11)),

      .a_pin0_dqs_mode               (`_map_pin_dqs_mode(0)),
      .a_pin1_dqs_mode               (`_map_pin_dqs_mode(1)),
      .a_pin2_dqs_mode               (`_map_pin_dqs_mode(2)),
      .a_pin3_dqs_mode               (`_map_pin_dqs_mode(3)),
      .a_pin4_dqs_mode               (`_map_pin_dqs_mode(4)),
      .a_pin5_dqs_mode               (`_map_pin_dqs_mode(5)),
      .a_pin6_dqs_mode               (`_map_pin_dqs_mode(6)),
      .a_pin7_dqs_mode               (`_map_pin_dqs_mode(7)),
      .a_pin8_dqs_mode               (`_map_pin_dqs_mode(8)),
      .a_pin9_dqs_mode               (`_map_pin_dqs_mode(9)),
      .a_pin10_dqs_mode              (`_map_pin_dqs_mode(10)),
      .a_pin11_dqs_mode              (`_map_pin_dqs_mode(11)),

      .a_pin0_data_in_mode           (`_map_pin_data_in_mode(0)),
      .a_pin1_data_in_mode           (`_map_pin_data_in_mode(1)),
      .a_pin2_data_in_mode           (`_map_pin_data_in_mode(2)),
      .a_pin3_data_in_mode           (`_map_pin_data_in_mode(3)),
      .a_pin4_data_in_mode           (`_map_pin_data_in_mode(4)),
      .a_pin5_data_in_mode           (`_map_pin_data_in_mode(5)),
      .a_pin6_data_in_mode           (`_map_pin_data_in_mode(6)),
      .a_pin7_data_in_mode           (`_map_pin_data_in_mode(7)),
      .a_pin8_data_in_mode           (`_map_pin_data_in_mode(8)),
      .a_pin9_data_in_mode           (`_map_pin_data_in_mode(9)),
      .a_pin10_data_in_mode          (`_map_pin_data_in_mode(10)),
      .a_pin11_data_in_mode          (`_map_pin_data_in_mode(11)),

      .a_pin0_gpio_differential      ("pin0_gpio_single_ended"),
      .a_pin1_gpio_differential      ("pin1_gpio_single_ended"),
      .a_pin2_gpio_differential      ("pin2_gpio_single_ended"),
      .a_pin3_gpio_differential      ("pin3_gpio_single_ended"),
      .a_pin4_gpio_differential      ("pin4_gpio_single_ended"),
      .a_pin5_gpio_differential      ("pin5_gpio_single_ended"),
      .a_pin6_gpio_differential      ("pin6_gpio_single_ended"),
      .a_pin7_gpio_differential      ("pin7_gpio_single_ended"),
      .a_pin8_gpio_differential      ("pin8_gpio_single_ended"),
      .a_pin9_gpio_differential      ("pin9_gpio_single_ended"),
      .a_pin10_gpio_differential     ("pin10_gpio_single_ended"),
      .a_pin11_gpio_differential     ("pin11_gpio_single_ended"),

      .a_pin0_dq_in_select           (`_map_pin_dq_in_select(0)),
      .a_pin1_dq_in_select           (`_map_pin_dq_in_select(1)),
      .a_pin2_dq_in_select           (`_map_pin_dq_in_select(2)),
      .a_pin3_dq_in_select           (`_map_pin_dq_in_select(3)),
      .a_pin4_dq_in_select           (`_map_pin_dq_in_select(4)),
      .a_pin5_dq_in_select           (`_map_pin_dq_in_select(5)),
      .a_pin6_dq_in_select           (`_map_pin_dq_in_select(6)),
      .a_pin7_dq_in_select           (`_map_pin_dq_in_select(7)),
      .a_pin8_dq_in_select           (`_map_pin_dq_in_select(8)),
      .a_pin9_dq_in_select           (`_map_pin_dq_in_select(9)),
      .a_pin10_dq_in_select          (`_map_pin_dq_in_select(10)),
      .a_pin11_dq_in_select          (`_map_pin_dq_in_select(11)),

      .a_db_afi_rlat_vlu             (db_afi_rlat_vlu),
      .a_db_afi_wlat_vlu             (db_afi_wlat_vlu),
      .a_db_sel_core_clk             (db_sel_core_clk),

      .a_db_dbi_wr_en                (db_dbi_wr_en),
      .a_db_dbi_rd_en                (db_dbi_rd_en),
      .a_db_dbi_sel                  (db_dbi_sel),
      .a_db_ptr_pipeline_depth       (db_ptr_pipeline_depth),
      .a_db_seq_rd_en_full_pipeline  (`a_db_seq_rd_en_full_pipeline_remap(db_seq_rd_en_full_pipeline)),

      .a_pin0_output_phase           (13'd0),
      .a_pin1_output_phase           (13'd0),
      .a_pin2_output_phase           (13'd0),
      .a_pin3_output_phase           (13'd0),
      .a_pin4_output_phase           (13'd0),
      .a_pin5_output_phase           (13'd0),
      .a_pin6_output_phase           (13'd0),
      .a_pin7_output_phase           (13'd0),
      .a_pin8_output_phase           (13'd0),
      .a_pin9_output_phase           (13'd0),
      .a_pin10_output_phase          (13'd0),
      .a_pin11_output_phase          (13'd0),

      .a_db_mrnk_write_mode          (db_mrnk_write_mode),
      .a_db_dbc_wb_reserved_entry    (dbc_wb_reserved_entry),

      .a_db_dbc_rb_readylat_en       (db_dbc_rb_readylat_en),
      .a_db_dbc_wb_readylat_en       (db_dbc_wb_readylat_en),

      .a_oct_size                    (oct_size),
      .a_rd_valid_delay              (rd_valid_delay),

      .a_dqs_enable_delay            (dqs_enable_delay),
      .a_dqs_phase_shift_b           (dqs_phase_shift_b),
      .a_dqs_phase_shift_a           (dqs_phase_shift_a),

      .a_dll_rst_en                  (dll_rst_en),
      .a_dll_core_updnen             (dll_core_updnen),
      .a_dll_ctlsel                  (dll_ctlsel),
      .a_dll_ctl_static              (dll_ctl_static)
   ) lane_inst (
      .phy_clk                       (phy_clk),
      .phy_clk_phs                   (phy_clk_phs),

      .phy_clk_local_early           (phy_clk_local_early),
      .phy_clk_local_late            (phy_clk_local_late),

      .reset_n                       (reset_n),
      .pll_locked                    (pll_locked),
      .dll_ref_clk                   (dll_ref_clk),
      .ioereg_locked                 (ioereg_locked),

      .oe_from_core                  (oe_from_core),
      .data_from_core                (data_from_core),
      .data_to_core                  (data_to_core),
      .mrnk_read_core                (mrnk_read_core),
      .mrnk_write_core               (mrnk_write_core),
      .rdata_en_full_core            (rdata_en_full_core),
      .rdata_valid_core              (rdata_valid_core),

      .core2dbc_rd_data_rdy          (core2dbc_rd_data_rdy),
      .core2dbc_wr_data_vld0         (core2dbc_wr_data_vld0),
      .core2dbc_wr_ecc_info          (core2dbc_wr_ecc_info),
      .dbc2core_rd_data_vld0         (dbc2core_rd_data_vld0),

      .dbc2core_rd_type              (dbc2core_rd_type),
      .dbc2core_wb_pointer           (dbc2core_wb_pointer),
      .dbc2core_wr_data_rdy          (dbc2core_wr_data_rdy),

      .ac_hmc                        (ac_hmc),
      .afi_rlat_core                 (afi_rlat_core),
      .afi_wlat_core                 (afi_wlat_core),
      .cfg_dbc                       (cfg_dbc),
      .ctl2dbc0                      (ctl2dbc0),
      .ctl2dbc1                      (ctl2dbc1),
      .dbc2ctl                       (dbc2ctl),

      .cal_avl_in                    (cal_avl_in),
      .cal_avl_readdata_out          (cal_avl_readdata_out),
      .cal_avl_out                   (cal_avl_out),
      .cal_avl_readdata_in           (cal_avl_readdata_in),

      .dqs_in                        (dqs_in),
      .broadcast_in_bot              (broadcast_in_bot),
      .broadcast_in_top              (broadcast_in_top),
      .broadcast_out_bot             (broadcast_out_bot),
      .broadcast_out_top             (broadcast_out_top),

      .data_in                       (data_in),
      .data_out                      (data_out),
      .data_oe                       (data_oe),
      .oct_enable                    (oct_enable),

      .core_dll                      (core_dll),
      .dll_core                      (dll_core),

      .sync_clk_bot_in               (sync_clk_bot_in),
      .sync_clk_bot_out              (sync_clk_bot_out),
      .sync_clk_top_in               (sync_clk_top_in),
      .sync_clk_top_out              (sync_clk_top_out),
      .sync_data_bot_in              (sync_data_bot_in),
      .sync_data_bot_out             (sync_data_bot_out),
      .sync_data_top_in              (sync_data_top_in),
      .sync_data_top_out             (sync_data_top_out),

      .dft_phy_clk                   (dft_phy_clk)
   );
endmodule
`ifdef QUESTA_INTEL_OEM
`pragma questa_oem_00 "EVeqkz9MvDzapiiVw7+udc++m43wu2P9R6Bkf/lfBn9ZttFzW71hzuu9P3yzPlvUUu1GESHEht8oUjkuxH5nYF5m2Y4yEaZOsor1W+qakklkcNM5gczDB8G/zUljAitcohcjlH9xX4F5r3RrLLQB1HrtXmnxKKrsVs2RsxKt4plRYJGUCxRjs6twKgr6lps1q22taZT7+7dZh7dYE0uKJfWB1PYeKR+rbOxvrAyMNm3g0SiPR8kcBjSVqQUz5PhpyZlwQ0KE7yFCmS6UWWe6bYAtJe7R/CNCtXSfgRYjdyzTvn3hpT6XEuKJxVexm4sgKWi4fEBb2SYQcUMoty4NUzeyiKLKqJ8JoSO1tLz5y7YNTd/tTEX9XPflI5Wj1IJ7bRKo1Igi9hwG5VEL7LxXmlzfFkmP7zA3z8zQRgNkPrYvcYKwqA+8Ir5j64R8nZEsTD7DJFwlvvBGjSin5gFoAOZYEi/nJbQCW3M0s71wazi5WBL0QZrhIDyzhN5aQh2lDClozFaDCfCzdtcl/CZjKZ/hm+epLPKEj0pE4upDXeYPPbScqgzLrtj8IaZUobImsxrYFUccYOmEkIcAtykXuJGdPp1VhuzdbQZzSUORxUxHoD2bF/R8VW9rZFmcAV4WJ4WHJdFjPeZgNjTSn27d+p8V8SzLJ79XgNtCt5aBPfexMu5fQE9p/2aVBS4PvNVkF004IuXR3gmU8aQNq7qbz6WkU4XOEakacu3Bw4ZYWcJhpFhcCGUVg2VaQdT4VlIvwAHKudsJj93MfUZwuLR5mI7VWk37xQ/+QNrwgsc3k+WCnOUHJ52JlsHkKF5KoiT6JrmjOvsOYmV5nwCr94QJ2bRjKmnk4HD0M8b5gXy+IIfTkq7n1tGzd2smxz0rKOI1EiWucV+wrjDZyrUFUugUSyGTFcv8XOIJbf+JZ2Irjf0apfAQ2Q4qn1Th3aHCPVFn3f956kDnZG9UgERbQCBBF5C9/URKfU9CkAoxChlK1lkBnGGRBBJ5ZeJgEl96Nl9P"
`endif