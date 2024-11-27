// Copyright (C) 2024  Intel Corporation. All rights reserved.
// Your use of Intel Corporation's design tools, logic functions 
// and other software and tools, and any partner logic 
// functions, and any output files from any of the foregoing 
// (including device programming or simulation files), and any 
// associated documentation or information are expressly subject 
// to the terms and conditions of the Intel Program License 
// Subscription Agreement, the Intel Quartus Prime License Agreement,
// the Intel FPGA IP License Agreement, or other applicable license
// agreement, including, without limitation, that your use is for
// the sole purpose of programming logic devices manufactured by
// Intel and sold by Intel or its authorized distributors.  Please
// refer to the Intel FPGA Software License Subscription Agreements 
// on the Quartus Prime software download page.

// VENDOR "Altera"
// PROGRAM "Quartus Prime"
// VERSION "Version 24.1.0 Build 115 03/21/2024 SC Pro Edition"

// DATE "10/15/2024 10:52:25"

// 
// Device: Altera AGFB014R24B2E2V Package FBGA2486
// 

// 
// This greybox netlist file is for third party Synthesis Tools
// for timing and resource estimation only.
// 


module io_pll (
	locked,
	outclk_0,
	outclk_1,
	outclk_2,
	outclk_3,
	outclk_4,
	refclk,
	rst)/* synthesis synthesis_greybox=0 */;
output 	locked;
output 	outclk_0;
output 	outclk_1;
output 	outclk_2;
output 	outclk_3;
output 	outclk_4;
input 	refclk;
input 	rst;

wire gnd;
wire vcc;
wire unknown;

assign gnd = 1'b0;
assign vcc = 1'b1;
// unknown value (1'bx) is not needed for this tool. Default to 1'b0
assign unknown = 1'b0;

wire \iopll_0.tennm_pll_O_BLOCK_SELECT ;
wire \iopll_0.locked ;
wire \iopll_0.outclk_0 ;
wire \iopll_0.outclk_1 ;
wire \iopll_0.outclk_2 ;
wire \iopll_0.outclk_3 ;
wire \iopll_0.outclk_4 ;

wire [8:0] \iopll_0.tennm_pll_OUTCLK_bus ;

assign \iopll_0.outclk_0  = \iopll_0.tennm_pll_OUTCLK_bus [1];
assign \iopll_0.outclk_1  = \iopll_0.tennm_pll_OUTCLK_bus [2];
assign \iopll_0.outclk_2  = \iopll_0.tennm_pll_OUTCLK_bus [3];
assign \iopll_0.outclk_3  = \iopll_0.tennm_pll_OUTCLK_bus [4];
assign \iopll_0.outclk_4  = \iopll_0.tennm_pll_OUTCLK_bus [5];

tennm_iopll \iopll_0.tennm_pll (
	.core_refclk(refclk),
	.csr_clk(vcc),
	.csr_en(vcc),
	.csr_in(vcc),
	.dprio_clk(gnd),
	.dprio_rst_n(~rst),
	.dps_rst_n(~rst),
	.extswitch(gnd),
	.fbclk_in(gnd),
	.fblvds_in(gnd),
	.mdio_dis(gnd),
	.pfden(vcc),
	.phase_en(gnd),
	.pipeline_global_en_n(gnd),
	.pll_cascade_in(gnd),
	.pll_select_top_avl(vcc),
	.pma_csr_test_dis(vcc),
	.read(gnd),
	.rst_n(~rst),
	.scan_mode_n(vcc),
	.scan_shift_n(vcc),
	.uc_cal_clk(gnd),
	.uc_cal_read(gnd),
	.uc_cal_write(gnd),
	.up_dn(gnd),
	.user_mode(vcc),
	.write(gnd),
	.zdb_in(gnd),
	.clken({gnd,gnd}),
	.cnt_sel({gnd,gnd,gnd,gnd}),
	.dprio_address({gnd,gnd,gnd,gnd,gnd,gnd,gnd,gnd,gnd}),
	.num_phase_shifts({gnd,gnd,gnd}),
	.refclk({gnd,gnd,gnd,gnd}),
	.uc_cal_addr({gnd,gnd,gnd,gnd,gnd,gnd,gnd,gnd,gnd,gnd,gnd,gnd,gnd,gnd,gnd,gnd,gnd,gnd,gnd,gnd}),
	.uc_cal_writedata({gnd,gnd,gnd,gnd,gnd,gnd,gnd,gnd}),
	.writedata({gnd,gnd,gnd,gnd,gnd,gnd,gnd,gnd}),
	.block_select(\iopll_0.tennm_pll_O_BLOCK_SELECT ),
	.cal_ok(),
	.clk0_bad(),
	.clk1_bad(),
	.clksel(),
	.core_avl_busy(),
	.core_cal_done(),
	.csr_out(),
	.dll_output(),
	.fbclk_out(),
	.fblvds_out(),
	.iopll_out_sig1(),
	.iopll_out_sig2(),
	.lf_reset(),
	.lock(\iopll_0.locked ),
	.phase_done(),
	.pll_cascade_out(),
	.pll_pd(),
	.vcop_en(),
	.extclk_dft(),
	.extclk_output(),
	.loaden(),
	.lvds_clk(),
	.outclk(\iopll_0.tennm_pll_OUTCLK_bus ),
	.readdata(),
	.uc_cal_readdata(),
	.vcoph());
defparam \iopll_0.tennm_pll .auto_clk_sw_en = "false";
defparam \iopll_0.tennm_pll .bw_mode = "mid_bw";
defparam \iopll_0.tennm_pll .c0_bypass_en = "true";
defparam \iopll_0.tennm_pll .c0_coarse_dly = "0 ps";
defparam \iopll_0.tennm_pll .c0_even_duty_en = "false";
defparam \iopll_0.tennm_pll .c0_fine_dly = "0 ps";
defparam \iopll_0.tennm_pll .c0_high = 256;
defparam \iopll_0.tennm_pll .c0_low = 256;
defparam \iopll_0.tennm_pll .c0_out_en = "false";
defparam \iopll_0.tennm_pll .c0_ph_mux_prst = 0;
defparam \iopll_0.tennm_pll .c0_prst = 1;
defparam \iopll_0.tennm_pll .c1_bypass_en = "false";
defparam \iopll_0.tennm_pll .c1_coarse_dly = "0 ps";
defparam \iopll_0.tennm_pll .c1_even_duty_en = "true";
defparam \iopll_0.tennm_pll .c1_fine_dly = "0 ps";
defparam \iopll_0.tennm_pll .c1_high = 3;
defparam \iopll_0.tennm_pll .c1_low = 2;
defparam \iopll_0.tennm_pll .c1_out_en = "true";
defparam \iopll_0.tennm_pll .c1_ph_mux_prst = 0;
defparam \iopll_0.tennm_pll .c1_prst = 1;
defparam \iopll_0.tennm_pll .c2_bypass_en = "false";
defparam \iopll_0.tennm_pll .c2_coarse_dly = "0 ps";
defparam \iopll_0.tennm_pll .c2_even_duty_en = "false";
defparam \iopll_0.tennm_pll .c2_fine_dly = "0 ps";
defparam \iopll_0.tennm_pll .c2_high = 4;
defparam \iopll_0.tennm_pll .c2_low = 4;
defparam \iopll_0.tennm_pll .c2_out_en = "true";
defparam \iopll_0.tennm_pll .c2_ph_mux_prst = 0;
defparam \iopll_0.tennm_pll .c2_prst = 1;
defparam \iopll_0.tennm_pll .c3_bypass_en = "false";
defparam \iopll_0.tennm_pll .c3_coarse_dly = "0 ps";
defparam \iopll_0.tennm_pll .c3_even_duty_en = "true";
defparam \iopll_0.tennm_pll .c3_fine_dly = "0 ps";
defparam \iopll_0.tennm_pll .c3_high = 3;
defparam \iopll_0.tennm_pll .c3_low = 2;
defparam \iopll_0.tennm_pll .c3_out_en = "true";
defparam \iopll_0.tennm_pll .c3_ph_mux_prst = 0;
defparam \iopll_0.tennm_pll .c3_prst = 1;
defparam \iopll_0.tennm_pll .c4_bypass_en = "false";
defparam \iopll_0.tennm_pll .c4_coarse_dly = "0 ps";
defparam \iopll_0.tennm_pll .c4_even_duty_en = "false";
defparam \iopll_0.tennm_pll .c4_fine_dly = "0 ps";
defparam \iopll_0.tennm_pll .c4_high = 4;
defparam \iopll_0.tennm_pll .c4_low = 4;
defparam \iopll_0.tennm_pll .c4_out_en = "true";
defparam \iopll_0.tennm_pll .c4_ph_mux_prst = 0;
defparam \iopll_0.tennm_pll .c4_prst = 3;
defparam \iopll_0.tennm_pll .c5_bypass_en = "false";
defparam \iopll_0.tennm_pll .c5_coarse_dly = "0 ps";
defparam \iopll_0.tennm_pll .c5_even_duty_en = "false";
defparam \iopll_0.tennm_pll .c5_fine_dly = "0 ps";
defparam \iopll_0.tennm_pll .c5_high = 5;
defparam \iopll_0.tennm_pll .c5_low = 5;
defparam \iopll_0.tennm_pll .c5_out_en = "true";
defparam \iopll_0.tennm_pll .c5_ph_mux_prst = 0;
defparam \iopll_0.tennm_pll .c5_prst = 1;
defparam \iopll_0.tennm_pll .c6_bypass_en = "true";
defparam \iopll_0.tennm_pll .c6_coarse_dly = "0 ps";
defparam \iopll_0.tennm_pll .c6_even_duty_en = "false";
defparam \iopll_0.tennm_pll .c6_fine_dly = "0 ps";
defparam \iopll_0.tennm_pll .c6_high = 256;
defparam \iopll_0.tennm_pll .c6_low = 256;
defparam \iopll_0.tennm_pll .c6_out_en = "false";
defparam \iopll_0.tennm_pll .c6_ph_mux_prst = 0;
defparam \iopll_0.tennm_pll .c6_prst = 1;
defparam \iopll_0.tennm_pll .c7_bypass_en = "true";
defparam \iopll_0.tennm_pll .c7_coarse_dly = "0 ps";
defparam \iopll_0.tennm_pll .c7_even_duty_en = "false";
defparam \iopll_0.tennm_pll .c7_fine_dly = "0 ps";
defparam \iopll_0.tennm_pll .c7_high = 256;
defparam \iopll_0.tennm_pll .c7_low = 256;
defparam \iopll_0.tennm_pll .c7_out_en = "false";
defparam \iopll_0.tennm_pll .c7_ph_mux_prst = 0;
defparam \iopll_0.tennm_pll .c7_prst = 1;
defparam \iopll_0.tennm_pll .c8_bypass_en = "true";
defparam \iopll_0.tennm_pll .c8_coarse_dly = "0 ps";
defparam \iopll_0.tennm_pll .c8_even_duty_en = "false";
defparam \iopll_0.tennm_pll .c8_fine_dly = "0 ps";
defparam \iopll_0.tennm_pll .c8_high = 256;
defparam \iopll_0.tennm_pll .c8_low = 256;
defparam \iopll_0.tennm_pll .c8_out_en = "false";
defparam \iopll_0.tennm_pll .c8_ph_mux_prst = 0;
defparam \iopll_0.tennm_pll .c8_prst = 1;
defparam \iopll_0.tennm_pll .clkin_0_src = "coreclkin";
defparam \iopll_0.tennm_pll .clkin_1_src = "ioclkin_0";
defparam \iopll_0.tennm_pll .clock_name_1 = "outclk0";
defparam \iopll_0.tennm_pll .clock_name_2 = "outclk1";
defparam \iopll_0.tennm_pll .clock_name_3 = "outclk2";
defparam \iopll_0.tennm_pll .clock_name_4 = "outclk3";
defparam \iopll_0.tennm_pll .clock_name_5 = "outclk4";
defparam \iopll_0.tennm_pll .clock_name_global_0 = "false";
defparam \iopll_0.tennm_pll .clock_name_global_1 = "false";
defparam \iopll_0.tennm_pll .clock_name_global_2 = "false";
defparam \iopll_0.tennm_pll .clock_name_global_3 = "false";
defparam \iopll_0.tennm_pll .clock_name_global_4 = "false";
defparam \iopll_0.tennm_pll .clock_name_global_5 = "false";
defparam \iopll_0.tennm_pll .clock_name_global_6 = "false";
defparam \iopll_0.tennm_pll .clock_name_global_7 = "false";
defparam \iopll_0.tennm_pll .clock_name_global_8 = "false";
defparam \iopll_0.tennm_pll .clock_to_compensate = 1;
defparam \iopll_0.tennm_pll .cmp_buf_dly = "0 ps";
defparam \iopll_0.tennm_pll .device_variant = "device1";
defparam \iopll_0.tennm_pll .duty_cycle_0 = 50;
defparam \iopll_0.tennm_pll .duty_cycle_1 = 50;
defparam \iopll_0.tennm_pll .duty_cycle_2 = 50;
defparam \iopll_0.tennm_pll .duty_cycle_3 = 50;
defparam \iopll_0.tennm_pll .duty_cycle_4 = 50;
defparam \iopll_0.tennm_pll .duty_cycle_5 = 50;
defparam \iopll_0.tennm_pll .duty_cycle_6 = 50;
defparam \iopll_0.tennm_pll .duty_cycle_7 = 50;
defparam \iopll_0.tennm_pll .duty_cycle_8 = 50;
defparam \iopll_0.tennm_pll .extclk_0_cnt_src = "pll_extclk_cnt_src_vss";
defparam \iopll_0.tennm_pll .extclk_0_enable = "true";
defparam \iopll_0.tennm_pll .extclk_1_cnt_src = "pll_extclk_cnt_src_vss";
defparam \iopll_0.tennm_pll .extclk_1_enable = "true";
defparam \iopll_0.tennm_pll .feedback = "direct";
defparam \iopll_0.tennm_pll .iopll_type = "top_bottom";
defparam \iopll_0.tennm_pll .loaden_0_coarse_dly = "0 ps";
defparam \iopll_0.tennm_pll .loaden_0_fine_dly = "0 ps";
defparam \iopll_0.tennm_pll .loaden_1_coarse_dly = "0 ps";
defparam \iopll_0.tennm_pll .loaden_1_fine_dly = "0 ps";
defparam \iopll_0.tennm_pll .lock_mode = "mid_lock_time";
defparam \iopll_0.tennm_pll .lvdsclk_0_coarse_dly = "0 ps";
defparam \iopll_0.tennm_pll .lvdsclk_0_fine_dly = "0 ps";
defparam \iopll_0.tennm_pll .lvdsclk_1_coarse_dly = "0 ps";
defparam \iopll_0.tennm_pll .lvdsclk_1_fine_dly = "0 ps";
defparam \iopll_0.tennm_pll .m_counter_bypass_en = "false";
defparam \iopll_0.tennm_pll .m_counter_coarse_dly = "0 ps";
defparam \iopll_0.tennm_pll .m_counter_even_duty_en = "false";
defparam \iopll_0.tennm_pll .m_counter_fine_dly = "0 ps";
defparam \iopll_0.tennm_pll .m_counter_high = 5;
defparam \iopll_0.tennm_pll .m_counter_low = 5;
defparam \iopll_0.tennm_pll .m_counter_scratch = 1;
defparam \iopll_0.tennm_pll .manu_clk_sw_en = "false";
defparam \iopll_0.tennm_pll .merging_permitted = "false";
defparam \iopll_0.tennm_pll .n_counter_bypass_en = "true";
defparam \iopll_0.tennm_pll .n_counter_coarse_dly = "0 ps";
defparam \iopll_0.tennm_pll .n_counter_fine_dly = "0 ps";
defparam \iopll_0.tennm_pll .n_counter_high = 256;
defparam \iopll_0.tennm_pll .n_counter_low = 256;
defparam \iopll_0.tennm_pll .n_counter_odd_div_duty_en = "false";
defparam \iopll_0.tennm_pll .outclk0 = "0 ps";
defparam \iopll_0.tennm_pll .outclk1 = "200.0 mhz";
defparam \iopll_0.tennm_pll .outclk2 = "125.0 mhz";
defparam \iopll_0.tennm_pll .outclk3 = "200.0 mhz";
defparam \iopll_0.tennm_pll .outclk4 = "125.0 mhz";
defparam \iopll_0.tennm_pll .outclk5 = "100.0 mhz";
defparam \iopll_0.tennm_pll .outclk6 = "0 ps";
defparam \iopll_0.tennm_pll .outclk7 = "0 ps";
defparam \iopll_0.tennm_pll .outclk8 = "0 ps";
defparam \iopll_0.tennm_pll .pfd = "100.0 mhz";
defparam \iopll_0.tennm_pll .phase_shift_0 = "0 ps";
defparam \iopll_0.tennm_pll .phase_shift_1 = "0 ps";
defparam \iopll_0.tennm_pll .phase_shift_2 = "0 ps";
defparam \iopll_0.tennm_pll .phase_shift_3 = "0 ps";
defparam \iopll_0.tennm_pll .phase_shift_4 = "2000 ps";
defparam \iopll_0.tennm_pll .phase_shift_5 = "0 ps";
defparam \iopll_0.tennm_pll .phase_shift_6 = "0 ps";
defparam \iopll_0.tennm_pll .phase_shift_7 = "0 ps";
defparam \iopll_0.tennm_pll .phase_shift_8 = "0 ps";
defparam \iopll_0.tennm_pll .prot_mode = "basic";
defparam \iopll_0.tennm_pll .ref_buf_dly = "0 ps";
defparam \iopll_0.tennm_pll .refclk_src_mux = "clk_0";
defparam \iopll_0.tennm_pll .refclk_time = "100.0 mhz";
defparam \iopll_0.tennm_pll .self_reset_en = "false";
defparam \iopll_0.tennm_pll .silicon_rev = "reva";
defparam \iopll_0.tennm_pll .simple_pll = "false";
defparam \iopll_0.tennm_pll .speed_grade = "dash1";
defparam \iopll_0.tennm_pll .uc_channel_base_addr = 0;
defparam \iopll_0.tennm_pll .vco = "1000.0 mhz";
defparam \iopll_0.tennm_pll .zdb_in_clk_src = "clk0";

assign locked = \iopll_0.locked ;

assign outclk_0 = \iopll_0.outclk_0 ;

assign outclk_1 = \iopll_0.outclk_1 ;

assign outclk_2 = \iopll_0.outclk_2 ;

assign outclk_3 = \iopll_0.outclk_3 ;

assign outclk_4 = \iopll_0.outclk_4 ;

endmodule
