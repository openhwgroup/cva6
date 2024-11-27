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


// This is a testing TERP file.
// Wrappers for other families can be found in altera_pll.v (pre Arria 10) and twentynm_iopll.v

`timescale 1ps/1ps
module io_pll_altera_iopll_1931_oypl3jq 
(
    // interface refclk
    input wire refclk,
    // interface locked
    output wire locked,
    // interface reset
    input wire rst,
    // interface outclk0
    output wire outclk_0,
    // interface outclk1
    output wire outclk_1,
    // interface outclk2
    output wire outclk_2,
    // interface outclk3
    output wire outclk_3,
    // interface outclk4
    output wire outclk_4
);

wire [1:0] extclk_out_wire;
wire refclk1;
assign refclk1 = 1'b0;
wire fbclk;
assign fbclk = 1'b0;
wire fboutclk;
wire zdbfbclk;
wire [1:0] loaden;
wire phase_done;
wire [29:0] reconfig_to_pll;
assign reconfig_to_pll = 30'b0;
wire scanclk;
assign scanclk = 1'b0;
wire [7:0] phout;
wire [2:0] num_phase_shifts;
assign num_phase_shifts = 3'b0;
wire permit_cal;
assign permit_cal = 1'b1;
wire fblvds_out;
assign fblvds_out = 1'b1;
wire [4:0] cntsel;
assign cntsel = 5'b0;
wire [1:0] clkbad;
wire [1:0] lvds_clk;
wire [8:0] outclk;
wire [2:0] unused_wires_high;

wire [0:0] unused_wires_low;
assign unused_wires_low = outclk[0:0];
assign unused_wires_high = outclk[8:6];
assign outclk_0 = outclk[1];
assign outclk_1 = outclk[2];
assign outclk_2 = outclk[3];
assign outclk_3 = outclk[4];
assign outclk_4 = outclk[5];
wire phase_en;
assign phase_en = 1'b0;
wire extswitch;
assign extswitch = 1'b0;
wire cascade_out;
wire dll_output;
assign dll_output = 1'b1;
wire activeclk;
wire adjpllin;
assign adjpllin = 1'b0;
wire updn;
assign updn = 1'b0;
wire [10:0] reconfig_from_pll;

wire feedback_clk;
wire fb_clkin;
wire fb_out_clk;
wire fboutclk_wire;
wire locked_wire;
wire [10:0] reconfig_from_pll_wire;
wire gnd /* synthesis keep*/;

// For use in dps pulse gen module. 
wire final_updn;
wire final_phase_en;
wire [3:0] final_cntsel;
wire [2:0] final_num_ps;
assign reconfig_from_pll[10:0] = reconfig_from_pll_wire;

wire adjpllin_wire = 1'b0;
wire dedicated_refclk_wire = 1'b0;
 
//Calibration wires
wire cal_ok_wire;

// Reset logic:

//Synchronise the reset signal using Flip-Flop to avoid race condition HSD : https://hsdes.intel.com/appstore/article/#/14021123640
// Uncomment the lines from 160 to 176 and comment lines 189 190 to workaround the race condition for FM87 
//
//
//reg cal_ok_wire_synced;
//
//always @ (posedge refclk or posedge rst) begin
//
//	if (rst) begin
//		cal_ok_wire_synced <= 1'b0;
//	end else begin
//		cal_ok_wire_synced <= cal_ok_wire;
//	end
//
//end
//
//wire rst_n_wire = ~((rst & cal_ok_wire_synced) | (~permit_cal));
//wire dprio_rst_n_wire = ~((~reconfig_to_pll[1] & cal_ok_wire_synced) | (~permit_cal));

// There are a few scenarios:
//  - Upstream PLL : 
//       - reset is anded with cal_ok_wire so that a reset signal from the
//         user can't interrupt calibration.
//       - permit_cal tied off to 1 -> rst_n_wire = ~(rst & cal_ok_wire)
//  - Downstream PLL: 
//       - connect upstream locked to downstream permit_cal
//       - until upstream PLL is locked, keep reset high so that the PLL
//         can't be calibrated.

// To get the FM hot potato passing temporarily skip cal_ok and permit_cal

//
//wire rst_n_wire = ~((rst & cal_ok_wire) | (~permit_cal));
//Removing cal_ok_wire support since its causing race condition in Hardware,
//Cal_ok_wire should not have a self loop happening and also got confirmation
//from PFE that this gating logic is handled within the Hardware HSD: 14021123640

wire rst_n_wire = ~(rst | (~permit_cal));
wire dprio_rst_n_wire = ~((~reconfig_to_pll[1] & cal_ok_wire) | (~permit_cal));


//------------- Counter enable localparams -------------------------------
localparam counter0_enable = "false";
localparam counter1_enable = "true";
localparam counter2_enable = "true";
localparam counter3_enable = "true";
localparam counter4_enable = "true";
localparam counter5_enable = "true";
localparam counter6_enable = "false";
localparam counter7_enable = "false";
localparam counter8_enable = "false";
//------------- Counter enable localparams -------------------------------


// ==========================================================================================
// Instantiate tennm_iopll!
// ==========================================================================================
tennm_iopll #(
    .auto_clk_sw_en("false"),
    .bw_mode("mid_bw"),
    .c0_bypass_en("true"),
    .c0_even_duty_en("false"),
    .c0_high(256),
    .c0_low(256),
    .c0_out_en(counter0_enable),
    .c0_ph_mux_prst(0),
    .c0_prst(1),
    .c1_bypass_en("false"),
    .c1_even_duty_en("true"),
    .c1_high(3),
    .c1_low(2),
    .c1_out_en(counter1_enable),
    .c1_ph_mux_prst(0),
    .c1_prst(1),
    .c2_bypass_en("false"),
    .c2_even_duty_en("false"),
    .c2_high(4),
    .c2_low(4),
    .c2_out_en(counter2_enable),
    .c2_ph_mux_prst(0),
    .c2_prst(1),
    .c3_bypass_en("false"),
    .c3_even_duty_en("true"),
    .c3_high(3),
    .c3_low(2),
    .c3_out_en(counter3_enable),
    .c3_ph_mux_prst(0),
    .c3_prst(1),
    .c4_bypass_en("false"),
    .c4_even_duty_en("false"),
    .c4_high(4),
    .c4_low(4),
    .c4_out_en(counter4_enable),
    .c4_ph_mux_prst(0),
    .c4_prst(3),
    .c5_bypass_en("false"),
    .c5_even_duty_en("false"),
    .c5_high(5),
    .c5_low(5),
    .c5_out_en(counter5_enable),
    .c5_ph_mux_prst(0),
    .c5_prst(1),
    .c6_bypass_en("true"),
    .c6_even_duty_en("false"),
    .c6_high(256),
    .c6_low(256),
    .c6_out_en(counter6_enable),
    .c6_ph_mux_prst(0),
    .c6_prst(1),
    .c7_bypass_en("true"),
    .c7_even_duty_en("false"),
    .c7_high(256),
    .c7_low(256),
    .c7_out_en(counter7_enable),
    .c7_ph_mux_prst(0),
    .c7_prst(1),
    .c8_bypass_en("true"),
    .c8_even_duty_en("false"),
    .c8_high(256),
    .c8_low(256),
    .c8_out_en(counter8_enable),
    .c8_ph_mux_prst(0),
    .c8_prst(1),
    .clkin_0_src("coreclkin"),
    .clkin_1_src("ioclkin_0"),
    .clock_name_0(""),
    .clock_name_1("outclk0"),
    .clock_name_2("outclk1"),
    .clock_name_3("outclk2"),
    .clock_name_4("outclk3"),
    .clock_name_5("outclk4"),
    .clock_name_6(""),
    .clock_name_7(""),
    .clock_name_8(""),
    .clock_name_global_0("false"),
    .clock_name_global_1("false"),
    .clock_name_global_2("false"),
    .clock_name_global_3("false"),
    .clock_name_global_4("false"),
    .clock_name_global_5("false"),
    .clock_name_global_6("false"),
    .clock_name_global_7("false"),
    .clock_name_global_8("false"),
    .clock_to_compensate(1),
    .duty_cycle_0(50),
    .duty_cycle_1(50),
    .duty_cycle_2(50),
    .duty_cycle_3(50),
    .duty_cycle_4(50),
    .duty_cycle_5(50),
    .duty_cycle_6(50),
    .duty_cycle_7(50),
    .duty_cycle_8(50),
    .extclk_0_cnt_src("pll_extclk_cnt_src_vss"),
    .extclk_0_enable("true"),
    .extclk_1_cnt_src("pll_extclk_cnt_src_vss"),
    .extclk_1_enable("true"),
    .feedback("direct"),
    .iopll_type("TOP_BOTTOM"),
    .m_counter_bypass_en("false"),
    .m_counter_even_duty_en("false"),
    .m_counter_high(5),
    .m_counter_low(5),
    .m_counter_scratch(1),
    .manu_clk_sw_en("false"),
    .merging_permitted("false"),
    .n_counter_bypass_en("true"),
    .n_counter_high(256),
    .n_counter_low(256),
    .n_counter_odd_div_duty_en("false"),
    .outclk0("0 ps"),
    .outclk1("200.0 MHz"),
    .outclk2("125.0 MHz"),
    .outclk3("200.0 MHz"),
    .outclk4("125.0 MHz"),
    .outclk5("100.0 MHz"),
    .outclk6("0 ps"),
    .outclk7("0 ps"),
    .outclk8("0 ps"),
    .pfd("100.0 MHz"),
    .phase_shift_0("0 ps"),
    .phase_shift_1("0 ps"),
    .phase_shift_2("0 ps"),
    .phase_shift_3("0 ps"),
    .phase_shift_4("2000 ps"),
    .phase_shift_5("0 ps"),
    .phase_shift_6("0 ps"),
    .phase_shift_7("0 ps"),
    .phase_shift_8("0 ps"),
    .prot_mode("BASIC"),
    .refclk_src_mux("clk_0"),
    .refclk_time("100.0 MHz"),
    .self_reset_en("false"),
    .simple_pll("false"),
    .uc_channel_base_addr(16'h0),
    .vco("1000.0 MHz")
) tennm_pll (
    .clken(2'b00),
    .cnt_sel(4'b0),
    .num_phase_shifts(3'b0),
    .phase_en(1'b0),
    .up_dn(1'b0),
    .dprio_clk(1'b0),
    .core_refclk(refclk),
    .csr_clk(1'b1),
    .csr_en(1'b1),
    .csr_in(1'b1),
    .dprio_rst_n(rst_n_wire),
    .dprio_address(9'b0),
    .read(1'b0),
    .write(1'b0),
    .writedata(8'b0),
    .pll_select_top_avl(1'b1), // Hardcoded to use the top PLL for now.
    .dps_rst_n(rst_n_wire),
    .extswitch(extswitch),
    .fbclk_in(1'b0),
    .fblvds_in(1'b0),
    .mdio_dis(1'b0),
    .pfden(1'b1),
    .pipeline_global_en_n(1'b0),
    .pll_cascade_in(adjpllin_wire),
    .pma_csr_test_dis(1'b1),
    .refclk({2'b0,refclk1, dedicated_refclk_wire}),
    .rst_n(rst_n_wire),
    .scan_mode_n(1'b1),
    .scan_shift_n(1'b1),
    .uc_cal_addr(20'b0),
    .uc_cal_clk(1'b0),
    .uc_cal_read(1'b0),
    .uc_cal_write(1'b0),
    .uc_cal_writedata(8'b0),
    .user_mode(1'b1),
    .zdb_in(1'b0),
    .block_select(),
    .clk0_bad(clkbad[0]),
    .clk1_bad(clkbad[1]),
    .clksel(activeclk),
    .csr_out(),
    .dll_output(dll_output),
    .extclk_dft(),
    .extclk_output({extclk_out_wire[1], fboutclk_wire}),
    .fbclk_out(feedback_clk),
    .fblvds_out(fblvds_out),
    .lf_reset(),
    .loaden(loaden),
    .lock(locked_wire),
    .lvds_clk(lvds_clk),
    .outclk(outclk),
    .phase_done(phase_done),
    .pll_cascade_out(cascade_out),
    .pll_pd(),
    .readdata(reconfig_from_pll_wire[7:0]),
    .vcop_en(),
    .vcoph(phout),
    .cal_ok(cal_ok_wire)
);
            
assign reconfig_from_pll_wire[8] = locked_wire;
assign reconfig_from_pll_wire[9] = phase_done;
assign reconfig_from_pll_wire[10] = cal_ok_wire;
assign extclk_out_wire[0] = fboutclk_wire;

assign fboutclk = fboutclk_wire;
assign locked = locked_wire;

// ==================================================================================
// Create clock buffers for fbclk,  fboutclk and zdbfbclk if necessary.
// ==================================================================================
assign zdbfbclk = 0;

endmodule


// =================================================================================
// The final_phase_en signal should be a signal pulse (there was a silicon bug
// involving this problem on Arria 10. DPS pulse gen generates a singe final_phase_en
// pulse when the user_phase_en goes high.
// It also delays the other signal by one clock cycle
// =================================================================================

module dps_pulse_gen_io_pll_altera_iopll_1931_oypl3jq (
    input  wire clk,            // the DPS clock
    input  wire rst,            // active high reset
    input  wire user_phase_en,  // the user's phase_en signal
    input  wire user_updn,     
    input  wire [2:0] user_num_ps,  
    input  wire [3:0] user_cntsel,  
    output reg  phase_en,        // the phase_en signal for the IOPLL atom
    output reg updn,     
    output reg [2:0] num_ps,  
    output reg [3:0] cntsel  
 );
 
    //-------------------------------------------------------------------------
    // States
    localparam IDLE        = 0,  // Idle state: user_phase_en = 0, phase_en = 0
               PULSE       = 1,  // Activate state: phase_en = 1
               WAIT        = 2;  // Wait for user_phase_en to go low

    //-------------------------------------------------------------------------
    // FSM current and next states
    reg [1:0] state, next;     
    
    // State update
    always @(posedge clk) begin
    
        updn <= user_updn;
        cntsel <= user_cntsel;
        num_ps <= user_num_ps;
    
        if (rst)    state <= IDLE;
        else        state <= next; 
    end  

    //-------------------------------------------------------------------------    
    // Next-state and output logic
    always @(*) begin
        next     = IDLE;  // Default next state 
        phase_en = 1'b0;  // Default output
        
        case (state)
            IDLE :  begin
                        if (user_phase_en)  next = PULSE;
                        else                next = IDLE;
                    end     
                         
            PULSE : begin
                        phase_en = 1'b1;
                        next     = WAIT;
                    end
                         
            WAIT :  begin         
                        if (~user_phase_en) next = IDLE;
                        else                next = WAIT;                  
                    end  
        endcase
    end
     
 endmodule


