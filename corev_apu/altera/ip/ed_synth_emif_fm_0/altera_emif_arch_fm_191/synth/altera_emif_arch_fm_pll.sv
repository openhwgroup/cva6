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


////////////////////////////////////////////////////////////////////////////////////////////////////////////
//  EMIF IOPLL instantiation for 20nm families
//
//  The following table describes the usage of IOPLL by EMIF.
//
//  PLL Counter    Fanouts                          Usage
//  =====================================================================================
//  VCO Outputs    vcoph[7:0] -> phy_clk_phs[7:0]   FR clocks, 8 phases (45-deg apart)
//                 vcoph[0] -> DLL                  FR clock to DLL
//  C-counter 0    lvds_clk[0] -> phy_clk[1]        Secondary PHY clock tree (C2P/P2C rate)
//  C-counter 1    loaden[0] -> phy_clk[0]          Primary PHY clock tree (PHY/HMC rate)
//  C-counter 2    phy_clk[2]                       Feedback PHY clock tree (slowest phy clock in system)
//
//
////////////////////////////////////////////////////////////////////////////////////////////////////////////

module altera_emif_arch_fm_pll #(
   parameter PORT_DFT_ND_PLL_CNTSEL_WIDTH            = 1,
   parameter PORT_DFT_ND_PLL_NUM_SHIFT_WIDTH         = 1,
   parameter PORT_DFT_ND_PLL_CORE_REFCLK_WIDTH       = 1,
   parameter PLL_REF_CLK_FREQ_PS_STR                 = "",
   parameter PLL_VCO_FREQ_PS_STR                     = "",
   parameter PLL_M_CNT_HIGH                          = 0,
   parameter PLL_M_CNT_LOW                           = 0,
   parameter PLL_N_CNT_HIGH                          = 0,
   parameter PLL_N_CNT_LOW                           = 0,
   parameter PLL_M_CNT_BYPASS_EN                     = "",
   parameter PLL_N_CNT_BYPASS_EN                     = "",
   parameter PLL_M_CNT_EVEN_DUTY_EN                  = "",
   parameter PLL_N_CNT_EVEN_DUTY_EN                  = "",
   parameter PLL_FBCLK_MUX_1                         = "",
   parameter PLL_FBCLK_MUX_2                         = "",
   parameter PLL_M_CNT_IN_SRC                        = "",
   parameter PLL_CP_SETTING                          = "",
   parameter PLL_BW_CTRL                             = "",
   parameter PLL_BW_SEL                              = "",
   parameter PLL_C_CNT_HIGH_0                        = 0,
   parameter PLL_C_CNT_LOW_0                         = 0,
   parameter PLL_C_CNT_PRST_0                        = 0,
   parameter PLL_C_CNT_PH_MUX_PRST_0                 = 0,
   parameter PLL_C_CNT_BYPASS_EN_0                   = "",
   parameter PLL_C_CNT_EVEN_DUTY_EN_0                = "",
   parameter PLL_C_CNT_HIGH_1                        = 0,
   parameter PLL_C_CNT_LOW_1                         = 0,
   parameter PLL_C_CNT_PRST_1                        = 0,
   parameter PLL_C_CNT_PH_MUX_PRST_1                 = 0,
   parameter PLL_C_CNT_BYPASS_EN_1                   = "",
   parameter PLL_C_CNT_EVEN_DUTY_EN_1                = "",
   parameter PLL_C_CNT_HIGH_2                        = 0,
   parameter PLL_C_CNT_LOW_2                         = 0,
   parameter PLL_C_CNT_PRST_2                        = 0,
   parameter PLL_C_CNT_PH_MUX_PRST_2                 = 0,
   parameter PLL_C_CNT_BYPASS_EN_2                   = "",
   parameter PLL_C_CNT_EVEN_DUTY_EN_2                = "",
   parameter PLL_C_CNT_HIGH_3                        = 0,
   parameter PLL_C_CNT_LOW_3                         = 0,
   parameter PLL_C_CNT_PRST_3                        = 0,
   parameter PLL_C_CNT_PH_MUX_PRST_3                 = 0,
   parameter PLL_C_CNT_BYPASS_EN_3                   = "",
   parameter PLL_C_CNT_EVEN_DUTY_EN_3                = "",
   parameter PLL_C_CNT_HIGH_4                        = 0,
   parameter PLL_C_CNT_LOW_4                         = 0,
   parameter PLL_C_CNT_PRST_4                        = 0,
   parameter PLL_C_CNT_PH_MUX_PRST_4                 = 0,
   parameter PLL_C_CNT_BYPASS_EN_4                   = "",
   parameter PLL_C_CNT_EVEN_DUTY_EN_4                = "",
   parameter PLL_C_CNT_HIGH_5                        = 0,
   parameter PLL_C_CNT_LOW_5                         = 0,
   parameter PLL_C_CNT_PRST_5                        = 0,
   parameter PLL_C_CNT_PH_MUX_PRST_5                 = 0,
   parameter PLL_C_CNT_BYPASS_EN_5                   = "",
   parameter PLL_C_CNT_EVEN_DUTY_EN_5                = "",
   parameter PLL_C_CNT_HIGH_6                        = 0,
   parameter PLL_C_CNT_LOW_6                         = 0,
   parameter PLL_C_CNT_PRST_6                        = 0,
   parameter PLL_C_CNT_PH_MUX_PRST_6                 = 0,
   parameter PLL_C_CNT_BYPASS_EN_6                   = "",
   parameter PLL_C_CNT_EVEN_DUTY_EN_6                = "",
   parameter PLL_C_CNT_HIGH_7                        = 0,
   parameter PLL_C_CNT_LOW_7                         = 0,
   parameter PLL_C_CNT_PRST_7                        = 0,
   parameter PLL_C_CNT_PH_MUX_PRST_7                 = 0,
   parameter PLL_C_CNT_BYPASS_EN_7                   = "",
   parameter PLL_C_CNT_EVEN_DUTY_EN_7                = "",
   parameter PLL_C_CNT_HIGH_8                        = 0,
   parameter PLL_C_CNT_LOW_8                         = 0,
   parameter PLL_C_CNT_PRST_8                        = 0,
   parameter PLL_C_CNT_PH_MUX_PRST_8                 = 0,
   parameter PLL_C_CNT_BYPASS_EN_8                   = "",
   parameter PLL_C_CNT_EVEN_DUTY_EN_8                = "",
   parameter PLL_C_CNT_FREQ_PS_STR_0                 = "",
   parameter PLL_C_CNT_PHASE_PS_STR_0                = "",
   parameter PLL_C_CNT_DUTY_CYCLE_0                  = 0,
   parameter PLL_C_CNT_FREQ_PS_STR_1                 = "",
   parameter PLL_C_CNT_PHASE_PS_STR_1                = "",
   parameter PLL_C_CNT_DUTY_CYCLE_1                  = 0,
   parameter PLL_C_CNT_FREQ_PS_STR_2                 = "",
   parameter PLL_C_CNT_PHASE_PS_STR_2                = "",
   parameter PLL_C_CNT_DUTY_CYCLE_2                  = 0,
   parameter PLL_C_CNT_FREQ_PS_STR_3                 = "",
   parameter PLL_C_CNT_PHASE_PS_STR_3                = "",
   parameter PLL_C_CNT_DUTY_CYCLE_3                  = 0,
   parameter PLL_C_CNT_FREQ_PS_STR_4                 = "",
   parameter PLL_C_CNT_PHASE_PS_STR_4                = "",
   parameter PLL_C_CNT_DUTY_CYCLE_4                  = 0,
   parameter PLL_C_CNT_FREQ_PS_STR_5                 = "",
   parameter PLL_C_CNT_PHASE_PS_STR_5                = "",
   parameter PLL_C_CNT_DUTY_CYCLE_5                  = 0,
   parameter PLL_C_CNT_FREQ_PS_STR_6                 = "",
   parameter PLL_C_CNT_PHASE_PS_STR_6                = "",
   parameter PLL_C_CNT_DUTY_CYCLE_6                  = 0,
   parameter PLL_C_CNT_FREQ_PS_STR_7                 = "",
   parameter PLL_C_CNT_PHASE_PS_STR_7                = "",
   parameter PLL_C_CNT_DUTY_CYCLE_7                  = 0,
   parameter PLL_C_CNT_FREQ_PS_STR_8                 = "",
   parameter PLL_C_CNT_PHASE_PS_STR_8                = "",
   parameter PLL_C_CNT_DUTY_CYCLE_8                  = 0,
   parameter PLL_C_CNT_OUT_EN_0                      = "",
   parameter PLL_C_CNT_OUT_EN_1                      = "",
   parameter PLL_C_CNT_OUT_EN_2                      = "",
   parameter PLL_C_CNT_OUT_EN_3                      = "",
   parameter PLL_C_CNT_OUT_EN_4                      = "",
   parameter PLL_C_CNT_OUT_EN_5                      = "",
   parameter PLL_C_CNT_OUT_EN_6                      = "",
   parameter PLL_C_CNT_OUT_EN_7                      = "",
   parameter PLL_C_CNT_OUT_EN_8                      = "",

   parameter PLL_REF_CLK_FREQ_MHZ_STR                = "",
   parameter PLL_VCO_FREQ_MHZ_STR                    = "",
   parameter PLL_C_CNT_FREQ_MHZ_STR_0                = "",
   parameter PLL_C_CNT_FREQ_MHZ_STR_1                = "",
   parameter PLL_C_CNT_FREQ_MHZ_STR_2                = "",
   parameter PLL_C_CNT_FREQ_MHZ_STR_3                = "",
   parameter PLL_C_CNT_FREQ_MHZ_STR_4                = "",
   parameter PLL_C_CNT_FREQ_MHZ_STR_5                = "",
   parameter PLL_C_CNT_FREQ_MHZ_STR_6                = "",
   parameter PLL_C_CNT_FREQ_MHZ_STR_7                = "",
   parameter PLL_C_CNT_FREQ_MHZ_STR_8                = "",
   parameter IS_HPS                                  = 0

) (
   input  logic                                               pll_ref_clk_int,       
   output logic                                               pll_locked,            
   output logic                                               pll_dll_clk,           
   output logic [7:0]                                         phy_clk_phs,           
   output logic [1:0]                                         phy_clk,               
   output logic                                               phy_fb_clk_to_tile,    
   input  logic                                               phy_fb_clk_to_pll,     
   output logic [8:0]                                         pll_c_counters,        
   input  logic                                               pll_phase_en,          
   input  logic                                               pll_up_dn,             
   input  logic [PORT_DFT_ND_PLL_CNTSEL_WIDTH-1:0]            pll_cnt_sel,           
   input  logic [PORT_DFT_ND_PLL_NUM_SHIFT_WIDTH-1:0]         pll_num_phase_shifts,  
   output logic                                               pll_phase_done,        
   input  logic [PORT_DFT_ND_PLL_CORE_REFCLK_WIDTH-1:0]       pll_core_refclk        
);
   timeunit 1ns;
   timeprecision 1ps;

   logic [7:0]        pll_vcoph;              
   logic [1:0]        pll_loaden;             
   logic [1:0]        pll_lvds_clk;           

   assign phy_clk_phs  = pll_vcoph;

   assign phy_clk[0]   = pll_loaden[0];       // C-cnt 1 drives phy_clk 0 through a delay chain (swapping is intentional)
   assign phy_clk[1]   = pll_lvds_clk[0];     // C-cnt 0 drives phy_clk 1 through a delay chain (swapping is intentional)

`ifdef ALTERA_EMIF_ENABLE_ISSP
   generate
      if (IS_HPS == 0) begin : non_hps
         altsource_probe #(
          .sld_auto_instance_index ("YES"),
          .sld_instance_index      (0),
		      .instance_id             ("PLLL"),
		      .probe_width             (1),
		      .source_width            (0),
		      .source_initial_value    ("0"),
      		.enable_metastability    ("NO")
      	) pll_lock_issp (
      		.probe  (pll_locked)
      	);
      end
   endgenerate
`endif

   tennm_iopll # (

      ////////////////////////////////////
      //  VCO and Ref clock
      //  fVCO = fRefClk * M * CCnt2 / N
      ////////////////////////////////////
      .prot_mode                                  ("emif_mode"),
      .refclk_time                                (PLL_REF_CLK_FREQ_PS_STR), 
      .vco                                        (PLL_VCO_FREQ_PS_STR),     

      // : N_CNT_BYPASS_EN is always on which means pfd_freq == ref_clk_freq / 1
      .pfd                                        (PLL_REF_CLK_FREQ_PS_STR), 

      ////////////////////////////////////
      //  M Counter
      ////////////////////////////////////
      .m_counter_bypass_en                    (PLL_M_CNT_BYPASS_EN),
      .m_counter_even_duty_en                 (PLL_M_CNT_EVEN_DUTY_EN),
      .m_counter_high                         (PLL_M_CNT_HIGH),
      .m_counter_low                          (PLL_M_CNT_LOW),
      .m_counter_coarse_dly                   ("0 ps"),
      .m_counter_fine_dly                     ("0 ps"),

      ////////////////////////////////////
      //  N Counter (bypassed)
      ////////////////////////////////////
      .n_counter_bypass_en                    (PLL_N_CNT_BYPASS_EN),
      .n_counter_odd_div_duty_en              (PLL_N_CNT_EVEN_DUTY_EN),
      .n_counter_high                         (PLL_N_CNT_HIGH),
      .n_counter_low                          (PLL_N_CNT_LOW),
      .n_counter_coarse_dly                   ("0 ps"),
      .n_counter_fine_dly                     ("0 ps"),

      ////////////////////////////////////
      //  C Counter 0 (phy_clk[1])
      ////////////////////////////////////
      .c0_out_en                                  (PLL_C_CNT_OUT_EN_0),                      // C-counter driving phy_clk[1]
      .outclk0                                    (PLL_C_CNT_FREQ_PS_STR_0),
      .phase_shift_0                              (PLL_C_CNT_PHASE_PS_STR_0),
      .duty_cycle_0                               (PLL_C_CNT_DUTY_CYCLE_0),
      .c0_bypass_en                               (PLL_C_CNT_BYPASS_EN_0),
      .c0_even_duty_en                            (PLL_C_CNT_EVEN_DUTY_EN_0),
      .c0_high                                    (PLL_C_CNT_HIGH_0),
      .c0_low                                     (PLL_C_CNT_LOW_0),
      .c0_ph_mux_prst                             (PLL_C_CNT_PH_MUX_PRST_0),
      .c0_prst                                    (PLL_C_CNT_PRST_0),
      .c0_coarse_dly                              ("0 ps"),
      .c0_fine_dly                                ("0 ps"),

      ////////////////////////////////////
      //  C Counter 1 (phy_clk[0])
      ////////////////////////////////////
      .c1_out_en                                  (PLL_C_CNT_OUT_EN_1),                      // C-counter driving phy_clk[0]
      .outclk1                                    (PLL_C_CNT_FREQ_PS_STR_1),
      .phase_shift_1                              (PLL_C_CNT_PHASE_PS_STR_1),
      .duty_cycle_1                               (PLL_C_CNT_DUTY_CYCLE_1),
      .c1_bypass_en                               (PLL_C_CNT_BYPASS_EN_1),
      .c1_even_duty_en                            (PLL_C_CNT_EVEN_DUTY_EN_1),
      .c1_high                                    (PLL_C_CNT_HIGH_1),
      .c1_low                                     (PLL_C_CNT_LOW_1),
      .c1_ph_mux_prst                             (PLL_C_CNT_PH_MUX_PRST_1),
      .c1_prst                                    (PLL_C_CNT_PRST_1),
      .c1_coarse_dly                              ("0 ps"),
      .c1_fine_dly                                ("0 ps"),

      ////////////////////////////////////
      //  C Counter 2 (phy_clk[2])
      ////////////////////////////////////
      .c2_out_en                                  (PLL_C_CNT_OUT_EN_2),                      // C-counter driving phy_clk[2]
      .outclk2                                    (PLL_C_CNT_FREQ_PS_STR_2),
      .phase_shift_2                              (PLL_C_CNT_PHASE_PS_STR_2),
      .duty_cycle_2                               (PLL_C_CNT_DUTY_CYCLE_2),
      .c2_bypass_en                               (PLL_C_CNT_BYPASS_EN_2),
      .c2_even_duty_en                            (PLL_C_CNT_EVEN_DUTY_EN_2),
      .c2_high                                    (PLL_C_CNT_HIGH_2),
      .c2_low                                     (PLL_C_CNT_LOW_2),
      .c2_ph_mux_prst                             (PLL_C_CNT_PH_MUX_PRST_2),
      .c2_prst                                    (PLL_C_CNT_PRST_2),
      .c2_coarse_dly                              ("0 ps"),
      .c2_fine_dly                                ("0 ps"),

      ////////////////////////////////////
      //  C Counter 3 (unused)
      ////////////////////////////////////
      .c3_out_en                                  (PLL_C_CNT_OUT_EN_3),                         // Not used by EMIF
      .outclk3                                    (PLL_C_CNT_FREQ_PS_STR_3),
      .phase_shift_3                              (PLL_C_CNT_PHASE_PS_STR_3),
      .duty_cycle_3                               (PLL_C_CNT_DUTY_CYCLE_3),
      .c3_bypass_en                               (PLL_C_CNT_BYPASS_EN_3),
      .c3_even_duty_en                            (PLL_C_CNT_EVEN_DUTY_EN_3),
      .c3_high                                    (PLL_C_CNT_HIGH_3),
      .c3_low                                     (PLL_C_CNT_LOW_3),
      .c3_ph_mux_prst                             (PLL_C_CNT_PH_MUX_PRST_3),
      .c3_prst                                    (PLL_C_CNT_PRST_3),
      .c3_coarse_dly                              ("0 ps"),
      .c3_fine_dly                                ("0 ps"),

      ////////////////////////////////////
      //  C Counter 4 (unused)
      ////////////////////////////////////
      .c4_out_en                                  (PLL_C_CNT_OUT_EN_4),                         // Not used by EMIF
      .outclk4                                    (PLL_C_CNT_FREQ_PS_STR_4),
      .phase_shift_4                              (PLL_C_CNT_PHASE_PS_STR_4),
      .duty_cycle_4                               (PLL_C_CNT_DUTY_CYCLE_4),
      .c4_bypass_en                               (PLL_C_CNT_BYPASS_EN_4),
      .c4_even_duty_en                            (PLL_C_CNT_EVEN_DUTY_EN_4),
      .c4_high                                    (PLL_C_CNT_HIGH_4),
      .c4_low                                     (PLL_C_CNT_LOW_4),
      .c4_ph_mux_prst                             (PLL_C_CNT_PH_MUX_PRST_4),
      .c4_prst                                    (PLL_C_CNT_PRST_4),
      .c4_coarse_dly                              ("0 ps"),
      .c4_fine_dly                                ("0 ps"),

      ////////////////////////////////////
      //  C Counter 5 (unused)
      ////////////////////////////////////
      .c5_out_en                                  (PLL_C_CNT_OUT_EN_5),                         // Not used by EMIF
      .outclk5                                    (PLL_C_CNT_FREQ_PS_STR_5),
      .phase_shift_5                              (PLL_C_CNT_PHASE_PS_STR_5),                   // Don't care (unused c-counter)
      .duty_cycle_5                               (PLL_C_CNT_DUTY_CYCLE_5),                     // Don't care (unused c-counter)
      .c5_bypass_en                               (PLL_C_CNT_BYPASS_EN_5),                      // Don't care (unused c-counter)
      .c5_even_duty_en                            (PLL_C_CNT_EVEN_DUTY_EN_5),                   // Don't care (unused c-counter)
      .c5_high                                    (PLL_C_CNT_HIGH_5),                           // Don't care (unused c-counter)
      .c5_low                                     (PLL_C_CNT_LOW_5),                            // Don't care (unused c-counter)
      .c5_ph_mux_prst                             (PLL_C_CNT_PH_MUX_PRST_5),                    // Don't care (unused c-counter)
      .c5_prst                                    (PLL_C_CNT_PRST_5),                           // Don't care (unused c-counter)
      .c5_coarse_dly                              ("0 ps"),                                     // Don't care (unused c-counter)
      .c5_fine_dly                                ("0 ps"),                                     // Don't care (unused c-counter)

      ////////////////////////////////////
      //  C Counter 6 (unused)
      ////////////////////////////////////
      .c6_out_en                                  (PLL_C_CNT_OUT_EN_6),                         // Not used by EMIF
      .outclk6                                    (PLL_C_CNT_FREQ_PS_STR_6),
      .phase_shift_6                              (PLL_C_CNT_PHASE_PS_STR_6),                   // Don't care (unused c-counter)
      .duty_cycle_6                               (PLL_C_CNT_DUTY_CYCLE_6),                     // Don't care (unused c-counter)
      .c6_bypass_en                               (PLL_C_CNT_BYPASS_EN_6),                      // Don't care (unused c-counter)
      .c6_even_duty_en                            (PLL_C_CNT_EVEN_DUTY_EN_6),                   // Don't care (unused c-counter)
      .c6_high                                    (PLL_C_CNT_HIGH_6),                           // Don't care (unused c-counter)
      .c6_low                                     (PLL_C_CNT_LOW_6),                            // Don't care (unused c-counter)
      .c6_ph_mux_prst                             (PLL_C_CNT_PH_MUX_PRST_6),                    // Don't care (unused c-counter)
      .c6_prst                                    (PLL_C_CNT_PRST_6),                           // Don't care (unused c-counter)
      .c6_coarse_dly                              ("0 ps"),                                     // Don't care (unused c-counter)
      .c6_fine_dly                                ("0 ps"),                                     // Don't care (unused c-counter)

      ////////////////////////////////////
      //  C Counter 7 (unused)
      ////////////////////////////////////
      .c7_out_en                                  (PLL_C_CNT_OUT_EN_7),                         // Not used by EMIF
      .outclk7                                    (PLL_C_CNT_FREQ_PS_STR_7),
      .phase_shift_7                              (PLL_C_CNT_PHASE_PS_STR_7),                   // Don't care (unused c-counter)
      .duty_cycle_7                               (PLL_C_CNT_DUTY_CYCLE_7),                     // Don't care (unused c-counter)
      .c7_bypass_en                               (PLL_C_CNT_BYPASS_EN_7),                      // Don't care (unused c-counter)
      .c7_even_duty_en                            (PLL_C_CNT_EVEN_DUTY_EN_7),                   // Don't care (unused c-counter)
      .c7_high                                    (PLL_C_CNT_HIGH_7),                           // Don't care (unused c-counter)
      .c7_low                                     (PLL_C_CNT_LOW_7),                            // Don't care (unused c-counter)
      .c7_ph_mux_prst                             (PLL_C_CNT_PH_MUX_PRST_7),                    // Don't care (unused c-counter)
      .c7_prst                                    (PLL_C_CNT_PRST_7),                           // Don't care (unused c-counter)
      .c7_coarse_dly                              ("0 ps"),                                     // Don't care (unused c-counter)
      .c7_fine_dly                                ("0 ps"),                                     // Don't care (unused c-counter)

      ////////////////////////////////////
      //  C Counter 8 (unused)
      ////////////////////////////////////
      .c8_out_en                                  (PLL_C_CNT_OUT_EN_8),                         // Not used by EMIF
      .outclk8                                    (PLL_C_CNT_FREQ_PS_STR_8),
      .phase_shift_8                              (PLL_C_CNT_PHASE_PS_STR_8),                   // Don't care (unused c-counter)
      .duty_cycle_8                               (PLL_C_CNT_DUTY_CYCLE_8),                     // Don't care (unused c-counter)
      .c8_bypass_en                               (PLL_C_CNT_BYPASS_EN_8),                      // Don't care (unused c-counter)
      .c8_even_duty_en                            (PLL_C_CNT_EVEN_DUTY_EN_8),                   // Don't care (unused c-counter)
      .c8_high                                    (PLL_C_CNT_HIGH_8),                           // Don't care (unused c-counter)
      .c8_low                                     (PLL_C_CNT_LOW_8),                            // Don't care (unused c-counter)
      .c8_ph_mux_prst                             (PLL_C_CNT_PH_MUX_PRST_8),                    // Don't care (unused c-counter)
      .c8_prst                                    (PLL_C_CNT_PRST_8),                           // Don't care (unused c-counter)
      .c8_coarse_dly                              ("0 ps"),                                     // Don't care (unused c-counter)
      .c8_fine_dly                                ("0 ps"),                                     // Don't care (unused c-counter)

      ////////////////////////////////////
      //  Misc Delay Chains
      ////////////////////////////////////
      .ref_buf_dly                                ("0 ps"),
      .cmp_buf_dly                                ("0 ps"),

      .lvdsclk_0_coarse_dly                       ("0 ps"),                        // Fine delay chain to skew phyclk[0]
      .loaden_0_coarse_dly                        ("0 ps"),                        // Fine delay chain to skew phyclk[1]
      .lvdsclk_1_coarse_dly                       ("0 ps"),                        // Fine delay chain to skew phyclk[2]
      .loaden_1_coarse_dly                        ("0 ps"),                        // Fine delay chain to skew phyclk[3]

      .lvdsclk_0_fine_dly                         ("0 ps"),                        // Fine delay chain to skew phyclk[0]
      .loaden_0_fine_dly                          ("0 ps"),                        // Fine delay chain to skew phyclk[1]
      .lvdsclk_1_fine_dly                         ("0 ps"),                        // Fine delay chain to skew phyclk[2]
      .loaden_1_fine_dly                          ("0 ps"),                        // Fine delay chain to skew phyclk[3]

      ////////////////////////////////////
      //  Misc PLL Modes and Features
      ////////////////////////////////////
      .feedback                                   ("direct"),                      // EMIF doesn't need PLL compensation. Alignment of core clocks and PHY clocks is handled by CPA

      .extclk_0_enable                            ("false"),                       // EMIF PLL does not need to drive output clock pin
      .extclk_1_enable                            ("false"),                       // EMIF PLL does not need to drive output clock pin

      .clkin_0_src                                ("refclkin"),                    //
      .clkin_1_src                                ("refclkin"),                    //
      .refclk_src_mux                             ("clk_0"),                       //
      .auto_clk_sw_en                             ("false"),                       // EMIF PLL does not use the automatic clock switch-over feature
      .manu_clk_sw_en                             ("false"),                       // EMIF PLL does not use the automatic clock switch-over feature
      .merging_permitted                          ("true"),

      .bw_mode                                    ("hi_bw"),                       // Bandwidth select
      .lock_mode                                  ("low_lock_time"),               //__ACDS_USER_COMMNET__ lock_fltr_cfg 100 => "low_lock_time"

      ////////////////////////////////////
      //  To enable PLL calibration
      ////////////////////////////////////
      .uc_channel_base_addr(16'h0)

   ) pll_inst (

      .refclk                                     (pll_core_refclk),
      .rst_n                                      (1'b1),
      .loaden                                     (pll_loaden),
      .lvds_clk                                   (pll_lvds_clk),
      .vcoph                                      (pll_vcoph),
      .fblvds_in                                  (),
      .fblvds_out                                 (phy_fb_clk_to_tile),
      .dll_output                                 (pll_dll_clk),
      .lock                                       (pll_locked),
      .outclk                                     (pll_c_counters),
      .fbclk_in                                   (1'b0),
      .fbclk_out                                  (),
      .zdb_in                                     (1'b0),
      .phase_done                                 (pll_phase_done),
      .pll_cascade_in                             (pll_ref_clk_int),
      .pll_cascade_out                            (),
      .extclk_output                              (),
      .core_refclk                                (1'b0),
      .dps_rst_n                                  (1'b1),
      .mdio_dis                                   (1'b0),
      .pfden                                      (1'b1),
      .phase_en                                   (pll_phase_en),
      .pma_csr_test_dis                           (1'b1),
      .up_dn                                      (pll_up_dn),
      .extswitch                                  (1'b0),
      .clken                                      (2'b00),                            // Don't care (extclk)
      .cnt_sel                                    (pll_cnt_sel),
      .num_phase_shifts                           (pll_num_phase_shifts),
      .clk0_bad                                   (),
      .clk1_bad                                   (),
      .clksel                                     (),
      .csr_clk                                    (1'b1),
      .csr_en                                     (1'b1),
      .csr_in                                     (1'b1),
      .csr_out                                    (),
      .dprio_clk                                  (1'b0),
      .dprio_rst_n                                (1'b1),
      .dprio_address                              (9'b000000000),
      .scan_mode_n                                (1'b1),
      .scan_shift_n                               (1'b1),
      .write                                      (1'b0),
      .read                                       (1'b0),
      .readdata                                   (),
      .writedata                                  (8'b00000000),
      .extclk_dft                                 (),
      .block_select                               (),
      .lf_reset                                   (),
      .pipeline_global_en_n                       (),
      .pll_pd                                     (),
      .vcop_en                                    (),
      .user_mode                                  (1'b1)
   );

endmodule
`ifdef QUESTA_INTEL_OEM
`pragma questa_oem_00 "EVeqkz9MvDzapiiVw7+udc++m43wu2P9R6Bkf/lfBn9ZttFzW71hzuu9P3yzPlvUUu1GESHEht8oUjkuxH5nYF5m2Y4yEaZOsor1W+qakklkcNM5gczDB8G/zUljAitcohcjlH9xX4F5r3RrLLQB1HrtXmnxKKrsVs2RsxKt4plRYJGUCxRjs6twKgr6lps1q22taZT7+7dZh7dYE0uKJfWB1PYeKR+rbOxvrAyMNm03/adeGfDnFvYrNFWP5b8KM0itmRZy+oB2JIV75ZMQZ1Tl7D0v4ikMe4xrpBpHUqXrV6jfjk0S7/nPE5IHNjYoNf5avFRpXLhXEFEv7vQrKo+Mg8KSKPQpX69tC7xEBelATHHx1TnRmQ7hA4jq+ThXSOxg+zToL8I3CnGhM2YYNGzaMUCxRuCSuPYVnP8mQlOdwf6mpNtx5deyV0S3rgLyGKrwhT+BRQ/pSvTyAI8dRjGQtzTTS0reTJp1Rt12sA/dAgr4SQA6V2iVzPqSg7JbGr01eXiFQIxI7nRp1wpeJVPdodOTFPj/3qBh/Un6qYhIlJcEyrd+fWcsEHoMK0zgSk5DHZ3tMEdtISaBSi3KGNe9EiVnV9KXHKQzL9aPv5Xego52m5YfN4AEuhrMNf2Th8GG1d7V8yEjpaclbedNfQlyIX87xgH7xhj9GBflSSzleMgrdzwa6Ogxs1Y8oA4O+lv6r/K1QxoCVTKS2PQ2GTmm0UXLGrDiTRNzv8CtcMahM+awrFJLuVfySUj5KXpwapBlvYJvtBqeZPWfPG7kBxfCd2Uv6l8b9Po6GnlQR9fheSvE4gmTPgCeh0Y7PC7hDzF/2bHQkBKGVvnwHgtdDBUtwQZPr6YzHpiy9IWyDakBxfABq9NhwMvwGVgikZxV5u6hIto8+qdIh/orxu1MA/fIcshm67Bae9cOn6VZE1dloaYHyBrYM9maLMMimc3tdPyWxt8KHSg/IYwaayAznD5bJQNAdVJrhPTyJTOSNUJqNjfd26wXn/XtyTu5xFxv"
`endif