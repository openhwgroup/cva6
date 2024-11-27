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
module altera_emif_arch_fm_pll_fast_sim #(
   parameter PLL_SIM_VCO_FREQ_PS                     = 0,
   parameter PLL_SIM_PHYCLK_0_FREQ_PS                = 0,
   parameter PLL_SIM_PHYCLK_1_FREQ_PS                = 0,
   parameter PLL_SIM_PHYCLK_FB_FREQ_PS               = 0,
   parameter PLL_SIM_PHY_CLK_VCO_PHASE_PS            = 0,
   parameter PORT_DFT_ND_PLL_CNTSEL_WIDTH            = 1,
   parameter PORT_DFT_ND_PLL_NUM_SHIFT_WIDTH         = 1,
   parameter PORT_DFT_ND_PLL_CORE_REFCLK_WIDTH       = 1
   
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
   timeunit 1ps;
   timeprecision 1ps;

   localparam VCO_PHASES = 8;

   reg vco_out, phyclk0_out, phyclk1_out, fbclk_out;
   reg [4:0] pll_lock_count;
   // synthesis translate_off
   initial begin
      vco_out <= 1'b1;
      forever #(PLL_SIM_VCO_FREQ_PS/2) vco_out <= ~vco_out;
   end
   initial begin
      phyclk0_out <= 1'b1;
      #(PLL_SIM_VCO_FREQ_PS*PLL_SIM_PHY_CLK_VCO_PHASE_PS/VCO_PHASES);
      forever #(PLL_SIM_PHYCLK_0_FREQ_PS/2) phyclk0_out <= ~phyclk0_out;
   end
   initial begin
      phyclk1_out <= 1'b1;
      #(PLL_SIM_VCO_FREQ_PS*PLL_SIM_PHY_CLK_VCO_PHASE_PS/VCO_PHASES);
      forever #(PLL_SIM_PHYCLK_1_FREQ_PS/2) phyclk1_out <= ~phyclk1_out;
   end
   initial begin
      fbclk_out <= 1'b1;
      #(PLL_SIM_VCO_FREQ_PS*PLL_SIM_PHY_CLK_VCO_PHASE_PS/VCO_PHASES);
      forever #(PLL_SIM_PHYCLK_FB_FREQ_PS/2) fbclk_out <= ~fbclk_out;
   end

   initial begin
      pll_lock_count <= 5'b0;
   end
   // synthesis translate_on
   
   always @ (posedge vco_out) begin
      if (pll_lock_count != 5'b11111) begin
         pll_lock_count <= pll_lock_count + 1;
      end
   end

   assign pll_locked = (pll_lock_count == 5'b11111);
   assign pll_dll_clk = pll_locked & vco_out;
   assign phy_clk_phs[0] = pll_locked & vco_out;
   always @ (*) begin
      phy_clk_phs[1] <= #(PLL_SIM_VCO_FREQ_PS/VCO_PHASES) phy_clk_phs[0];
      phy_clk_phs[2] <= #(PLL_SIM_VCO_FREQ_PS/VCO_PHASES) phy_clk_phs[1];
      phy_clk_phs[3] <= #(PLL_SIM_VCO_FREQ_PS/VCO_PHASES) phy_clk_phs[2];
      phy_clk_phs[4] <= #(PLL_SIM_VCO_FREQ_PS/VCO_PHASES) phy_clk_phs[3];
      phy_clk_phs[5] <= #(PLL_SIM_VCO_FREQ_PS/VCO_PHASES) phy_clk_phs[4];
      phy_clk_phs[6] <= #(PLL_SIM_VCO_FREQ_PS/VCO_PHASES) phy_clk_phs[5];
      phy_clk_phs[7] <= #(PLL_SIM_VCO_FREQ_PS/VCO_PHASES) phy_clk_phs[6];
   end
   assign phy_clk = {pll_locked & phyclk1_out, pll_locked & phyclk0_out};
   assign phy_fb_clk_to_tile = pll_locked & fbclk_out;
   assign pll_c_counters[0] =  pll_locked & phyclk1_out; 
   assign pll_c_counters[1] =  pll_locked & phyclk0_out;
   assign pll_c_counters[2] =  pll_locked & fbclk_out;
   assign pll_c_counters[8:3] = 6'd0;
   assign pll_phase_done = 1'b1;

endmodule
`ifdef QUESTA_INTEL_OEM
`pragma questa_oem_00 "EVeqkz9MvDzapiiVw7+udc++m43wu2P9R6Bkf/lfBn9ZttFzW71hzuu9P3yzPlvUUu1GESHEht8oUjkuxH5nYF5m2Y4yEaZOsor1W+qakklkcNM5gczDB8G/zUljAitcohcjlH9xX4F5r3RrLLQB1HrtXmnxKKrsVs2RsxKt4plRYJGUCxRjs6twKgr6lps1q22taZT7+7dZh7dYE0uKJfWB1PYeKR+rbOxvrAyMNm3BGXk9lUcm5RF8HkFXhW2IR5/x+h8T5PbKTqwuwhus1/PoXI0qiAFflw54MC3ilxDPX80k62rh2cYxlerC4ZmDfBW+AOOM6AeHpIuZZWUvyPWYWXWrivxWPneu9rYZ2WrnHdZaQJpueIIQKhFVanmu0CdggAbNdVWGkffyupL0hJ2ZXdoiMn7ro+63lDA0Y1cE0pkahmZa2BD94Ih3FeHJSDmTmUnprODmyptruZuWjNzca0WZ99JaABDaU1De7O00OrFojm2rNW9D8FMfoeiVrsoGXOQiq6nF+rCQCPXvCRVjRQL2WR7SwJuFTMfCkxYt/p3gamgN1pQi6e4v1BU5cVfe895AiYHwmu+of3gtCzhVtHwvvsbJcU+iHZID4Oy8skadjkfj5VfopXg+q4WThbsBpevH2svYAJtqw735zAaP3yr8xTqf+B5y4mkbJM+Va2uyMLbKNfYyT6WVIH37gp7W6IZOVRfO0d+EAX3viymgSnc04cUmChs22J67SKR3NB4goS/+wvbMA8AfbDrtFNucsatvj+D4PK0jydwxQSwduLOlv/WWy8tMh55u9zpYYqrP883sUN+sO2NsQTEYNfCqDU0gOFl7HYK8Gc1t9M/4kmKPKXbvurDkVKAAS/oZfXZ+PZ0GqQgsbRm02JxXAq+hWuHwbIOJuSphyNSs65rF3/8E5JROZ53Ezii4rvOlHVWeDdBnkPjJlHnhS1UVrNVW8bQfEhgp1rS9u1YAZ041Tnh+zHgS/Jf/+XKkklzfi+7HnyYffrIKaVhJ4NSt"
`endif