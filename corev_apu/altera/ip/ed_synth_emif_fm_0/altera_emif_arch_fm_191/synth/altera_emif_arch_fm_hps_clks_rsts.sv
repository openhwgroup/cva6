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
// This module handles the creation and wiring of the HPS clock/reset signals.
//
///////////////////////////////////////////////////////////////////////////////

// altera message_off 10036

 module altera_emif_arch_fm_hps_clks_rsts #(
   parameter PORT_CLKS_SHARING_MASTER_OUT_WIDTH      = 32,
   parameter PORT_CLKS_SHARING_SLAVE_IN_WIDTH        = 32,
   parameter PORT_DFT_ND_CORE_CLK_BUF_OUT_WIDTH      = 1,
   parameter PORT_DFT_ND_CORE_CLK_LOCKED_WIDTH       = 1,
   parameter PORT_HPS_EMIF_H2E_GP_WIDTH              = 1
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
   
   // Feedback signals to CPA via the core
   output logic [1:0]                                           core_clks_fb_to_cpa_pri,
   output logic [1:0]                                           core_clks_fb_to_cpa_sec,
   
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
   
   // HPS clocks are not modeled for simulation.
   // Also in HPS mode we do not generate clocks that are visible to user logic.
   assign pll_ref_clk_int    = pll_ref_clk;
   
   // Reset request is not supported by HPS EMIF.
   // HPS EMIF has its own way of reset request mechanism.
   assign local_reset_req_int     = 1'b0;

   assign afi_clk                 = 1'b0;
   assign afi_half_clk            = 1'b0;
   assign afi_reset_n             = 1'b1;
   
   assign emif_usr_clk            = 1'b0;
   assign emif_usr_half_clk       = 1'b0;
   assign emif_usr_reset_n        = 1'b1;
   
   assign emif_usr_clk_sec        = 1'b0;
   assign emif_usr_half_clk_sec   = 1'b0;
   assign emif_usr_reset_n_sec    = 1'b1;
   
   assign core_clks_fb_to_cpa_pri = '0;
   assign core_clks_fb_to_cpa_sec = '0;
   assign clks_sharing_master_out = '0;
   
   assign dft_core_clk_locked     = '0;
   assign dft_core_clk_buf_out    = '0;
   
endmodule
`ifdef QUESTA_INTEL_OEM
`pragma questa_oem_00 "EVeqkz9MvDzapiiVw7+udc++m43wu2P9R6Bkf/lfBn9ZttFzW71hzuu9P3yzPlvUUu1GESHEht8oUjkuxH5nYF5m2Y4yEaZOsor1W+qakklkcNM5gczDB8G/zUljAitcohcjlH9xX4F5r3RrLLQB1HrtXmnxKKrsVs2RsxKt4plRYJGUCxRjs6twKgr6lps1q22taZT7+7dZh7dYE0uKJfWB1PYeKR+rbOxvrAyMNm2VJ/YUEn9R/ugUoGv9EVWxH2feQCRBXZZFQaUR7HxitpOWsPBGtN9tbo3ts1HWl/3/p/hfRgTvK3To+uNM1OSBeMLQ9IUr7hM//ghYu5SaAKQ7CTeOveiHpxUm8dG+ZJ7Pl4XvhfvC4/uneZ6vAWQSDVB5RKTPrtAtF2+dqdUoYcKOPZLA2UG71oa2MUAEhhpqwvG829Z0T2BMnXTY9w2/4v+Yb7cPxCkKuAfD0aeHpoEYCDJdv/r1nYjpFVzWYYGOhsm/h2nMmihZBBpGAFpvF7uo0obDwCYv5xra53EHt/hfIhPLXCWQTc5iR/F5YcgZ6KMGvvpFCJwbOIoNHM2wm6VlSxtYmfoQnxoSQN47Xtw3VyPudSziivVu0HFALaXbh9KCFqFP4ThEU8PbkWXSBwZijFL2f5WgcjD6LZmHhiIZIEWAVUa1NauPlL+uxFbisLejCRb7qDAU5fy9i60iba/riaUz1obOAt5F9XbqVkbHK5NPhfkswQV7ERsB88PqsRhfkB61RCcdPJ/WJJoyyL2cEYTdtlK1V+9PfNebeGJXxPRnndnNOmpAmMM0JXR0z8KDxB8N9/i/EoqLNfiTqJ9p9b3KS+WxYIlDVKKFMCqlbmGgIyEycix0IgfYyA72gofzIF5rLlloSCLq99pLWtL8R7MP8+Z4sQkrMuJIegphhK9XQlKmWWTeRonWRoTaCwquZ0v9fH2P6hAk7deaO3dgK9dBBmc7Ht6rgoWveg6/0DNCx9sZT2cW303qcokHAY9qS+yAZH8H01IpS1GV"
`endif