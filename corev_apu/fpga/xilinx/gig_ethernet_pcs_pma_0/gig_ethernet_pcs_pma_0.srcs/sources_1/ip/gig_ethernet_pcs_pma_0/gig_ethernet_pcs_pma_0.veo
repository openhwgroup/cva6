// (c) Copyright 1995-2026 Xilinx, Inc. All rights reserved.
// 
// This file contains confidential and proprietary information
// of Xilinx, Inc. and is protected under U.S. and
// international copyright and other intellectual property
// laws.
// 
// DISCLAIMER
// This disclaimer is not a license and does not grant any
// rights to the materials distributed herewith. Except as
// otherwise provided in a valid license issued to you by
// Xilinx, and to the maximum extent permitted by applicable
// law: (1) THESE MATERIALS ARE MADE AVAILABLE "AS IS" AND
// WITH ALL FAULTS, AND XILINX HEREBY DISCLAIMS ALL WARRANTIES
// AND CONDITIONS, EXPRESS, IMPLIED, OR STATUTORY, INCLUDING
// BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, NON-
// INFRINGEMENT, OR FITNESS FOR ANY PARTICULAR PURPOSE; and
// (2) Xilinx shall not be liable (whether in contract or tort,
// including negligence, or under any other theory of
// liability) for any loss or damage of any kind or nature
// related to, arising under or in connection with these
// materials, including for any direct, or any indirect,
// special, incidental, or consequential loss or damage
// (including loss of data, profits, goodwill, or any type of
// loss or damage suffered as a result of any action brought
// by a third party) even if such damage or loss was
// reasonably foreseeable or Xilinx had been advised of the
// possibility of the same.
// 
// CRITICAL APPLICATIONS
// Xilinx products are not designed or intended to be fail-
// safe, or for use in any application requiring fail-safe
// performance, such as life-support or safety devices or
// systems, Class III medical devices, nuclear facilities,
// applications related to the deployment of airbags, or any
// other applications that could lead to death, personal
// injury, or severe property or environmental damage
// (individually and collectively, "Critical
// Applications"). Customer assumes the sole risk and
// liability of any use of Xilinx products in Critical
// Applications, subject only to applicable laws and
// regulations governing limitations on product liability.
// 
// THIS COPYRIGHT NOTICE AND DISCLAIMER MUST BE RETAINED AS
// PART OF THIS FILE AT ALL TIMES.
// 
// DO NOT MODIFY THIS FILE.

// IP VLNV: xilinx.com:ip:gig_ethernet_pcs_pma:16.2
// IP Revision: 0

// The following must be inserted into your Verilog file for this
// core to be instantiated. Change the instance name and port connections
// (in parentheses) to your own signal names.

//----------- Begin Cut here for INSTANTIATION Template ---// INST_TAG
gig_ethernet_pcs_pma_0 your_instance_name (
  .gtrefclk_p(gtrefclk_p),                          // input wire gtrefclk_p
  .gtrefclk_n(gtrefclk_n),                          // input wire gtrefclk_n
  .gtrefclk_out(gtrefclk_out),                      // output wire gtrefclk_out
  .gtrefclk_bufg_out(gtrefclk_bufg_out),            // output wire gtrefclk_bufg_out
  .txn(txn),                                        // output wire txn
  .txp(txp),                                        // output wire txp
  .rxn(rxn),                                        // input wire rxn
  .rxp(rxp),                                        // input wire rxp
  .independent_clock_bufg(independent_clock_bufg),  // input wire independent_clock_bufg
  .userclk_out(userclk_out),                        // output wire userclk_out
  .userclk2_out(userclk2_out),                      // output wire userclk2_out
  .rxuserclk_out(rxuserclk_out),                    // output wire rxuserclk_out
  .rxuserclk2_out(rxuserclk2_out),                  // output wire rxuserclk2_out
  .resetdone(resetdone),                            // output wire resetdone
  .pma_reset_out(pma_reset_out),                    // output wire pma_reset_out
  .mmcm_locked_out(mmcm_locked_out),                // output wire mmcm_locked_out
  .sgmii_clk_r(sgmii_clk_r),                        // output wire sgmii_clk_r
  .sgmii_clk_f(sgmii_clk_f),                        // output wire sgmii_clk_f
  .sgmii_clk_en(sgmii_clk_en),                      // output wire sgmii_clk_en
  .gmii_txd(gmii_txd),                              // input wire [7 : 0] gmii_txd
  .gmii_tx_en(gmii_tx_en),                          // input wire gmii_tx_en
  .gmii_tx_er(gmii_tx_er),                          // input wire gmii_tx_er
  .gmii_rxd(gmii_rxd),                              // output wire [7 : 0] gmii_rxd
  .gmii_rx_dv(gmii_rx_dv),                          // output wire gmii_rx_dv
  .gmii_rx_er(gmii_rx_er),                          // output wire gmii_rx_er
  .gmii_isolate(gmii_isolate),                      // output wire gmii_isolate
  .configuration_vector(configuration_vector),      // input wire [4 : 0] configuration_vector
  .an_interrupt(an_interrupt),                      // output wire an_interrupt
  .an_adv_config_vector(an_adv_config_vector),      // input wire [15 : 0] an_adv_config_vector
  .an_restart_config(an_restart_config),            // input wire an_restart_config
  .speed_is_10_100(speed_is_10_100),                // input wire speed_is_10_100
  .speed_is_100(speed_is_100),                      // input wire speed_is_100
  .status_vector(status_vector),                    // output wire [15 : 0] status_vector
  .reset(reset),                                    // input wire reset
  .signal_detect(signal_detect),                    // input wire signal_detect
  .gt0_qplloutclk_out(gt0_qplloutclk_out),          // output wire gt0_qplloutclk_out
  .gt0_qplloutrefclk_out(gt0_qplloutrefclk_out)    // output wire gt0_qplloutrefclk_out
);
// INST_TAG_END ------ End INSTANTIATION Template ---------

// You must compile the wrapper file gig_ethernet_pcs_pma_0.v when simulating
// the core, gig_ethernet_pcs_pma_0. When compiling the wrapper file, be sure to
// reference the Verilog simulation library.

