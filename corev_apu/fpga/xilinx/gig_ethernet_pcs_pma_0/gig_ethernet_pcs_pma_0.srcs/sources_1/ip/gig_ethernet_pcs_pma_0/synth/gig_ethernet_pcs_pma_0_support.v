//------------------------------------------------------------------------------
// File       : gig_ethernet_pcs_pma_0_support.v
// Author     : Xilinx Inc.
//------------------------------------------------------------------------------
// (c) Copyright 2011 Xilinx, Inc. All rights reserved.
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
// 
//------------------------------------------------------------------------------
// Description: This module holds the support level for the pcs/pma core
//              This can be used as-is in a single core design, or adapted
//              for use with multi-core implementations

`timescale 1 ps/1 ps
(* DowngradeIPIdentifiedWarnings="yes" *)

//------------------------------------------------------------------------------
// The module declaration for the Core Block wrapper.
//------------------------------------------------------------------------------

module gig_ethernet_pcs_pma_0_support 
  #( parameter EXAMPLE_SIMULATION                     =  0 )
    
   (
      // Transceiver Interface
      //----------------------


      input        gtrefclk_p,                // differential clock
      input        gtrefclk_n,                // differential clock
      output       gtrefclk_out,              // Very high quality clock for GT transceiver.
      output       gtrefclk_bufg_out,
      output       txp,                   // Differential +ve of serial transmission from PMA to PMD.
      output       txn,                   // Differential -ve of serial transmission from PMA to PMD.
      input        rxp,                   // Differential +ve for serial reception from PMD to PMA.
      input        rxn,                   // Differential -ve for serial reception from PMD to PMA.
      output       userclk_out,               
      output       userclk2_out,              
      output       rxuserclk_out,             
      output       rxuserclk2_out,            
      input        independent_clock_bufg,    // Freerun Independent clock,
      output       pma_reset_out,             // transceiver PMA reset signal
      output       mmcm_locked_out,           // MMCM Locked
      output       resetdone,
      // GMII Interface
      //---------------
      output       sgmii_clk_r,             // Clock for client MAC 
      output       sgmii_clk_f,             // Clock for client MAC 
      output       sgmii_clk_en,          // Clock enable for client MAC
      input [7:0]  gmii_txd,              // Transmit data from client MAC.
      input        gmii_tx_en,            // Transmit control signal from client MAC.
      input        gmii_tx_er,            // Transmit control signal from client MAC.
      output [7:0] gmii_rxd,              // Received Data to client MAC.
      output       gmii_rx_dv,            // Received control signal to client MAC.
      output       gmii_rx_er,            // Received control signal to client MAC.
      output       gmii_isolate,          // Tristate control to electrically isolate GMII.

      // Management: Alternative to MDIO Interface
      //------------------------------------------

      input [4:0]  configuration_vector,  // Alternative to MDIO interface.

      output       an_interrupt,          // Interrupt to processor to signal that Auto-Negotiation has completed
      input [15:0] an_adv_config_vector,  // Alternate interface to program REG4 (AN ADV)
      input        an_restart_config,     // Alternate signal to modify AN restart bit in REG0

      // Speed Control
      //--------------
      input        speed_is_10_100,       // Core should operate at either 10Mbps or 100Mbps speeds
      input        speed_is_100,          // Core should operate at 100Mbps speed

      // General IO's
      //-------------
      output [15:0] status_vector,         // Core status.
      input        reset,                 // Asynchronous reset for entire core.
      
      input        signal_detect,          // Input from PMD to indicate presence of optical input.
      output            gt0_qplloutclk_out,
      output            gt0_qplloutrefclk_out
 


   );


   //---------------------------------------------------------------------------
   // Internal signals used in this block level wrapper.
   //---------------------------------------------------------------------------

   // Core <=> Transceiver interconnect
   wire         gtrefclk;                 // High quality clock
   wire         gtrefclk_bufg;
   wire         cplllock;                // reset done indication from transceiver
   wire         mmcm_reset;               // Reset to MMCM based on resetdone
   wire         mmcm_locked;              // Signal indicating that MMCM has locked
   wire         pma_reset;                // Reset synchronized to system clock
   wire         txoutclk;                 // txoutclk from GT transceiver (62.5MHz)
   wire         rxoutclk;                 // txoutclk from GT transceiver (62.5MHz)
   wire         userclk;                  
   wire         userclk2;                 
   wire         rxuserclk;                 
   wire         rxuserclk2;                 

      // GT Interface
      //-------------
   wire                gt0_qplloutclk;
   wire                gt0_qplloutrefclk;
  
gig_ethernet_pcs_pma_0_block  # ( .EXAMPLE_SIMULATION             (EXAMPLE_SIMULATION) )  
pcs_pma_block_i
   (
      // Transceiver Interface
      //----------------------

      .gtrefclk                            (gtrefclk),              // Very high quality clock for GT transceiver.
      .gtrefclk_bufg                       (gtrefclk_bufg),
      .txp (txp),                   // Differential +ve of serial transmission from PMA to PMD.
      .txn (txn),                   // Differential -ve of serial transmission from PMA to PMD.
      .rxp (rxp),                   // Differential +ve for serial reception from PMD to PMA.
      .rxn (rxn),                   // Differential -ve for serial reception from PMD to PMA.

      .txoutclk                            (txoutclk),
      .rxoutclk                            (rxoutclk),
      .resetdone                           (resetdone),
      .cplllock                            (cplllock),
      .mmcm_reset                          (mmcm_reset),
      .userclk                             (userclk),
      .userclk2                            (userclk2),
      .rxuserclk                           (rxuserclk),
      .rxuserclk2                          (rxuserclk2),
      .independent_clock_bufg              (independent_clock_bufg),
      .pma_reset                           (pma_reset),
      .mmcm_locked                         (mmcm_locked),

      .sgmii_clk_r                         (sgmii_clk_r),
      .sgmii_clk_f                         (sgmii_clk_f),
      .sgmii_clk_en                        (sgmii_clk_en),
      .gmii_txd                            (gmii_txd),
      .gmii_tx_en                          (gmii_tx_en),
      .gmii_tx_er                          (gmii_tx_er),
      .gmii_rxd                            (gmii_rxd),
      .gmii_rx_dv                          (gmii_rx_dv),
      .gmii_rx_er                          (gmii_rx_er),
      .gmii_isolate                        (gmii_isolate),

      // Management: Alternative to MDIO Interface
      //------------------------------------------

      .configuration_vector          (configuration_vector),

      .an_interrupt                  (an_interrupt),
      .an_adv_config_vector          (an_adv_config_vector),
      .an_restart_config             (an_restart_config),

      // Speed Control
      //--------------
      .speed_is_10_100               (speed_is_10_100),
      .speed_is_100                  (speed_is_100),


      // General IO's
      //-------------
      .status_vector          (status_vector),         // Core status.
      .reset                  (pma_reset),                 // Asynchronous reset for entire core.
      
      .signal_detect           (signal_detect) ,         // Input from PMD to indicate presence of optical input.
      .gt0_qplloutclk_in       (gt0_qplloutclk),                          
      .gt0_qplloutrefclk_in    (gt0_qplloutrefclk)
   );


  //----------------------------------------------------------------------------
  // Instantiate the clocking module.
  //----------------------------------------------------------------------------
   gig_ethernet_pcs_pma_0_clocking core_clocking_i
   (
      .gtrefclk_p                (gtrefclk_p),
      .gtrefclk_n                (gtrefclk_n),
      .txoutclk                  (txoutclk),
      .rxoutclk                  (rxoutclk),
      .mmcm_reset                (mmcm_reset),
      .gtrefclk                  (gtrefclk),
      .gtrefclk_bufg             (gtrefclk_bufg),
      .mmcm_locked               (mmcm_locked), 
      .userclk                   (userclk),
      .userclk2                  (userclk2),
      .rxuserclk                 (rxuserclk),
      .rxuserclk2                (rxuserclk2)
   );

assign gtrefclk_out   = gtrefclk;
assign gtrefclk_bufg_out   = gtrefclk_bufg;
assign userclk_out    = userclk;
assign userclk2_out   = userclk2;
assign rxuserclk_out  = rxuserclk;
assign rxuserclk2_out = rxuserclk2;


   //---------------------------------------------------------------------------
   // Transceiver PMA reset circuitry
   //---------------------------------------------------------------------------
   gig_ethernet_pcs_pma_0_resets core_resets_i
   (
     .reset                     (reset),
     .independent_clock_bufg    (independent_clock_bufg),

     .pma_reset                 (pma_reset)
   );

assign pma_reset_out = pma_reset;


  gig_ethernet_pcs_pma_0_gt_common core_gt_common_i
(
    .GTREFCLK0_IN                (gtrefclk) ,
    .QPLLLOCK_OUT                (),
    .QPLLLOCKDETCLK_IN           (independent_clock_bufg),
    .QPLLOUTCLK_OUT              (gt0_qplloutclk),
    .QPLLOUTREFCLK_OUT           (gt0_qplloutrefclk),
    .QPLLREFCLKLOST_OUT          (),    
    .QPLLRESET_IN                (pma_reset) 
);

  assign   gt0_qplloutclk_out        = gt0_qplloutclk;
  assign   gt0_qplloutrefclk_out     = gt0_qplloutrefclk;

 assign   mmcm_locked_out              = mmcm_locked;

endmodule // gig_ethernet_pcs_pma_0_support

