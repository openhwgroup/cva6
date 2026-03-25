//------------------------------------------------------------------------------
// File       : gig_ethernet_pcs_pma_0_clocking.v
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
// Description: This module holds the Clocking logic for pcs/pma core. 


`timescale 1 ps/1 ps


//------------------------------------------------------------------------------
// The module declaration for the example design
//------------------------------------------------------------------------------

module gig_ethernet_pcs_pma_0_clocking
   (
      input            gtrefclk_p,                // Differential +ve of reference clock for MGT: 125MHz, very high quality.
      input            gtrefclk_n,                // Differential -ve of reference clock for MGT: 125MHz, very high quality.
      input            txoutclk,                  // txoutclk from GT transceiver.
      input            rxoutclk,                  // rxoutclk from GT transceiver.
      input            mmcm_reset,                // MMCM Reset
      
      output           gtrefclk,                  // gtrefclk routed through an IBUFG.
      output           gtrefclk_bufg,             // gtrefclk routed through a BUFG for driving logic.
      output  wire     mmcm_locked,               // MMCM locked

      output           userclk,                   // for GT PMA reference clock
      output           userclk2,                  // 125MHz clock for core reference clock.
      output           rxuserclk,                 // for GT PMA reference clock
      output           rxuserclk2                 // 125MHz clock for core reference clock.
   );

   wire         clkout0;                  // MMCM output clock
   wire         clkout1;                  // MMCM output clock
   wire         clkfbout;                 // MMCM Feedback clock
// Route txoutclk input through a BUFG
   wire txoutclk_bufg;
  
   wire userclk_i;
   wire rxoutclk_buf;

   wire gtrefclk_i;
   //---------------------------------------------------------------------------
   // Transceiver Clock Management
   //---------------------------------------------------------------------------

   // Clock circuitry for the Transceiver uses a differential input clock.
   // gtrefclk is routed to the tranceiver.
   IBUFDS_GTE2 ibufds_gtrefclk (
      .I     (gtrefclk_p),
      .IB    (gtrefclk_n),
      .CEB   (1'b0),
      .O     (gtrefclk_i),
      .ODIV2 ()
   );

  assign gtrefclk = gtrefclk_i;

   BUFG  bufg_gtrefclk (
      .I         (gtrefclk_i),
      .O         (gtrefclk_bufg)
   );
   // Route txoutclk input through a BUFG
   BUFG  bufg_txoutclk (
      .I         (txoutclk),
      .O         (txoutclk_bufg)
   );

  // The GT transceiver provides a 62.5MHz clock to the FPGA fabrix.  This is 
  // routed to an MMCM module where it is used to create phase and frequency
  // related 62.5MHz and 125MHz clock sources
  MMCME2_ADV # (
    .BANDWIDTH            ("OPTIMIZED"),
    .CLKOUT4_CASCADE      ("FALSE"),
    .COMPENSATION         ("ZHOLD"),
    .STARTUP_WAIT         ("FALSE"),
    .DIVCLK_DIVIDE        (1),
    .CLKFBOUT_PHASE       (0.000),
    .CLKFBOUT_USE_FINE_PS ("FALSE"),
    .CLKOUT0_PHASE        (0.000),
    .CLKOUT0_DUTY_CYCLE   (0.5),
    .CLKOUT0_USE_FINE_PS  ("FALSE"),
    .CLKOUT1_PHASE        (0.000),
    .CLKOUT1_DUTY_CYCLE   (0.5),
    .CLKOUT1_USE_FINE_PS  ("FALSE"),
    .CLKIN1_PERIOD        (16.0),
    .CLKFBOUT_MULT_F      (16.000),
    .CLKOUT0_DIVIDE_F     (8.000),
    .CLKOUT1_DIVIDE       (16),
    
    .REF_JITTER1          (0.010)
  ) mmcm_adv_inst (
    // Output clocks
    .CLKFBOUT             (clkfbout),
    .CLKFBOUTB            (),
    .CLKOUT0              (clkout0),
    .CLKOUT0B             (),
    .CLKOUT1              (clkout1),
    .CLKOUT1B             (),
    .CLKOUT2              (),
    .CLKOUT2B             (),
    .CLKOUT3              (),
    .CLKOUT3B             (),
    .CLKOUT4              (),
    .CLKOUT5              (),
    .CLKOUT6              (),
    // Input clock control
    .CLKFBIN              (clkfbout),
    .CLKIN1               (txoutclk_bufg),
    .CLKIN2               (1'b0),
    // Tied to always select the primary input clock
    .CLKINSEL             (1'b1),
    // Ports for dynamic reconfiguration
    .DADDR                (7'h0),
    .DCLK                 (1'b0),
    .DEN                  (1'b0),
    .DI                   (16'h0),
    .DO                   (),
    .DRDY                 (),
    .DWE                  (1'b0),
    // Ports for dynamic phase shift
    .PSCLK                (1'b0),
    .PSEN                 (1'b0),
    .PSINCDEC             (1'b0),
    .PSDONE               (),
    // Other control and status signals
    .LOCKED               (mmcm_locked),
    .CLKINSTOPPED         (),
    .CLKFBSTOPPED         (),
    .PWRDWN               (1'b0),
    .RST                  (mmcm_reset)
   );
  // This 62.5MHz clock is placed onto global clock routing and is then used
   // for tranceiver TXUSRCLK/RXUSRCLK.
   BUFG bufg_userclk (
      .I     (clkout1),
      .O     (userclk_i)
   );


   // This 125MHz clock is placed onto global clock routing and is then used
   // to clock all Ethernet core logic.
   BUFG bufg_userclk2 (
      .I     (clkout0),
      .O     (userclk2)
   );



assign userclk = userclk_i;


   // Place the Rx recovered clock on a Global Clock Buffer (it may be possible
   // to switch this for a BUFHCE/BUFR and BUFMR combination)
   BUFG rxrecclkbufg (
      .I   (rxoutclk),
      .O   (rxoutclk_buf)
   );
    assign rxuserclk2 = rxoutclk_buf;
    assign rxuserclk  = rxoutclk_buf;
   


endmodule // gig_ethernet_pcs_pma_0_clocking
