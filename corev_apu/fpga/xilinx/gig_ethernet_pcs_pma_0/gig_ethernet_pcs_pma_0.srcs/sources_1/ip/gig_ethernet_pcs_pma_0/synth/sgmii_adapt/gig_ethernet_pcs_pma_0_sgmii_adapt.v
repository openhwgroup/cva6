//------------------------------------------------------------------------------
// File       : gig_ethernet_pcs_pma_0_sgmii_adapt.v
// Author     : Xilinx Inc.
//------------------------------------------------------------------------------
// (c) Copyright 2004-2008 Xilinx, Inc. All rights reserved.
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
// Description: This is the top level entity for the SGMII adaptation
//              module.  This creates a GMII-style interface which is
//              clocked at 125MHz at 1Gbps; 12.5MHz at 100Mbps and
//              1.25MHz at 10Mbps.  The GMII-style interface has an
//              8-bit data path.  At 10/100Mbps speeds, this GMII-style
//              interface does not conform to any offical specification
//              but it is a convenient interface to use internally to
//              connect to a client MAC - for example, the Tri-Speed
//              Ethernet MAC LogiCORE from Xilinx.
//
//              This instantiates three sub modules, which are:
//
//              clk_gen.v
//              -----------
//
//              This file creates the necessary receiver and transmitter
//              clocks and clock enables for use with the core.  Clock
//              frequencies are:
//                 * 125  MHz at an operating speed of 1Gbps
//                 * 12.5 MHz at an operating speed of 100Mbps
//                 * 1.25 MHz at an operating speed of 10Mbps
//
//              tx_rate_adapt.v
//              ---------------
//
//              This module accepts transmitter data from the GMII style
//              interface from the attached client MAC.  At 1 Gbps, this
//              GMII transmitter data will be valid on evey clock cycle
//              of the 125MHz reference clock; at 100Mbps, this data
//              will be repeated for a ten clock period duration of the
//              125MHz reference clock; at 10Mbps, this data will be
//              repeated for a hundred clock period duration of the
//              125MHz reference clock.
//
//              This module will sample the input transmitter GMII data
//              synchronously to the 125MHz reference clock.  This
//              sampled data can then be connected direcly to the input
//              GMII-style interface of the Ethernet 1000BASE-X PCS/PMA
//              or SGMII LogiCORE.
//
//              rx_rate_adapt.v
//              ---------------
//
//              This module accepts receiver data from the Ethernet
//              1000BASE-X PCS/PMA or SGMII LogiCORE. At 1 Gbps, this
//              data will be valid on evey clock cycle of the 125MHz
//              reference clock; at 100Mbps, this data will be repeated
//              for a ten clock period duration of the 125MHz reference
//              clock; at 10Mbps, this data will be repeated for a
//              hundred clock period duration of the 125MHz reference
//              clock.
//
//              This module will sample the input receiver data
//              synchronously to the 125MHz reference clock in the
//              centre of the data valid window.  The Start of Frame
//              Delimiter (SFD) is also detected, and if required, it is
//              realigned across the 8-bit data path.
//
//              This data will then be held constant for the
//              appropriate number of clock cycles so that it can be
//              sampled by the client MAC attached at the other end of
//              the GMII-style link.


`timescale 1 ps/1 ps


//------------------------------------------------------------------------------
// The module declaration for the SGMII adaptation logic.
//------------------------------------------------------------------------------

module gig_ethernet_pcs_pma_0_sgmii_adapt
  (
    input            reset,            // Asynchronous reset for entire core.

    // Clock derivation
    //-----------------
    input            clk125m,          // Reference 125MHz clock.
    output           sgmii_clk_r,      // Clock to client MAC (125MHz, 12.5MHz or 1.25MHz) (to rising edge DDR).
    output           sgmii_clk_f,      // Clock to client MAC (125MHz, 12.5MHz or 1.25MHz) (to falling edge DDR).
    output           sgmii_clk_en,     // Clock enable to client MAC (125MHz, 12.5MHz or 1.25MHz).
    // GMII Tx
    //--------
    input  [7:0]     gmii_txd_in,      // Transmit data from client MAC.
    input            gmii_tx_en_in,    // Transmit data valid signal from client MAC.
    input            gmii_tx_er_in,    // Transmit error signal from client MAC.
    output [7:0]     gmii_rxd_out,     // Received Data to client MAC.
    output           gmii_rx_dv_out,   // Received data valid signal to client MAC.
    output           gmii_rx_er_out,   // Received error signal to client MAC.

    // GMII Rx
    //--------
    input [7:0]      gmii_rxd_in,      // Received Data to client MAC.
    input            gmii_rx_dv_in,    // Received data valid signal to client MAC.
    input            gmii_rx_er_in,    // Received error signal to client MAC.
    output [7:0]     gmii_txd_out,     // Transmit data from client MAC.
    output           gmii_tx_en_out,   // Transmit data valid signal from client MAC.
    output           gmii_tx_er_out,   // Transmit error signal from client MAC.

    // Speed Control
    //--------------
    input            speed_is_10_100,  // Core should operate at either 10Mbps or 100Mbps speeds
    input            speed_is_100      // Core should operate at 100Mbps speed

  );



  //----------------------------------------------------------------------------
  // internal signals used in this wrapper.
  //----------------------------------------------------------------------------

  // A clock enable for the GMII transmitter and receiver data path 
  wire         sgmii_clk_en_int;
  // create a synchronous reset in the clk125m clock domain
  wire         sync_reset;

  // Resynchronous the speed settings into the local clock domain
  wire         speed_is_10_100_resync;
  wire         speed_is_100_resync;



  //----------------------------------------------------------------------------
  // Clock Resynchronisation logic
  //----------------------------------------------------------------------------

  // Create synchronous reset in the clk125m clock domain.
  gig_ethernet_pcs_pma_0_reset_sync gen_sync_reset (
    .clk                 (clk125m),
    .reset_in            (reset),
    .reset_out           (sync_reset)
  );


  // Resynchronous the speed settings into the local clock domain
  gig_ethernet_pcs_pma_0_sync_block resync_speed_10_100 (
    .clk                 (clk125m),
    .data_in             (speed_is_10_100),
    .data_out            (speed_is_10_100_resync)
  );


  // Resynchronous the speed settings into the local clock domain
  gig_ethernet_pcs_pma_0_sync_block resync_speed_100 (
    .clk                 (clk125m),
    .data_in             (speed_is_100),
    .data_out            (speed_is_100_resync)
  );



  //----------------------------------------------------------------------------
  // Component instantiation for the clock generation circuitry
  //----------------------------------------------------------------------------

  gig_ethernet_pcs_pma_0_clk_gen clock_generation (
    .reset               (sync_reset),
    .clk125m             (clk125m),
    .speed_is_10_100     (speed_is_10_100_resync),
    .speed_is_100        (speed_is_100_resync),
    .sgmii_clk_r         (sgmii_clk_r),
    .sgmii_clk_f         (sgmii_clk_f),
    .sgmii_clk_en        (sgmii_clk_en_int)
  );

  // Route to output port
  assign sgmii_clk_en = sgmii_clk_en_int;

  //----------------------------------------------------------------------------
  // Component Instantiation for the transmitter rate adapt logic
  //----------------------------------------------------------------------------

  gig_ethernet_pcs_pma_0_tx_rate_adapt transmitter (
    .reset               (sync_reset),
    .clk125m             (clk125m),
    .sgmii_clk_en        (sgmii_clk_en_int),
    .gmii_txd_in         (gmii_txd_in),
    .gmii_tx_en_in       (gmii_tx_en_in),
    .gmii_tx_er_in       (gmii_tx_er_in),
    .gmii_txd_out        (gmii_txd_out),
    .gmii_tx_en_out      (gmii_tx_en_out),
    .gmii_tx_er_out      (gmii_tx_er_out)
  );

  //----------------------------------------------------------------------------
  // Component Instantiation for the receiver rate adapt logic
  //----------------------------------------------------------------------------
  gig_ethernet_pcs_pma_0_rx_rate_adapt receiver (
    .reset               (sync_reset),
    .clk125m             (clk125m),
    .sgmii_clk_en        (sgmii_clk_en_int),
    .gmii_rxd_in         (gmii_rxd_in),
    .gmii_rx_dv_in       (gmii_rx_dv_in),
    .gmii_rx_er_in       (gmii_rx_er_in),
    .gmii_rxd_out        (gmii_rxd_out),
    .gmii_rx_dv_out      (gmii_rx_dv_out),
    .gmii_rx_er_out      (gmii_rx_er_out)
  );

endmodule

