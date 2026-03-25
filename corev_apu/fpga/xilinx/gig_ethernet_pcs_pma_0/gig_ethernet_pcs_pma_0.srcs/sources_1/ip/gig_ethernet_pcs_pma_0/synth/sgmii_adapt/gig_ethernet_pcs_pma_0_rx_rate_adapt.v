//------------------------------------------------------------------------------
// File       : gig_ethernet_pcs_pma_0_rx_rate_adapt.v
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
// Description: This module accepts receiver data from the Ethernet
//              1000BASE-X PCS/PMA or SGMII LogiCORE. At 1 Gbps, this
//              data will be valid on evey clock cycle of the 125MHz
//              reference clock; at 100Mbps, this data will be repeated
//              for a ten clock period duration of the 125MHz reference
//              clock; at 10Mbps, this data will be repeated for a
//              hundred clock period duration of the 125MHz reference
//              clock.
//
//              The Start of Frame Delimiter (SFD) is also detected, and
//              if required, it is realigned across the 8-bit data path.
//              This module will then sample this correctly aligned data
//              synchronously to the 125MHz reference clock. This data
//              will be held constant for the appropriate number of clock
//              cycles so that it can then be sampled by the client MAC
//              attached at the other end of the GMII-style link.



`timescale 1 ps/1 ps


//------------------------------------------------------------------------------
// The module declaration
//------------------------------------------------------------------------------

module gig_ethernet_pcs_pma_0_rx_rate_adapt
  (
    input            reset,                  // Synchronous reset.
    input            clk125m,                // Reference 125MHz receiver clock.
    input            sgmii_clk_en,           // Clock enable for the receiver logic (125MHz, 25MHz, 2.5MHz).
    input      [7:0] gmii_rxd_in,            // Receive data from client MAC.
    input            gmii_rx_dv_in,          // Receive data valid signal from client MAC.
    input            gmii_rx_er_in,          // Receive error signal from client MAC.
    output reg [7:0] gmii_rxd_out,           // Receive data from client MAC.
    output reg       gmii_rx_dv_out,         // Receive data valid signal from client MAC.
    output reg       gmii_rx_er_out          // Receive error signal from client MAC.
  );



  //----------------------------------------------------------------------------
  // internal signals used in this module.
  //----------------------------------------------------------------------------


  reg [7:0] rxd_reg1;       // gmii_rxd_in delayed by 1 clock cycle
  reg [7:0] rxd_reg2;       // gmii_rxd_in delayed by 2 clock cycles
  reg       rx_dv_reg1;     // gmii_rx_dv_in delayed by 1 clock cycle
  reg       rx_dv_reg2;     // gmii_rx_dv_in delayed by 2 clock cycles
  reg       rx_er_reg1;     // gmii_rx_er_in delayed by 1 clock cycle
  reg       rx_er_reg2;     // gmii_rx_er_in delayed by 2 clock cycles
  reg       sfd_aligned;    // 0xD5 (The Start of Frame Delimiter (SFD) ) has been detected on a single 8-bit code group
  reg       sfd_misaligned; // 0xD5 (SFD) has been detected across two 8-bit code groups
  reg       sfd_enable;     // Enable the detection of the SFD at the start of a new frame
  reg       muxsel;         // Used to control the 8-bit SFD based alignment
  reg [7:0] rxd_aligned;    // gmii_rxd_in aligned
  reg       rx_dv_aligned;  // gmii_rx_dv_in aligned
  reg       rx_er_aligned;  // gmii_rx_er_in aligned



   initial     //initialize all outputs to 0 at startup
     begin
       gmii_rxd_out = 8'b00000000;
       gmii_rx_dv_out = 1'b0;
       gmii_rx_er_out = 1'b0;
     end

  // Create a pipeline for the gmii receiver signals
  always @(posedge clk125m)
  begin
    if (reset == 1'b1) begin
      rxd_reg1     <= 8'b0;
      rxd_reg2     <= 8'b0;
      rx_dv_reg1   <= 1'b0;
      rx_dv_reg2   <= 1'b0;
      rx_er_reg1   <= 1'b0;
      rx_er_reg2   <= 1'b0;
    end
    else begin
      if (sgmii_clk_en == 1'b1) begin
        rxd_reg1   <= gmii_rxd_in;
        rxd_reg2   <= rxd_reg1;
        rx_dv_reg1 <= gmii_rx_dv_in;
        rx_dv_reg2 <= rx_dv_reg1;
        rx_er_reg1 <= gmii_rx_er_in;
        rx_er_reg2 <= rx_er_reg1;
      end
    end
  end


  // Detect the SDF code across a single 8-bit data code group
  always @(rxd_reg1)
  begin
    if (rxd_reg1 == 8'b11010101)
      sfd_aligned <= 1'b1;
    else
      sfd_aligned <= 1'b0;
  end



  // Detect the SDF code across two 8-bit data code groups
  always @(rxd_reg1 or gmii_rxd_in)
  begin
    if (gmii_rxd_in[3:0] == 4'b1101 && rxd_reg1[7:4] == 4'b0101)
      sfd_misaligned <= 1'b1;
    else
      sfd_misaligned <= 1'b0;
  end



  // only the 1st 0xD5 at the start of the frame is the genuine SFD (the
  // value 0xD5 may follow later in the frame data).  Therefore it is
  // important to only use the first 0xD5 code for alignment.
  // sfd_enable is therefore created to enable the SFD based alignment.
  // sfd_enable is asserted at the beginning of every frame and is
  // unasserted after the detection of the first 0xD5 code.
  always @(posedge clk125m)
  begin
    if (reset == 1'b1)
      sfd_enable   <= 1'b0;
    else begin
      if (sgmii_clk_en == 1'b1) begin
        if ((gmii_rx_dv_in == 1'b1) && (rx_dv_reg1 == 1'b0))      // assert at the start of the frame (signified by the rising edge of gmii_rx_dv_in)
          sfd_enable <= 1'b1;
        else if (sfd_aligned == 1'b1 || sfd_misaligned == 1'b1)   // unassert after detecting the 1st 0xD5 value
          sfd_enable <= 1'b0;
      end
    end
  end



  // Create a multiplexer control signals which is used to control the
  // alignment of the frame across the 8-bit data path
  always @(posedge clk125m)
  begin
    if (reset == 1'b1)
      muxsel   <= 1'b0;
    else begin
      if (sgmii_clk_en == 1'b1) begin
        if (sfd_aligned == 1'b1 && sfd_enable == 1'b1)  // muxsel is realigned at the start of each frame based on the alignment of the SFD
          muxsel <= 1'b0;
        else if (sfd_misaligned == 1'b1 && sfd_enable == 1'b1)
          muxsel <= 1'b1;
      end
    end
  end



  // Realign the receiver data across the 8-bit data path based on the
  // alignment of the SFD.
  always @(posedge clk125m)
  begin
    if (reset == 1'b1) begin
      rxd_aligned     <= 8'b0;
      rx_dv_aligned   <= 1'b0;
      rx_er_aligned   <= 1'b0;
    end
    else begin
      if (sgmii_clk_en == 1'b1) begin
        if (muxsel == 1'b0) begin
          rxd_aligned   <= rxd_reg2;                       // preserve alignment
          rx_dv_aligned <= rx_dv_reg2;
          rx_er_aligned <= rx_er_reg2;
        end
        else begin
          rxd_aligned   <= {rxd_reg1[3:0], rxd_reg2[7:4]}; // correct the alignment
          rx_dv_aligned <= rx_dv_reg1 && rx_dv_reg2;
          rx_er_aligned <= rx_er_reg1 || rx_er_reg2;
        end
      end
    end
  end




  // Sample the correctly aligned data
  always @(posedge clk125m)
  begin
    if (reset == 1'b1) begin
      gmii_rxd_out     <= 8'b0;
      gmii_rx_dv_out   <= 8'b0;
      gmii_rx_er_out   <= 1'b0;
    end
    else begin
      if (sgmii_clk_en == 1'b1) begin
        gmii_rxd_out   <= rxd_aligned;
        gmii_rx_dv_out <= rx_dv_aligned;
        gmii_rx_er_out <= rx_er_aligned;
      end
    end
  end



endmodule

