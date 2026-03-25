//------------------------------------------------------------------------------
// File       : gig_ethernet_pcs_pma_0_johnson_cntr.v
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
//  Description:  This logic describes a standard johnson counter to
//                create divided down clocks.  A divide by 10 clock is
//                created.
//
//                The capabilities of this Johnson counter are extended
//                with the use of the clock enables - it is only the
//                clock-enabled cycles which are divided down.
//
//                The divide by 10 clock is output directly from a rising
//                edge triggered flip-flop (clocked on the input clk).


`timescale 1 ps/1 ps


//------------------------------------------------------------------------------
// Module declaration.
//-----------------------------------------------------------------------------

module gig_ethernet_pcs_pma_0_johnson_cntr
  (
    input  reset,           // Synchronous Reset
    input  clk,             // Input clock (always at 125MHz)
    input  clk_en,          // Clock enable for rising edge triggered flip flops
    output clk_div10        // (Clock, gated with clock enable) divide by 10
  );



  //----------------------------------------------------------------------------
  // internal signals used in this top level wrapper.
  //----------------------------------------------------------------------------


  reg reg1;            // first flip flop
  reg reg2;            // second flip flop
  reg reg3;            // third flip flop
  reg reg4;            // fourth flip flop
  reg reg5;            // fifth flip flop



  // Create a 5-stage shift register
  always @(posedge clk)
  begin
    if (reset == 1'b1) begin
      reg1 <= 1'b0;
      reg2 <= 1'b0;
      reg3 <= 1'b0;
      reg4 <= 1'b0;
      reg5 <= 1'b0;
    end
    else begin
      if (clk_en == 1'b1) begin
        if (reg5 == 1'b1 && reg4 == 1'b0) begin  // ensure that LFSR self corrects on every repetition
          reg1 <= 1'b0;
          reg2 <= 1'b0;
          reg3 <= 1'b0;
          reg4 <= 1'b0;
          reg5 <= 1'b0;
        end
        else begin
          reg1 <= !reg5;
          reg2 <= reg1;
          reg3 <= reg2;
          reg4 <= reg3;
          reg5 <= reg4;
        end
      end
    end
  end



  // The 5-stage shift register causes reg3 to toggle every 5 clock
  // enabled cycles, effectively creating a divide by 10 clock
  assign clk_div10 = reg3;



endmodule

