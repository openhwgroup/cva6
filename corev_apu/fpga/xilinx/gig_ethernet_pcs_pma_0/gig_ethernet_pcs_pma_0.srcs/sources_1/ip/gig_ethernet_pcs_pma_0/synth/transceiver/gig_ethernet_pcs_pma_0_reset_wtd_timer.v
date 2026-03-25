//------------------------------------------------------------------------------
// Title      : Reset watch dog timer 
// File       : gig_ethernet_pcs_pma_0_reset_wtd_timer.v
// Author     : Xilinx
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
//------------------------------------------------------------------------------
//  Description:  This logic describes a watch dog counter for 3 seconds.
//                If data valid is not received withing 3 seconds a reset is
//                asserted.


`timescale 1 ps/1 ps


//------------------------------------------------------------------------------
// Module declaration.
//-----------------------------------------------------------------------------

(* DowngradeIPIdentifiedWarnings="yes" *)
module gig_ethernet_pcs_pma_0_reset_wtd_timer #
  (
    parameter  WAIT_TIME = 24'H8F0D18
  )
  (
    input      clk,               // Input clock
    input      data_valid,        // Indication that data is received
    output reg reset              // Reset on timer timeout
  );



   reg  [5:0]   counter_stg1 = 6'd0;
   reg  [11:0]  counter_stg2 = 12'd0;
   reg  [11:0]  counter_stg3 = 12'd0;
   wire         counter_stg1_roll;
   wire         counter_stg2_roll;
   wire         timer_reset;
   wire         three_sec_timeout;

   always @(posedge clk)
   begin
       if ((data_valid == 1'b1) || (timer_reset == 1'b1)) begin
           counter_stg1 <= 6'b000000;
       end
       else begin
           if (data_valid == 1'b0) begin
               counter_stg1 <= counter_stg1 + 6'b000001;
           end
       end
   end
   
   assign counter_stg1_roll = (counter_stg1 == 6'b111111);

   always @(posedge clk)
   begin
       if ((data_valid == 1'b1) || (timer_reset == 1'b1)) begin
           counter_stg2 <= 12'b000000000000;
       end
       else begin
           if ((data_valid == 1'b0) & (counter_stg1_roll == 1'b1)) begin
               counter_stg2 <= counter_stg2 + 12'b000000000001;
           end
       end
   end

   assign counter_stg2_roll = (counter_stg2 == 12'b111111111111);

   always @(posedge clk)
   begin
       if ((data_valid == 1'b1) || (timer_reset == 1'b1)) begin
           counter_stg3 <= 12'b000000000000;
       end
       else begin
           if ((data_valid == 1'b0) & (counter_stg2_roll == 1'b1) & (counter_stg1_roll == 1'b1)) begin
               counter_stg3 <= counter_stg3 + 12'b000000000001;
           end
       end
   end


   assign three_sec_timeout = ((counter_stg3 == WAIT_TIME[23:12]) & (counter_stg2 == WAIT_TIME[11:0]));
   assign timer_reset = ((counter_stg3 == WAIT_TIME[23:12]) & (counter_stg2 == WAIT_TIME[11:0]) & (counter_stg1 == 6'H3F));

   always @(posedge clk)
   begin
       if ((three_sec_timeout == 1'b1) & (counter_stg1[5] == 1'b1)) begin
           reset <= 1'b1;
       end
       else begin
           reset <= 1'b0;
       end
   end

endmodule

