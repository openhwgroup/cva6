// Copyright 2015 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the “License”); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an “AS IS” BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Engineer:       Antonio Pullini - pullinia@iis.ee.ethz.ch                  //
//                                                                            //
// Additional contributions by:                                               //
//                 Sven Stucki - svstucki@student.ethz.ch                     //
//                 Michael Gautschi - gautschi@iis.ee.ethz.ch                 //
//                 Igor Loi - igor.loi@unibo.it                               //
//                 Davide Schiavone - pschiavo@iis.ee.ethz.ch                 //
//                                                                            //
// Design Name:    RISC-V register file  Wrapper                              //
// Project Name:   RISCV                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Register file Wrapper, that provides one test port (1RW)   //
//                 to be connected to a bist collar (MBIST)                   //
//                 Test data is written on port A, (port B is masked during   //
//                 test. Test Read data is got from port A (rdata_a_o)        //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

//
// ADDRESS 0 is NOT WRITABLE !!!!!!!!!!!!!!!!!!!!
//

module register_file_test_wrap
#(
   parameter ADDR_WIDTH    = 5,
   parameter DATA_WIDTH    = 32,
   parameter FPU           = 0,
   parameter Zfinx         = 0
)
(
   // Clock and Reset
   input  logic                   clk,
   input  logic                   rst_n,

   input  logic                   test_en_i,

   //Read port R1
   input  logic [ADDR_WIDTH-1:0]  raddr_a_i,
   output logic [DATA_WIDTH-1:0]  rdata_a_o,

   //Read port R2
   input  logic [ADDR_WIDTH-1:0]  raddr_b_i,
   output logic [DATA_WIDTH-1:0]  rdata_b_o,

   //Read port R3
   input  logic [ADDR_WIDTH-1:0]  raddr_c_i,
   output logic [DATA_WIDTH-1:0]  rdata_c_o,

   // Write port W1
   input  logic [ADDR_WIDTH-1:0]   waddr_a_i,
   input  logic [DATA_WIDTH-1:0]   wdata_a_i,
   input  logic                    we_a_i,

   // Write port W2
   input  logic [ADDR_WIDTH-1:0]   waddr_b_i,
   input  logic [DATA_WIDTH-1:0]   wdata_b_i,
   input  logic                    we_b_i,

   // BIST ENABLE
   input  logic                    BIST,
   //BIST ports
   input  logic                    CSN_T,
   input  logic                    WEN_T,
   input  logic [ADDR_WIDTH-1:0]   A_T,
   input  logic [DATA_WIDTH-1:0]   D_T,
   output logic [DATA_WIDTH-1:0]   Q_T
);


   logic [ADDR_WIDTH-1:0]        ReadAddr_a_muxed;

   logic                         WriteEnable_a_muxed;
   logic [ADDR_WIDTH-1:0]        WriteAddr_a_muxed;
   logic [DATA_WIDTH-1:0]        WriteData_a_muxed;

   logic                         WriteEnable_b_muxed;
   logic [ADDR_WIDTH-1:0]        WriteAddr_b_muxed;
   logic [DATA_WIDTH-1:0]        WriteData_b_muxed;


   logic [ADDR_WIDTH-1:0]        TestReadAddr_Q;


   // Multiplex This port during BIST
   assign WriteData_a_muxed   = (BIST) ?  D_T                                       : wdata_a_i;
   // FIX for CADENCE PMBIST : ignore Addr MSB (FPU=0) and internally invert address
   // assign WriteAddr_a_muxed   = (BIST) ?  A_T                                       : waddr_a_i;
   assign WriteAddr_a_muxed   = (BIST) ?  {1'b0,~A_T[ADDR_WIDTH-2:0]}              : waddr_a_i;
   assign WriteEnable_a_muxed = (BIST) ? (( CSN_T == 1'b0 ) && ( WEN_T == 1'b0))    : we_a_i;

   // Mask this port during TEST MODE (BIST == 1)
   assign WriteData_b_muxed   = (BIST) ? '0    : wdata_b_i;
   assign WriteAddr_b_muxed   = (BIST) ? '0    : waddr_b_i;
   assign WriteEnable_b_muxed = (BIST) ? 1'b0  : we_b_i;


   assign ReadAddr_a_muxed    = (BIST) ? TestReadAddr_Q   : raddr_a_i;


   assign Q_T = rdata_a_o;

   always_ff @(posedge clk or negedge rst_n)
   begin : proc_
      if(~rst_n)
      begin
         TestReadAddr_Q <= '0;
      end
      else
      begin
         if((CSN_T == 1'b0)&& ( WEN_T == 1'b1)) // Test Read
         begin
            // FIX for CADENCE PMBIST : ignore Addr MSB (FPU=0) and internally invert address
            // TestReadAddr_Q <= A_T;
            TestReadAddr_Q <= {1'b0,~A_T[ADDR_WIDTH-2:0]} ;
         end
      end
   end


   riscv_register_file
   #(
      .ADDR_WIDTH ( ADDR_WIDTH          ),
      .DATA_WIDTH ( DATA_WIDTH          ),
      .FPU        ( FPU                 ),
      .Zfinx      ( Zfinx               )
   )
   riscv_register_file_i
   (
      .clk        ( clk                 ),
      .rst_n      ( rst_n               ),

      .test_en_i  ( test_en_i           ),

      .raddr_a_i  ( ReadAddr_a_muxed    ),
      .rdata_a_o  ( rdata_a_o           ),

      .raddr_b_i  ( raddr_b_i           ),
      .rdata_b_o  ( rdata_b_o           ),

      .raddr_c_i  ( raddr_c_i           ),
      .rdata_c_o  ( rdata_c_o           ),

      .waddr_a_i  ( WriteAddr_a_muxed   ),
      .wdata_a_i  ( WriteData_a_muxed   ),
      .we_a_i     ( WriteEnable_a_muxed ),

      .waddr_b_i  ( WriteAddr_b_muxed   ),
      .wdata_b_i  ( WriteData_b_muxed   ),
      .we_b_i     ( WriteEnable_b_muxed )
   );





endmodule
