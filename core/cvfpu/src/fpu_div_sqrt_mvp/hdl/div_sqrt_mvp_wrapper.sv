// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the “License”); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an “AS IS” BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
////////////////////////////////////////////////////////////////////////////////
// Company:        IIS @ ETHZ - Federal Institute of Technology               //
//                                                                            //
// Engineers:      Lei Li -- lile@iis.ee.ethz.ch                              //
//                                                                            //
// Additional contributions by:                                               //
//                                                                            //
//                                                                            //
//                                                                            //
// Create Date:    20/04/2018                                                 //
// Design Name:    FPU                                                        //
// Module Name:    div_sqrt_mvp_wrapper.sv                                    //
// Project Name:   The shared divisor and square root                         //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    The wrapper of  div_sqrt_top_mvp                           //
//                                                                            //
//                                                                            //
//                                                                            //
//                                                                            //
//                                                                            //
//                                                                            //
//                                                                            //
//                                                                            //
//                                                                            //
//                                                                            //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

import defs_div_sqrt_mvp::*;

module div_sqrt_mvp_wrapper
#(
   parameter   PrePipeline_depth_S             =        0,  // If you want to add a flip/flop stage before preprocess, set it to 1.
   parameter   PostPipeline_depth_S            =        2  // The output delay stages
)
  (//Input
   input logic                            Clk_CI,
   input logic                            Rst_RBI,
   input logic                            Div_start_SI,
   input logic                            Sqrt_start_SI,

   //Input Operands
   input logic [C_OP_FP64-1:0]            Operand_a_DI,
   input logic [C_OP_FP64-1:0]            Operand_b_DI,

   // Input Control
   input logic [C_RM-1:0]                 RM_SI,    //Rounding Mode
   input logic [C_PC-1:0]                 Precision_ctl_SI, // Precision Control
   input logic [C_FS-1:0]                 Format_sel_SI,  // Format Selection,
   input logic                            Kill_SI,

   //Output Result
   output logic [C_OP_FP64-1:0]           Result_DO,

   //Output-Flags
   output logic [4:0]                     Fflags_SO,
   output logic                           Ready_SO,
   output logic                           Done_SO
 );


   logic                                 Div_start_S_S,Sqrt_start_S_S;
   logic [C_OP_FP64-1:0]                 Operand_a_S_D;
   logic [C_OP_FP64-1:0]                 Operand_b_S_D;

   // Input Control
   logic [C_RM-1:0]                      RM_S_S;    //Rounding Mode
   logic [C_PC-1:0]                      Precision_ctl_S_S; // Precision Control
   logic [C_FS-1:0]                      Format_sel_S_S;  // Format Selection,
   logic                                 Kill_S_S;


  logic [C_OP_FP64-1:0]                  Result_D;
  logic                                  Ready_S;
  logic                                  Done_S;
  logic [4:0]                            Fflags_S;


  generate
    if(PrePipeline_depth_S==1)
      begin

         div_sqrt_top_mvp  div_top_U0  //for RTL

          (//Input
           .Clk_CI                 (Clk_CI),
           .Rst_RBI                (Rst_RBI),
           .Div_start_SI           (Div_start_S_S),
           .Sqrt_start_SI          (Sqrt_start_S_S),
           //Input Operands
           .Operand_a_DI          (Operand_a_S_D),
           .Operand_b_DI          (Operand_b_S_D),
           .RM_SI                 (RM_S_S),    //Rounding Mode
           .Precision_ctl_SI      (Precision_ctl_S_S),
           .Format_sel_SI         (Format_sel_S_S),
           .Kill_SI               (Kill_S_S),
           .Result_DO             (Result_D),
           .Fflags_SO             (Fflags_S),
           .Ready_SO              (Ready_S),
           .Done_SO               (Done_S)
         );

           always_ff @(posedge Clk_CI, negedge Rst_RBI)
             begin
                if(~Rst_RBI)
                  begin
                    Div_start_S_S<='0;
                    Sqrt_start_S_S<=1'b0;
                    Operand_a_S_D<='0;
                    Operand_b_S_D<='0;
                    RM_S_S <=1'b0;
                    Precision_ctl_S_S<='0;
                    Format_sel_S_S<='0;
                    Kill_S_S<='0;
                  end
                else
                  begin
                    Div_start_S_S<=Div_start_SI;
                    Sqrt_start_S_S<=Sqrt_start_SI;
                    Operand_a_S_D<=Operand_a_DI;
                    Operand_b_S_D<=Operand_b_DI;
                    RM_S_S <=RM_SI;
                    Precision_ctl_S_S<=Precision_ctl_SI;
                    Format_sel_S_S<=Format_sel_SI;
                    Kill_S_S<=Kill_SI;
                  end
            end
     end

     else
      begin
          div_sqrt_top_mvp  div_top_U0  //for RTL
          (//Input
           .Clk_CI                 (Clk_CI),
           .Rst_RBI                (Rst_RBI),
           .Div_start_SI           (Div_start_SI),
           .Sqrt_start_SI          (Sqrt_start_SI),
           //Input Operands
           .Operand_a_DI          (Operand_a_DI),
           .Operand_b_DI          (Operand_b_DI),
           .RM_SI                 (RM_SI),    //Rounding Mode
           .Precision_ctl_SI      (Precision_ctl_SI),
           .Format_sel_SI         (Format_sel_SI),
           .Kill_SI               (Kill_SI),
           .Result_DO             (Result_D),
           .Fflags_SO             (Fflags_S),
           .Ready_SO              (Ready_S),
           .Done_SO               (Done_S)
         );
      end
  endgenerate

   /////////////////////////////////////////////////////////////////////////////
   // First Stage of Outputs
   /////////////////////////////////////////////////////////////////////////////
  logic [C_OP_FP64-1:0]         Result_dly_S_D;
  logic                         Ready_dly_S_S;
  logic                         Done_dly_S_S;
  logic [4:0]                   Fflags_dly_S_S;
   always_ff @(posedge Clk_CI, negedge Rst_RBI)
     begin
        if(~Rst_RBI)
          begin
            Result_dly_S_D<='0;
            Ready_dly_S_S<=1'b0;
            Done_dly_S_S<=1'b0;
            Fflags_dly_S_S<=1'b0;
          end
        else
          begin
            Result_dly_S_D<=Result_D;
            Ready_dly_S_S<=Ready_S;
            Done_dly_S_S<=Done_S;
            Fflags_dly_S_S<=Fflags_S;
          end
    end

   /////////////////////////////////////////////////////////////////////////////
   // Second Stage of Outputs
   /////////////////////////////////////////////////////////////////////////////

  logic [C_OP_FP64-1:0]         Result_dly_D_D;
  logic                         Ready_dly_D_S;
  logic                         Done_dly_D_S;
  logic [4:0]                   Fflags_dly_D_S;
  generate
    if(PostPipeline_depth_S==2)
      begin
        always_ff @(posedge Clk_CI, negedge Rst_RBI)
          begin
            if(~Rst_RBI)
              begin
                Result_dly_D_D<='0;
                Ready_dly_D_S<=1'b0;
                Done_dly_D_S<=1'b0;
                Fflags_dly_D_S<=1'b0;
              end
           else
             begin
               Result_dly_D_D<=Result_dly_S_D;
               Ready_dly_D_S<=Ready_dly_S_S;
               Done_dly_D_S<=Done_dly_S_S;
               Fflags_dly_D_S<=Fflags_dly_S_S;
             end
          end
        assign  Result_DO = Result_dly_D_D;
        assign  Ready_SO  = Ready_dly_D_S;
        assign  Done_SO  = Done_dly_D_S;
        assign  Fflags_SO=Fflags_dly_D_S;
       end

     else
       begin
         assign  Result_DO = Result_dly_S_D;
         assign  Ready_SO  = Ready_dly_S_S;
         assign  Done_SO   = Done_dly_S_S;
         assign  Fflags_SO  = Fflags_dly_S_S;
       end

   endgenerate

endmodule //
