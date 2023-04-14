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
// Engineers:                Lei Li  //lile@iis.ee.ethz.ch                    //
//		                                                                        //
// Additional contributions by:                                               //
//                                                                            //
//                                                                            //
//                                                                            //
// Create Date:    01/03/2018                                                 //
// Design Name:    FPU                                                        //
// Module Name:    preprocess_mvp.sv                                          //
// Project Name:   Private FPU                                                //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:           decode and data preparation                         //
//                                                                            //
// Revision Date:  12/04/2018                                                 //
//                 Lei Li                                                     //
//                 To address some requirements by Stefan and add low power   //
//                 control for special cases                                  //
//                                                                            //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

import defs_div_sqrt_mvp::*;

module preprocess_mvp
  (
   input logic                   Clk_CI,
   input logic                   Rst_RBI,
   input logic                   Div_start_SI,
   input logic                   Sqrt_start_SI,
   input logic                   Ready_SI,
   //Input Operands
   input logic [C_OP_FP64-1:0]   Operand_a_DI,
   input logic [C_OP_FP64-1:0]   Operand_b_DI,
   input logic [C_RM-1:0]        RM_SI,    //Rounding Mode
   input logic [C_FS-1:0]        Format_sel_SI,  // Format Selection

   // to control
   output logic                  Start_SO,
   output logic [C_EXP_FP64:0]   Exp_a_DO_norm,
   output logic [C_EXP_FP64:0]   Exp_b_DO_norm,
   output logic [C_MANT_FP64:0]  Mant_a_DO_norm,
   output logic [C_MANT_FP64:0]  Mant_b_DO_norm,

   output logic [C_RM-1:0]       RM_dly_SO,

   output logic                  Sign_z_DO,
   output logic                  Inf_a_SO,
   output logic                  Inf_b_SO,
   output logic                  Zero_a_SO,
   output logic                  Zero_b_SO,
   output logic                  NaN_a_SO,
   output logic                  NaN_b_SO,
   output logic                  SNaN_SO,
   output logic                  Special_case_SBO,
   output logic                  Special_case_dly_SBO
   );

   //Hidden Bits
   logic                         Hb_a_D;
   logic                         Hb_b_D;

   logic [C_EXP_FP64-1:0]        Exp_a_D;
   logic [C_EXP_FP64-1:0]        Exp_b_D;
   logic [C_MANT_FP64-1:0]       Mant_a_NonH_D;
   logic [C_MANT_FP64-1:0]       Mant_b_NonH_D;
   logic [C_MANT_FP64:0]         Mant_a_D;
   logic [C_MANT_FP64:0]         Mant_b_D;

   /////////////////////////////////////////////////////////////////////////////
   // Disassemble operands
   /////////////////////////////////////////////////////////////////////////////
   logic                      Sign_a_D,Sign_b_D;
   logic                      Start_S;

     always_comb
       begin
         case(Format_sel_SI)
           2'b00:
             begin
               Sign_a_D = Operand_a_DI[C_OP_FP32-1];
               Sign_b_D = Operand_b_DI[C_OP_FP32-1];
               Exp_a_D  = {3'h0, Operand_a_DI[C_OP_FP32-2:C_MANT_FP32]};
               Exp_b_D  = {3'h0, Operand_b_DI[C_OP_FP32-2:C_MANT_FP32]};
               Mant_a_NonH_D = {Operand_a_DI[C_MANT_FP32-1:0],29'h0};
               Mant_b_NonH_D = {Operand_b_DI[C_MANT_FP32-1:0],29'h0};
             end
           2'b01:
             begin
               Sign_a_D = Operand_a_DI[C_OP_FP64-1];
               Sign_b_D = Operand_b_DI[C_OP_FP64-1];
               Exp_a_D  = Operand_a_DI[C_OP_FP64-2:C_MANT_FP64];
               Exp_b_D  = Operand_b_DI[C_OP_FP64-2:C_MANT_FP64];
               Mant_a_NonH_D = Operand_a_DI[C_MANT_FP64-1:0];
               Mant_b_NonH_D = Operand_b_DI[C_MANT_FP64-1:0];
             end
           2'b10:
             begin
               Sign_a_D = Operand_a_DI[C_OP_FP16-1];
               Sign_b_D = Operand_b_DI[C_OP_FP16-1];
               Exp_a_D  = {6'h00, Operand_a_DI[C_OP_FP16-2:C_MANT_FP16]};
               Exp_b_D  = {6'h00, Operand_b_DI[C_OP_FP16-2:C_MANT_FP16]};
               Mant_a_NonH_D = {Operand_a_DI[C_MANT_FP16-1:0],42'h0};
               Mant_b_NonH_D = {Operand_b_DI[C_MANT_FP16-1:0],42'h0};
             end
           2'b11:
             begin
               Sign_a_D = Operand_a_DI[C_OP_FP16ALT-1];
               Sign_b_D = Operand_b_DI[C_OP_FP16ALT-1];
               Exp_a_D  = {3'h0, Operand_a_DI[C_OP_FP16ALT-2:C_MANT_FP16ALT]};
               Exp_b_D  = {3'h0, Operand_b_DI[C_OP_FP16ALT-2:C_MANT_FP16ALT]};
               Mant_a_NonH_D = {Operand_a_DI[C_MANT_FP16ALT-1:0],45'h0};
               Mant_b_NonH_D = {Operand_b_DI[C_MANT_FP16ALT-1:0],45'h0};
             end
           endcase
       end


   assign Mant_a_D = {Hb_a_D,Mant_a_NonH_D};
   assign Mant_b_D = {Hb_b_D,Mant_b_NonH_D};

   assign Hb_a_D = | Exp_a_D; // hidden bit
   assign Hb_b_D = | Exp_b_D; // hidden bit

   assign Start_S= Div_start_SI | Sqrt_start_SI;



   /////////////////////////////////////////////////////////////////////////////
   // preliminary checks for infinite/zero/NaN operands                       //
   /////////////////////////////////////////////////////////////////////////////

   logic               Mant_a_prenorm_zero_S;
   logic               Mant_b_prenorm_zero_S;

   logic               Exp_a_prenorm_zero_S;
   logic               Exp_b_prenorm_zero_S;
   assign Exp_a_prenorm_zero_S = ~Hb_a_D;
   assign Exp_b_prenorm_zero_S = ~Hb_b_D;

   logic               Exp_a_prenorm_Inf_NaN_S;
   logic               Exp_b_prenorm_Inf_NaN_S;

   logic               Mant_a_prenorm_QNaN_S;
   logic               Mant_a_prenorm_SNaN_S;
   logic               Mant_b_prenorm_QNaN_S;
   logic               Mant_b_prenorm_SNaN_S;

   assign Mant_a_prenorm_QNaN_S=Mant_a_NonH_D[C_MANT_FP64-1]&&(~(|Mant_a_NonH_D[C_MANT_FP64-2:0]));
   assign Mant_a_prenorm_SNaN_S=(~Mant_a_NonH_D[C_MANT_FP64-1])&&((|Mant_a_NonH_D[C_MANT_FP64-2:0]));
   assign Mant_b_prenorm_QNaN_S=Mant_b_NonH_D[C_MANT_FP64-1]&&(~(|Mant_b_NonH_D[C_MANT_FP64-2:0]));
   assign Mant_b_prenorm_SNaN_S=(~Mant_b_NonH_D[C_MANT_FP64-1])&&((|Mant_b_NonH_D[C_MANT_FP64-2:0]));

     always_comb
       begin
         case(Format_sel_SI)
           2'b00:
             begin
               Mant_a_prenorm_zero_S=(Operand_a_DI[C_MANT_FP32-1:0] == C_MANT_ZERO_FP32);
               Mant_b_prenorm_zero_S=(Operand_b_DI[C_MANT_FP32-1:0] == C_MANT_ZERO_FP32);
               Exp_a_prenorm_Inf_NaN_S=(Operand_a_DI[C_OP_FP32-2:C_MANT_FP32] == C_EXP_INF_FP32);
               Exp_b_prenorm_Inf_NaN_S=(Operand_b_DI[C_OP_FP32-2:C_MANT_FP32] == C_EXP_INF_FP32);
             end
           2'b01:
             begin
               Mant_a_prenorm_zero_S=(Operand_a_DI[C_MANT_FP64-1:0] == C_MANT_ZERO_FP64);
               Mant_b_prenorm_zero_S=(Operand_b_DI[C_MANT_FP64-1:0] == C_MANT_ZERO_FP64);
               Exp_a_prenorm_Inf_NaN_S=(Operand_a_DI[C_OP_FP64-2:C_MANT_FP64] == C_EXP_INF_FP64);
               Exp_b_prenorm_Inf_NaN_S=(Operand_b_DI[C_OP_FP64-2:C_MANT_FP64] == C_EXP_INF_FP64);
             end
           2'b10:
             begin
               Mant_a_prenorm_zero_S=(Operand_a_DI[C_MANT_FP16-1:0] == C_MANT_ZERO_FP16);
               Mant_b_prenorm_zero_S=(Operand_b_DI[C_MANT_FP16-1:0] == C_MANT_ZERO_FP16);
               Exp_a_prenorm_Inf_NaN_S=(Operand_a_DI[C_OP_FP16-2:C_MANT_FP16] == C_EXP_INF_FP16);
               Exp_b_prenorm_Inf_NaN_S=(Operand_b_DI[C_OP_FP16-2:C_MANT_FP16] == C_EXP_INF_FP16);
             end
           2'b11:
             begin
               Mant_a_prenorm_zero_S=(Operand_a_DI[C_MANT_FP16ALT-1:0] == C_MANT_ZERO_FP16ALT);
               Mant_b_prenorm_zero_S=(Operand_b_DI[C_MANT_FP16ALT-1:0] == C_MANT_ZERO_FP16ALT);
               Exp_a_prenorm_Inf_NaN_S=(Operand_a_DI[C_OP_FP16ALT-2:C_MANT_FP16ALT] == C_EXP_INF_FP16ALT);
               Exp_b_prenorm_Inf_NaN_S=(Operand_b_DI[C_OP_FP16ALT-2:C_MANT_FP16ALT] == C_EXP_INF_FP16ALT);
             end
           endcase
       end




   logic               Zero_a_SN,Zero_a_SP;
   logic               Zero_b_SN,Zero_b_SP;
   logic               Inf_a_SN,Inf_a_SP;
   logic               Inf_b_SN,Inf_b_SP;
   logic               NaN_a_SN,NaN_a_SP;
   logic               NaN_b_SN,NaN_b_SP;
   logic               SNaN_SN,SNaN_SP;

   assign Zero_a_SN = (Start_S&&Ready_SI)?(Exp_a_prenorm_zero_S&&Mant_a_prenorm_zero_S):Zero_a_SP;
   assign Zero_b_SN = (Start_S&&Ready_SI)?(Exp_b_prenorm_zero_S&&Mant_b_prenorm_zero_S):Zero_b_SP;
   assign Inf_a_SN = (Start_S&&Ready_SI)?(Exp_a_prenorm_Inf_NaN_S&&Mant_a_prenorm_zero_S):Inf_a_SP;
   assign Inf_b_SN = (Start_S&&Ready_SI)?(Exp_b_prenorm_Inf_NaN_S&&Mant_b_prenorm_zero_S):Inf_b_SP;
   assign NaN_a_SN = (Start_S&&Ready_SI)?(Exp_a_prenorm_Inf_NaN_S&&(~Mant_a_prenorm_zero_S)):NaN_a_SP;
   assign NaN_b_SN = (Start_S&&Ready_SI)?(Exp_b_prenorm_Inf_NaN_S&&(~Mant_b_prenorm_zero_S)):NaN_b_SP;
   assign SNaN_SN = (Start_S&&Ready_SI) ? ((Mant_a_prenorm_SNaN_S&&NaN_a_SN) | (Mant_b_prenorm_SNaN_S&&NaN_b_SN)) : SNaN_SP;

   always_ff @(posedge Clk_CI, negedge Rst_RBI)
     begin
        if(~Rst_RBI)
          begin
            Zero_a_SP <='0;
            Zero_b_SP <='0;
            Inf_a_SP <='0;
            Inf_b_SP <='0;
            NaN_a_SP <='0;
            NaN_b_SP <='0;
            SNaN_SP <= '0;
          end
        else
         begin
           Inf_a_SP <=Inf_a_SN;
           Inf_b_SP <=Inf_b_SN;
           Zero_a_SP <=Zero_a_SN;
           Zero_b_SP <=Zero_b_SN;
           NaN_a_SP <=NaN_a_SN;
           NaN_b_SP <=NaN_b_SN;
           SNaN_SP <= SNaN_SN;
         end
      end

   /////////////////////////////////////////////////////////////////////////////
   // Low power control
   /////////////////////////////////////////////////////////////////////////////

   assign Special_case_SBO=(~{(Div_start_SI)?(Zero_a_SN | Zero_b_SN |  Inf_a_SN | Inf_b_SN | NaN_a_SN | NaN_b_SN): (Zero_a_SN | Inf_a_SN | NaN_a_SN | Sign_a_D) })&&(Start_S&&Ready_SI);


   always_ff @(posedge Clk_CI, negedge Rst_RBI)
     begin
       if(~Rst_RBI)
          begin
            Special_case_dly_SBO <= '0;
          end
       else if((Start_S&&Ready_SI))
         begin
            Special_case_dly_SBO <= Special_case_SBO;
         end
       else if(Special_case_dly_SBO)
         begin
         Special_case_dly_SBO <= 1'b1;
         end
      else
         begin
            Special_case_dly_SBO <= '0;
         end
    end

   /////////////////////////////////////////////////////////////////////////////
   // Delay sign for normalization and round                                  //
   /////////////////////////////////////////////////////////////////////////////

   logic                   Sign_z_DN;
   logic                   Sign_z_DP;

   always_comb
     begin
       if(Div_start_SI&&Ready_SI)
           Sign_z_DN = Sign_a_D ^ Sign_b_D;
       else if(Sqrt_start_SI&&Ready_SI)
           Sign_z_DN = Sign_a_D;
       else
           Sign_z_DN = Sign_z_DP;
    end

   always_ff @(posedge Clk_CI, negedge Rst_RBI)
     begin
       if(~Rst_RBI)
          begin
            Sign_z_DP <= '0;
          end
       else
         begin
            Sign_z_DP <= Sign_z_DN;
         end
    end

   logic [C_RM-1:0]                  RM_DN;
   logic [C_RM-1:0]                  RM_DP;

   always_comb
     begin
       if(Start_S&&Ready_SI)
           RM_DN = RM_SI;
       else
           RM_DN = RM_DP;
    end

   always_ff @(posedge Clk_CI, negedge Rst_RBI)
     begin
       if(~Rst_RBI)
          begin
            RM_DP <= '0;
          end
       else
         begin
            RM_DP <= RM_DN;
         end
    end
   assign RM_dly_SO = RM_DP;

   logic [5:0]                  Mant_leadingOne_a, Mant_leadingOne_b;
   logic                        Mant_zero_S_a,Mant_zero_S_b;

  lzc #(
    .WIDTH ( C_MANT_FP64+1 ),
    .MODE  ( 1             )
  ) LOD_Ua (
    .in_i    ( Mant_a_D          ),
    .cnt_o   ( Mant_leadingOne_a ),
    .empty_o ( Mant_zero_S_a     )
  );

   logic [C_MANT_FP64:0]            Mant_a_norm_DN,Mant_a_norm_DP;

   assign  Mant_a_norm_DN = ((Start_S&&Ready_SI))?(Mant_a_D<<(Mant_leadingOne_a)):Mant_a_norm_DP;

   always_ff @(posedge Clk_CI, negedge Rst_RBI)
     begin
        if(~Rst_RBI)
          begin
            Mant_a_norm_DP <= '0;
          end
        else
          begin
            Mant_a_norm_DP<=Mant_a_norm_DN;
          end
     end

   logic [C_EXP_FP64:0]            Exp_a_norm_DN,Exp_a_norm_DP;
   assign  Exp_a_norm_DN = ((Start_S&&Ready_SI))?(Exp_a_D-Mant_leadingOne_a+(|Mant_leadingOne_a)):Exp_a_norm_DP;  //Covering the process of denormal numbers

   always_ff @(posedge Clk_CI, negedge Rst_RBI)
     begin
        if(~Rst_RBI)
          begin
            Exp_a_norm_DP <= '0;
          end
        else
          begin
            Exp_a_norm_DP<=Exp_a_norm_DN;
          end
     end

  lzc #(
    .WIDTH ( C_MANT_FP64+1 ),
    .MODE  ( 1             )
  ) LOD_Ub (
    .in_i    ( Mant_b_D          ),
    .cnt_o   ( Mant_leadingOne_b ),
    .empty_o ( Mant_zero_S_b     )
  );


   logic [C_MANT_FP64:0]            Mant_b_norm_DN,Mant_b_norm_DP;

   assign  Mant_b_norm_DN = ((Start_S&&Ready_SI))?(Mant_b_D<<(Mant_leadingOne_b)):Mant_b_norm_DP;

   always_ff @(posedge Clk_CI, negedge Rst_RBI)
     begin
        if(~Rst_RBI)
          begin
            Mant_b_norm_DP <= '0;
          end
        else
          begin
            Mant_b_norm_DP<=Mant_b_norm_DN;
          end
     end

   logic [C_EXP_FP64:0]            Exp_b_norm_DN,Exp_b_norm_DP;
   assign  Exp_b_norm_DN = ((Start_S&&Ready_SI))?(Exp_b_D-Mant_leadingOne_b+(|Mant_leadingOne_b)):Exp_b_norm_DP; //Covering the process of denormal numbers

   always_ff @(posedge Clk_CI, negedge Rst_RBI)
     begin
        if(~Rst_RBI)
          begin
            Exp_b_norm_DP <= '0;
          end
        else
          begin
            Exp_b_norm_DP<=Exp_b_norm_DN;
          end
     end

   /////////////////////////////////////////////////////////////////////////////
   // Output assignments                                                      //
   /////////////////////////////////////////////////////////////////////////////

   assign Start_SO=Start_S;
   assign Exp_a_DO_norm=Exp_a_norm_DP;
   assign Exp_b_DO_norm=Exp_b_norm_DP;
   assign Mant_a_DO_norm=Mant_a_norm_DP;
   assign Mant_b_DO_norm=Mant_b_norm_DP;
   assign Sign_z_DO=Sign_z_DP;
   assign Inf_a_SO=Inf_a_SP;
   assign Inf_b_SO=Inf_b_SP;
   assign Zero_a_SO=Zero_a_SP;
   assign Zero_b_SO=Zero_b_SP;
   assign NaN_a_SO=NaN_a_SP;
   assign NaN_b_SO=NaN_b_SP;
   assign SNaN_SO=SNaN_SP;

endmodule
