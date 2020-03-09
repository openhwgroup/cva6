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
// Engineers:      Lei Li    lile@iis.ee.ethz.ch                              //
//                                                                            //
// Additional contributions by:                                               //
//                                                                            //
//                                                                            //
//                                                                            //
// Create Date:    09/03/2018                                                 //
// Design Name:    FPU                                                        //
// Module Name:    norm_div_sqrt_mvp.sv                                       //
// Project Name:                                                              //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Floating point Normalizer/Rounding unit                    //
//                 Since this module is design as a combinatinal logic, it can//
//                 be added arbinary register stages for different frequency  //
//                 in the wrapper module.                                     //
//                                                                            //
//                                                                            //
//                                                                            //
// Revision Date:  12/04/2018                                                 //
//                 Lei Li                                                     //
//                 To address some requirements by Stefan                     //
//                                                                            //
//                                                                            //
//                                                                            //
//                                                                            //
//                                                                            //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

import defs_div_sqrt_mvp::*;

module norm_div_sqrt_mvp
  (//Inputs
   input logic [C_MANT_FP64+4:0]                Mant_in_DI,  // Include the needed 4-bit for rounding and hidden bit
   input logic signed [C_EXP_FP64+1:0]          Exp_in_DI,
   input logic                                  Sign_in_DI,
   input logic                                  Div_enable_SI,
   input logic                                  Sqrt_enable_SI,
   input logic                                  Inf_a_SI,
   input logic                                  Inf_b_SI,
   input logic                                  Zero_a_SI,
   input logic                                  Zero_b_SI,
   input logic                                  NaN_a_SI,
   input logic                                  NaN_b_SI,
   input logic                                  SNaN_SI,
   input logic [C_RM-1:0]                       RM_SI,
   input logic                                  Full_precision_SI,
   input logic                                  FP32_SI,
   input logic                                  FP64_SI,
   input logic                                  FP16_SI,
   input logic                                  FP16ALT_SI,
   //Outputs
   output logic [C_EXP_FP64+C_MANT_FP64:0]      Result_DO,
   output logic [4:0]                           Fflags_SO //{NV,DZ,OF,UF,NX}
   );


   logic                                        Sign_res_D;

   logic                                        NV_OP_S;
   logic                                        Exp_OF_S;
   logic                                        Exp_UF_S;
   logic                                        Div_Zero_S;
   logic                                        In_Exact_S;

   /////////////////////////////////////////////////////////////////////////////
   // Normalization                                                           //
   /////////////////////////////////////////////////////////////////////////////
   logic [C_MANT_FP64:0]                        Mant_res_norm_D;
   logic [C_EXP_FP64-1:0]                       Exp_res_norm_D;

   /////////////////////////////////////////////////////////////////////////////
   // Right shift operations for negtive exponents                            //
   /////////////////////////////////////////////////////////////////////////////

  logic  [C_EXP_FP64+1:0]                       Exp_Max_RS_FP64_D;
  logic  [C_EXP_FP32+1:0]                       Exp_Max_RS_FP32_D;
  logic  [C_EXP_FP16+1:0]                       Exp_Max_RS_FP16_D;
  logic  [C_EXP_FP16ALT+1:0]                    Exp_Max_RS_FP16ALT_D;
  //
  assign Exp_Max_RS_FP64_D=Exp_in_DI[C_EXP_FP64:0]+C_MANT_FP64+1; // to check exponent after (C_MANT_FP64+1)-bit >> when Exp_in_DI is negative
  assign Exp_Max_RS_FP32_D=Exp_in_DI[C_EXP_FP32:0]+C_MANT_FP32+1; // to check exponent after (C_MANT_FP32+1)-bit >> when Exp_in_DI is negative
  assign Exp_Max_RS_FP16_D=Exp_in_DI[C_EXP_FP16:0]+C_MANT_FP16+1; // to check exponent after (C_MANT_FP16+1)-bit >> when Exp_in_DI is negative
  assign Exp_Max_RS_FP16ALT_D=Exp_in_DI[C_EXP_FP16ALT:0]+C_MANT_FP16ALT+1; // to check exponent after (C_MANT_FP16ALT+1)-bit >> when Exp_in_DI is negative
  logic  [C_EXP_FP64+1:0]                       Num_RS_D;
  assign Num_RS_D=~Exp_in_DI+1+1;            // How many right shifts(RS) are needed to generate a denormal number? >> is need only when Exp_in_DI is negative
  logic  [C_MANT_FP64:0]                        Mant_RS_D;
  logic  [C_MANT_FP64+4:0]                      Mant_forsticky_D;
  assign  {Mant_RS_D,Mant_forsticky_D} ={Mant_in_DI,{(C_MANT_FP64+1){1'b0}} } >>(Num_RS_D); //
//
  logic [C_EXP_FP64+1:0]                        Exp_subOne_D;
  assign Exp_subOne_D = Exp_in_DI -1;

   //normalization
   logic [1:0]                                  Mant_lower_D;
   logic                                        Mant_sticky_bit_D;
   logic [C_MANT_FP64+4:0]                      Mant_forround_D;

   always_comb
     begin

       if(NaN_a_SI)  //  if a is NaN, return NaN
         begin
           Div_Zero_S=1'b0;
           Exp_OF_S=1'b0;
           Exp_UF_S=1'b0;
           Mant_res_norm_D={1'b0,C_MANT_NAN_FP64};
           Exp_res_norm_D='1;
           Mant_forround_D='0;
           Sign_res_D=1'b0;
           NV_OP_S = SNaN_SI;
         end

      else if(NaN_b_SI)   //if b is NaN, return NaN
        begin
          Div_Zero_S=1'b0;
          Exp_OF_S=1'b0;
          Exp_UF_S=1'b0;
          Mant_res_norm_D={1'b0,C_MANT_NAN_FP64};
          Exp_res_norm_D='1;
          Mant_forround_D='0;
          Sign_res_D=1'b0;
          NV_OP_S = SNaN_SI;
        end

      else if(Inf_a_SI)
        begin
          if(Div_enable_SI&&Inf_b_SI)                     //Inf/Inf, retrurn NaN
            begin
              Div_Zero_S=1'b0;
              Exp_OF_S=1'b0;
              Exp_UF_S=1'b0;
              Mant_res_norm_D={1'b0,C_MANT_NAN_FP64};
              Exp_res_norm_D='1;
              Mant_forround_D='0;
              Sign_res_D=1'b0;
              NV_OP_S = 1'b1;
            end
          else if (Sqrt_enable_SI && Sign_in_DI) begin // catch sqrt(-inf)
            Div_Zero_S=1'b0;
            Exp_OF_S=1'b0;
            Exp_UF_S=1'b0;
            Mant_res_norm_D={1'b0,C_MANT_NAN_FP64};
            Exp_res_norm_D='1;
            Mant_forround_D='0;
            Sign_res_D=1'b0;
            NV_OP_S = 1'b1;
          end else begin
            Div_Zero_S=1'b0;
            Exp_OF_S=1'b1;
            Exp_UF_S=1'b0;
            Mant_res_norm_D= '0;
            Exp_res_norm_D='1;
            Mant_forround_D='0;
            Sign_res_D=Sign_in_DI;
            NV_OP_S = 1'b0;
          end
        end

      else if(Div_enable_SI&&Inf_b_SI)
        begin
          Div_Zero_S=1'b0;
          Exp_OF_S=1'b1;
          Exp_UF_S=1'b0;
          Mant_res_norm_D= '0;
          Exp_res_norm_D='0;
          Mant_forround_D='0;
          Sign_res_D=Sign_in_DI;
          NV_OP_S = 1'b0;
        end

     else if(Zero_a_SI)
       begin
         if(Div_enable_SI&&Zero_b_SI)
           begin
              Div_Zero_S=1'b1;
              Exp_OF_S=1'b0;
              Exp_UF_S=1'b0;
              Mant_res_norm_D={1'b0,C_MANT_NAN_FP64};
              Exp_res_norm_D='1;
              Mant_forround_D='0;
              Sign_res_D=1'b0;
              NV_OP_S = 1'b1;
           end
         else
           begin
             Div_Zero_S=1'b0;
             Exp_OF_S=1'b0;
             Exp_UF_S=1'b0;
             Mant_res_norm_D='0;
             Exp_res_norm_D='0;
             Mant_forround_D='0;
             Sign_res_D=Sign_in_DI;
             NV_OP_S = 1'b0;
           end
       end

     else  if(Div_enable_SI&&(Zero_b_SI))  //div Zero
       begin
         Div_Zero_S=1'b1;
         Exp_OF_S=1'b0;
         Exp_UF_S=1'b0;
         Mant_res_norm_D='0;
         Exp_res_norm_D='1;
         Mant_forround_D='0;
         Sign_res_D=Sign_in_DI;
         NV_OP_S = 1'b0;
       end

      else if(Sign_in_DI&&Sqrt_enable_SI)   //sqrt(-a)
        begin
          Div_Zero_S=1'b0;
          Exp_OF_S=1'b0;
          Exp_UF_S=1'b0;
          Mant_res_norm_D={1'b0,C_MANT_NAN_FP64};
          Exp_res_norm_D='1;
          Mant_forround_D='0;
          Sign_res_D=1'b0;
          NV_OP_S = 1'b1;
        end

     else if((Exp_in_DI[C_EXP_FP64:0]=='0))
       begin
         if(Mant_in_DI!='0)       //Exp=0, Mant!=0, it is denormal
           begin
             Div_Zero_S=1'b0;
             Exp_OF_S=1'b0;
             Exp_UF_S=1'b1;
             Mant_res_norm_D={1'b0,Mant_in_DI[C_MANT_FP64+4:5]};
             Exp_res_norm_D='0;
             Mant_forround_D={Mant_in_DI[4:0],{(C_MANT_FP64){1'b0}} };
             Sign_res_D=Sign_in_DI;
             NV_OP_S = 1'b0;
           end
         else                 // Zero
           begin
             Div_Zero_S=1'b0;
             Exp_OF_S=1'b0;
             Exp_UF_S=1'b0;
             Mant_res_norm_D='0;
             Exp_res_norm_D='0;
             Mant_forround_D='0;
             Sign_res_D=Sign_in_DI;
             NV_OP_S = 1'b0;
           end
        end

      else if((Exp_in_DI[C_EXP_FP64:0]==C_EXP_ONE_FP64)&&(~Mant_in_DI[C_MANT_FP64+4]))  //denormal
        begin
          Div_Zero_S=1'b0;
          Exp_OF_S=1'b0;
          Exp_UF_S=1'b1;
          Mant_res_norm_D=Mant_in_DI[C_MANT_FP64+4:4];
          Exp_res_norm_D='0;
          Mant_forround_D={Mant_in_DI[3:0],{(C_MANT_FP64+1){1'b0}}};
          Sign_res_D=Sign_in_DI;
          NV_OP_S = 1'b0;
        end

      else if(Exp_in_DI[C_EXP_FP64+1])    //minus              //consider format
        begin
          if(((~Exp_Max_RS_FP32_D[C_EXP_FP32+1])&&FP32_SI) | ((~Exp_Max_RS_FP64_D[C_EXP_FP64+1])&&FP64_SI) | ((~Exp_Max_RS_FP16_D[C_EXP_FP16+1])&&FP16_SI) | ((~Exp_Max_RS_FP16ALT_D[C_EXP_FP16ALT+1])&&FP16ALT_SI) )    //OF EXP<0 after RS
            begin
              Div_Zero_S=1'b0;
              Exp_OF_S=1'b1;
              Exp_UF_S=1'b0;
              Mant_res_norm_D='0;
              Exp_res_norm_D='0;
              Mant_forround_D='0;
              Sign_res_D=Sign_in_DI;
              NV_OP_S = 1'b0;
            end
          else                    //denormal
            begin
              Div_Zero_S=1'b0;
              Exp_OF_S=1'b0;
              Exp_UF_S=1'b1;
              Mant_res_norm_D={Mant_RS_D[C_MANT_FP64:0]};
              Exp_res_norm_D='0;
              Mant_forround_D={Mant_forsticky_D[C_MANT_FP64+4:0]};   //??
              Sign_res_D=Sign_in_DI;
              NV_OP_S = 1'b0;
            end
        end

      else if( (Exp_in_DI[C_EXP_FP32]&&FP32_SI) | (Exp_in_DI[C_EXP_FP64]&&FP64_SI) | (Exp_in_DI[C_EXP_FP16]&&FP16_SI) | (Exp_in_DI[C_EXP_FP16ALT]&&FP16ALT_SI) )            //OF
        begin
          Div_Zero_S=1'b0;
          Exp_OF_S=1'b1;
          Exp_UF_S=1'b0;
          Mant_res_norm_D='0;
          Exp_res_norm_D='1;
          Mant_forround_D='0;
          Sign_res_D=Sign_in_DI;
          NV_OP_S = 1'b0;
        end

      else if( ((Exp_in_DI[C_EXP_FP32-1:0]=='1)&&FP32_SI) | ((Exp_in_DI[C_EXP_FP64-1:0]=='1)&&FP64_SI) |  ((Exp_in_DI[C_EXP_FP16-1:0]=='1)&&FP16_SI) | ((Exp_in_DI[C_EXP_FP16ALT-1:0]=='1)&&FP16ALT_SI) )//255
        begin
          if(~Mant_in_DI[C_MANT_FP64+4]) // MSB=0
            begin
              Div_Zero_S=1'b0;
              Exp_OF_S=1'b0;
              Exp_UF_S=1'b0;
              Mant_res_norm_D=Mant_in_DI[C_MANT_FP64+3:3];
              Exp_res_norm_D=Exp_subOne_D;
              Mant_forround_D={Mant_in_DI[2:0],{(C_MANT_FP64+2){1'b0}}};
              Sign_res_D=Sign_in_DI;
              NV_OP_S = 1'b0;
            end
          else if(Mant_in_DI!='0)         //NaN
            begin
              Div_Zero_S=1'b0;
              Exp_OF_S=1'b1;
              Exp_UF_S=1'b0;
              Mant_res_norm_D= '0;
              Exp_res_norm_D='1;
              Mant_forround_D='0;
              Sign_res_D=Sign_in_DI;
              NV_OP_S = 1'b0;
            end
          else                         //infinity
            begin
              Div_Zero_S=1'b0;
              Exp_OF_S=1'b1;
              Exp_UF_S=1'b0;
              Mant_res_norm_D= '0;
              Exp_res_norm_D='1;
              Mant_forround_D='0;
              Sign_res_D=Sign_in_DI;
              NV_OP_S = 1'b0;
            end
         end

      else if(Mant_in_DI[C_MANT_FP64+4])  //normal numbers with 1.XXX
        begin
           Div_Zero_S=1'b0;
           Exp_OF_S=1'b0;
           Exp_UF_S=1'b0;
           Mant_res_norm_D= Mant_in_DI[C_MANT_FP64+4:4];
           Exp_res_norm_D=Exp_in_DI[C_EXP_FP64-1:0];
           Mant_forround_D={Mant_in_DI[3:0],{(C_MANT_FP64+1){1'b0}}};
           Sign_res_D=Sign_in_DI;
           NV_OP_S = 1'b0;
        end

      else                                   //normal numbers with 0.1XX
         begin
           Div_Zero_S=1'b0;
           Exp_OF_S=1'b0;
           Exp_UF_S=1'b0;
           Mant_res_norm_D=Mant_in_DI[C_MANT_FP64+3:3];
           Exp_res_norm_D=Exp_subOne_D;
           Mant_forround_D={Mant_in_DI[2:0],{(C_MANT_FP64+2){1'b0}}};
           Sign_res_D=Sign_in_DI;
           NV_OP_S = 1'b0;
         end

     end

   /////////////////////////////////////////////////////////////////////////////
   // Rounding enable only for full precision (Full_precision_SI==1'b1)       //
   /////////////////////////////////////////////////////////////////////////////

   logic [C_MANT_FP64:0]                   Mant_upper_D;
   logic [C_MANT_FP64+1:0]                 Mant_upperRounded_D;
   logic                                   Mant_roundUp_S;
   logic                                   Mant_rounded_S;

  always_comb //determine which bits for Mant_lower_D and Mant_sticky_bit_D
    begin
      if(FP32_SI)
        begin
          Mant_upper_D = {Mant_res_norm_D[C_MANT_FP64:C_MANT_FP64-C_MANT_FP32], {(C_MANT_FP64-C_MANT_FP32){1'b0}} };
          Mant_lower_D = Mant_res_norm_D[C_MANT_FP64-C_MANT_FP32-1:C_MANT_FP64-C_MANT_FP32-2];
          Mant_sticky_bit_D = | Mant_res_norm_D[C_MANT_FP64-C_MANT_FP32-3:0];
        end
      else if(FP64_SI)
        begin
          Mant_upper_D = Mant_res_norm_D[C_MANT_FP64:0];
          Mant_lower_D = Mant_forround_D[C_MANT_FP64+4:C_MANT_FP64+3];
          Mant_sticky_bit_D = | Mant_forround_D[C_MANT_FP64+3:0];
        end
      else if(FP16_SI)
        begin
          Mant_upper_D = {Mant_res_norm_D[C_MANT_FP64:C_MANT_FP64-C_MANT_FP16], {(C_MANT_FP64-C_MANT_FP16){1'b0}} };
          Mant_lower_D = Mant_res_norm_D[C_MANT_FP64-C_MANT_FP16-1:C_MANT_FP64-C_MANT_FP16-2];
          Mant_sticky_bit_D = | Mant_res_norm_D[C_MANT_FP64-C_MANT_FP16-3:30];
        end
      else  //FP16ALT
      begin
          Mant_upper_D = {Mant_res_norm_D[C_MANT_FP64:C_MANT_FP64-C_MANT_FP16ALT], {(C_MANT_FP64-C_MANT_FP16ALT){1'b0}} };
          Mant_lower_D = Mant_res_norm_D[C_MANT_FP64-C_MANT_FP16ALT-1:C_MANT_FP64-C_MANT_FP16ALT-2];
          Mant_sticky_bit_D = | Mant_res_norm_D[C_MANT_FP64-C_MANT_FP16ALT-3:30];
      end
    end

   assign Mant_rounded_S = (|(Mant_lower_D))| Mant_sticky_bit_D;




   always_comb //determine whether to round up or not
     begin
        Mant_roundUp_S = 1'b0;
        case (RM_SI)
          C_RM_NEAREST :
            Mant_roundUp_S = Mant_lower_D[1] && ((Mant_lower_D[0] | Mant_sticky_bit_D )| ( (FP32_SI&&Mant_upper_D[C_MANT_FP64-C_MANT_FP32]) | (FP64_SI&&Mant_upper_D[0]) | (FP16_SI&&Mant_upper_D[C_MANT_FP64-C_MANT_FP16]) | (FP16ALT_SI&&Mant_upper_D[C_MANT_FP64-C_MANT_FP16ALT]) ) );
          C_RM_TRUNC   :
            Mant_roundUp_S = 0;
          C_RM_PLUSINF :
            Mant_roundUp_S = Mant_rounded_S & ~Sign_in_DI;
          C_RM_MINUSINF:
            Mant_roundUp_S = Mant_rounded_S & Sign_in_DI;
          default          :
            Mant_roundUp_S = 0;
        endcase // case (RM_DI)
     end // always_comb begin

  logic                                 Mant_renorm_S;
  logic  [C_MANT_FP64:0]                Mant_roundUp_Vector_S; // for all the formats

  assign Mant_roundUp_Vector_S={7'h0,(FP16ALT_SI&&Mant_roundUp_S),2'h0,(FP16_SI&&Mant_roundUp_S),12'h0,(FP32_SI&&Mant_roundUp_S),28'h0,(FP64_SI&&Mant_roundUp_S)};


  assign Mant_upperRounded_D = Mant_upper_D + Mant_roundUp_Vector_S;
  assign Mant_renorm_S       = Mant_upperRounded_D[C_MANT_FP64+1];

  /////////////////////////////////////////////////////////////////////////////
  // Renormalization for Rounding                                           //
  /////////////////////////////////////////////////////////////////////////////
  logic [C_MANT_FP64-1:0]               Mant_res_round_D;
  logic [C_EXP_FP64-1:0]                Exp_res_round_D;


  assign Mant_res_round_D = (Mant_renorm_S)?Mant_upperRounded_D[C_MANT_FP64:1]:Mant_upperRounded_D[C_MANT_FP64-1:0]; // including the process of the hidden bit
  assign Exp_res_round_D  = Exp_res_norm_D+Mant_renorm_S;

  /////////////////////////////////////////////////////////////////////////////
  //  Output Assignments                                                     //
  /////////////////////////////////////////////////////////////////////////////
  logic [C_MANT_FP64-1:0]               Mant_before_format_ctl_D;
  logic [C_EXP_FP64-1:0]                Exp_before_format_ctl_D;
  assign Mant_before_format_ctl_D = Full_precision_SI ? Mant_res_round_D : Mant_res_norm_D;
  assign Exp_before_format_ctl_D = Full_precision_SI ? Exp_res_round_D : Exp_res_norm_D;

  always_comb    //NaN Boxing
    begin  //
      if(FP32_SI)
          begin
            Result_DO ={32'hffff_ffff,Sign_res_D,Exp_before_format_ctl_D[C_EXP_FP32-1:0],Mant_before_format_ctl_D[C_MANT_FP64-1:C_MANT_FP64-C_MANT_FP32]};
          end
       else if(FP64_SI)
          begin
            Result_DO ={Sign_res_D,Exp_before_format_ctl_D[C_EXP_FP64-1:0],Mant_before_format_ctl_D[C_MANT_FP64-1:0]};
          end
      else if(FP16_SI)
          begin
            Result_DO ={48'hffff_ffff_ffff,Sign_res_D,Exp_before_format_ctl_D[C_EXP_FP16-1:0],Mant_before_format_ctl_D[C_MANT_FP64-1:C_MANT_FP64-C_MANT_FP16]};
          end
      else
          begin
            Result_DO ={48'hffff_ffff_ffff,Sign_res_D,Exp_before_format_ctl_D[C_EXP_FP16ALT-1:0],Mant_before_format_ctl_D[C_MANT_FP64-1:C_MANT_FP64-C_MANT_FP16ALT]};
          end
    end

assign In_Exact_S = (~Full_precision_SI) | Mant_rounded_S;
assign Fflags_SO = {NV_OP_S,Div_Zero_S,Exp_OF_S,Exp_UF_S,In_Exact_S}; //{NV,DZ,OF,UF,NX}

endmodule // norm_div_sqrt_mvp
