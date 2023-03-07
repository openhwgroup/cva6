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
// Engineers:      Lei Li                    lile@iis.ee.ethz.ch              //
//                                                                            //
// Additional contributions by:                                               //
//                                                                            //
//                                                                            //
//                                                                            //
// Create Date:    04/03/2018                                                 //
// Design Name:    FPU                                                        //
// Module Name:    control_mvp.sv                                             //
// Project Name:   Private FPU                                                //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    the control logic  of div and sqrt                         //
//                                                                            //
// Revision Date:  12/04/2018                                                 //
//                 Lei Li                                                     //
//                 To address some requirements by Stefan and add low power   //
//                 control for special cases                                  //
// Revision Date:  13/04/2018                                                 //
//                 Lei Li                                                     //
//                 To fix some bug found in Control FSM                       //
//                 when Iteration_unit_num_S  = 2'b10                         //
//                                                                            //
//                                                                            //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

import defs_div_sqrt_mvp::*;

module control_mvp

  (//Input
   input logic                                        Clk_CI,
   input logic                                        Rst_RBI,
   input logic                                        Div_start_SI ,
   input logic                                        Sqrt_start_SI,
   input logic                                        Start_SI,
   input logic                                        Kill_SI,
   input logic                                        Special_case_SBI,
   input logic                                        Special_case_dly_SBI,
   input logic [C_PC-1:0]                             Precision_ctl_SI,
   input logic [1:0]                                  Format_sel_SI,
   input logic [C_MANT_FP64:0]                        Numerator_DI,
   input logic [C_EXP_FP64:0]                         Exp_num_DI,
   input logic [C_MANT_FP64:0]                        Denominator_DI,
   input logic [C_EXP_FP64:0]                         Exp_den_DI,


   output logic                                       Div_start_dly_SO ,
   output logic                                       Sqrt_start_dly_SO,
   output logic                                       Div_enable_SO,
   output logic                                       Sqrt_enable_SO,


   //To next stage
   output logic                                       Full_precision_SO,
   output logic                                       FP32_SO,
   output logic                                       FP64_SO,
   output logic                                       FP16_SO,
   output logic                                       FP16ALT_SO,

   output logic                                       Ready_SO,
   output logic                                       Done_SO,

   output logic [C_MANT_FP64+4:0]                     Mant_result_prenorm_DO,
 //  output logic [3:0]                                 Round_bit_DO,
   output logic [C_EXP_FP64+1:0]                      Exp_result_prenorm_DO
 );

   logic  [C_MANT_FP64+1+4:0]                         Partial_remainder_DN,Partial_remainder_DP; //58bits,r=q+2
   logic  [C_MANT_FP64+4:0]                           Quotient_DP; //57bits
   /////////////////////////////////////////////////////////////////////////////
   // Assign Inputs                                                          //
   /////////////////////////////////////////////////////////////////////////////
   logic [C_MANT_FP64+1:0]                            Numerator_se_D;  //sign extension and hidden bit
   logic [C_MANT_FP64+1:0]                            Denominator_se_D; //signa extension and hidden bit
   logic [C_MANT_FP64+1:0]                            Denominator_se_DB;  //1's complement

   assign  Numerator_se_D={1'b0,Numerator_DI};

   assign  Denominator_se_D={1'b0,Denominator_DI};

  always_comb
   begin
     if(FP32_SO)
       begin
         Denominator_se_DB={~Denominator_se_D[C_MANT_FP64+1:C_MANT_FP64-C_MANT_FP32], {(C_MANT_FP64-C_MANT_FP32){1'b0}} };
       end
     else if(FP64_SO) begin
         Denominator_se_DB=~Denominator_se_D;
     end
     else if(FP16_SO) begin
         Denominator_se_DB={~Denominator_se_D[C_MANT_FP64+1:C_MANT_FP64-C_MANT_FP16], {(C_MANT_FP64-C_MANT_FP16){1'b0}} };
     end
     else begin
         Denominator_se_DB={~Denominator_se_D[C_MANT_FP64+1:C_MANT_FP64-C_MANT_FP16ALT], {(C_MANT_FP64-C_MANT_FP16ALT){1'b0}} };
     end
   end


   logic [C_MANT_FP64+1:0]                            Mant_D_sqrt_Norm;

   assign Mant_D_sqrt_Norm=Exp_num_DI[0]?{1'b0,Numerator_DI}:{Numerator_DI,1'b0}; //for sqrt

   /////////////////////////////////////////////////////////////////////////////
   // Format Selection                                                       //
   /////////////////////////////////////////////////////////////////////////////
   logic [1:0]                                      Format_sel_S;

   always_ff @(posedge Clk_CI, negedge Rst_RBI)
     begin
        if(~Rst_RBI)
          begin
            Format_sel_S<='b0;
          end
        else if(Start_SI&&Ready_SO)
          begin
            Format_sel_S<=Format_sel_SI;
          end
        else
          begin
            Format_sel_S<=Format_sel_S;
          end
    end

   assign FP32_SO = (Format_sel_S==2'b00);
   assign FP64_SO = (Format_sel_S==2'b01);
   assign FP16_SO = (Format_sel_S==2'b10);
   assign FP16ALT_SO = (Format_sel_S==2'b11);



   /////////////////////////////////////////////////////////////////////////////
   // Precision Control                                                       //
   /////////////////////////////////////////////////////////////////////////////

   logic [C_PC-1:0]                                   Precision_ctl_S;
   always_ff @(posedge Clk_CI, negedge Rst_RBI)
     begin
        if(~Rst_RBI)
          begin
            Precision_ctl_S<='b0;
          end
        else if(Start_SI&&Ready_SO)
          begin
            Precision_ctl_S<=Precision_ctl_SI;
          end
        else
          begin
            Precision_ctl_S<=Precision_ctl_S;
          end
    end
  assign Full_precision_SO = (Precision_ctl_S==6'h00);



     logic [5:0]                                     State_ctl_S;
     logic [5:0]                                     State_Two_iteration_unit_S;
     logic [5:0]                                     State_Four_iteration_unit_S;

    assign State_Two_iteration_unit_S = Precision_ctl_S[C_PC-1:1];  //Two iteration units
    assign State_Four_iteration_unit_S = Precision_ctl_S[C_PC-1:2];  //Four iteration units
     always_comb
       begin
         case(Iteration_unit_num_S)
//////////////////////one iteration unit, start///////////////////////////////////////
           2'b00:  //one iteration unit
             begin
               case(Format_sel_S)
                 2'b00: //FP32
                   begin
                     if(Full_precision_SO)
                       begin
                         State_ctl_S = 6'h1b;  //24+4 more iterations for rounding bits
                       end
                     else
                       begin
                         State_ctl_S = Precision_ctl_S;
                       end
                   end
                 2'b01: //FP64
                   begin
                     if(Full_precision_SO)
                       begin
                         State_ctl_S = 6'h38;  //53+4 more iterations for rounding bits
                       end
                     else
                       begin
                         State_ctl_S = Precision_ctl_S;
                       end
                   end
                 2'b10: //FP16
                   begin
                     if(Full_precision_SO)
                       begin
                         State_ctl_S = 6'h0e;  //11+4 more iterations for rounding bits
                       end
                     else
                       begin
                         State_ctl_S = Precision_ctl_S;
                       end
                   end
                 2'b11: //FP16ALT
                   begin
                     if(Full_precision_SO)
                       begin
                         State_ctl_S = 6'h0b;  //8+4 more iterations for rounding bits
                       end
                     else
                       begin
                         State_ctl_S = Precision_ctl_S;
                       end
                  end
                endcase
              end
//////////////////////one iteration unit, end///////////////////////////////////////

//////////////////////two iteration units, start///////////////////////////////////////
           2'b01:  //two iteration units
             begin
               case(Format_sel_S)
                 2'b00: //FP32
                   begin
                     if(Full_precision_SO)
                       begin
                         State_ctl_S = 6'h0d;  //24+4 more iterations for rounding bits
                       end
                     else
                       begin
                         State_ctl_S = State_Two_iteration_unit_S;
                       end
                   end
                 2'b01: //FP64
                   begin
                     if(Full_precision_SO)
                       begin
                         State_ctl_S = 6'h1b;  //53+3 more iterations for rounding bits
                       end
                     else
                       begin
                         State_ctl_S = State_Two_iteration_unit_S;
                       end
                   end
                 2'b10: //FP16
                   begin
                     if(Full_precision_SO)
                       begin
                         State_ctl_S = 6'h06;  //11+3 more iterations for rounding bits
                       end
                     else
                       begin
                         State_ctl_S = State_Two_iteration_unit_S;
                       end
                   end
                 2'b11: //FP16ALT
                   begin
                     if(Full_precision_SO)
                       begin
                         State_ctl_S = 6'h05;  //8+4 more iterations for rounding bits
                       end
                     else
                       begin
                         State_ctl_S = State_Two_iteration_unit_S;
                       end
                  end
                endcase
              end
//////////////////////two iteration units, end///////////////////////////////////////

//////////////////////three iteration units, start///////////////////////////////////////
           2'b10:  //three iteration units
             begin
               case(Format_sel_S)
                 2'b00: //FP32
                   begin
                     case(Precision_ctl_S)
                       6'h00:
                         begin
                           State_ctl_S = 6'h08;  //24+3 more iterations for rounding bits
                         end
                       6'h06,6'h07,6'h08:
                         begin
                           State_ctl_S = 6'h02;
                         end
                       6'h09,6'h0a,6'h0b:
                         begin
                           State_ctl_S = 6'h03;
                         end
                       6'h0c,6'h0d,6'h0e:
                         begin
                           State_ctl_S = 6'h04;
                         end
                       6'h0f,6'h10,6'h11:
                         begin
                           State_ctl_S = 6'h05;
                         end
                       6'h12,6'h13,6'h14:
                         begin
                           State_ctl_S = 6'h06;
                         end
                       6'h15,6'h16,6'h17:
                         begin
                           State_ctl_S = 6'h07;
                         end
                       default:
                         begin
                           State_ctl_S = 6'h08;  //24+3 more iterations for rounding bits
                         end
                     endcase
                   end
                 2'b01: //FP64
                   begin
                     case(Precision_ctl_S)
                       6'h00:
                         begin
                           State_ctl_S = 6'h12;  //53+4 more iterations for rounding bits
                         end
                       6'h06,6'h07,6'h08:
                         begin
                           State_ctl_S = 6'h02;
                         end
                       6'h09,6'h0a,6'h0b:
                         begin
                           State_ctl_S = 6'h03;
                         end
                       6'h0c,6'h0d,6'h0e:
                         begin
                           State_ctl_S = 6'h04;
                         end
                       6'h0f,6'h10,6'h11:
                         begin
                           State_ctl_S = 6'h05;
                         end
                       6'h12,6'h13,6'h14:
                         begin
                           State_ctl_S = 6'h06;
                         end
                       6'h15,6'h16,6'h17:
                         begin
                           State_ctl_S = 6'h07;
                         end
                       6'h18,6'h19,6'h1a:
                         begin
                           State_ctl_S = 6'h08;
                         end
                       6'h1b,6'h1c,6'h1d:
                         begin
                           State_ctl_S = 6'h09;
                         end
                       6'h1e,6'h1f,6'h20:
                         begin
                           State_ctl_S = 6'h0a;
                         end
                       6'h21,6'h22,6'h23:
                         begin
                           State_ctl_S = 6'h0b;
                         end
                       6'h24,6'h25,6'h26:
                         begin
                           State_ctl_S = 6'h0c;
                         end
                       6'h27,6'h28,6'h29:
                         begin
                           State_ctl_S = 6'h0d;
                         end
                       6'h2a,6'h2b,6'h2c:
                         begin
                           State_ctl_S = 6'h0e;
                         end
                       6'h2d,6'h2e,6'h2f:
                         begin
                           State_ctl_S = 6'h0f;
                         end
                       6'h30,6'h31,6'h32:
                         begin
                           State_ctl_S = 6'h10;
                         end
                       6'h33,6'h34,6'h35:
                         begin
                           State_ctl_S = 6'h11;
                         end
                       default:
                         begin
                           State_ctl_S = 6'h12;  //53+4 more iterations for rounding bits
                         end
                     endcase
                   end
                 2'b10: //FP16
                   begin
                     case(Precision_ctl_S)
                       6'h00:
                         begin
                           State_ctl_S = 6'h04;  //12+3 more iterations for rounding bits
                         end
                       6'h06,6'h07,6'h08:
                         begin
                           State_ctl_S = 6'h02;
                         end
                       6'h09,6'h0a,6'h0b:
                         begin
                           State_ctl_S = 6'h03;
                         end
                       default:
                         begin
                           State_ctl_S = 6'h04;  //12+3 more iterations for rounding bits
                         end
                     endcase
                   end
                 2'b11: //FP16ALT
                   begin
                     case(Precision_ctl_S)
                       6'h00:
                         begin
                           State_ctl_S = 6'h03;  //8+4 more iterations for rounding bits
                         end
                       6'h06,6'h07,6'h08:
                         begin
                           State_ctl_S = 6'h02;
                         end
                       default:
                         begin
                           State_ctl_S = 6'h03;  //8+4 more iterations for rounding bits
                         end
                     endcase
                  end
                endcase
              end
//////////////////////three iteration units, end///////////////////////////////////////

//////////////////////four iteration units, start///////////////////////////////////////
           2'b11:  //four iteration units
             begin
               case(Format_sel_S)
                 2'b00: //FP32
                   begin
                     if(Full_precision_SO)
                       begin
                         State_ctl_S = 6'h06;  //24+4 more iterations for rounding bits
                       end
                     else
                       begin
                         State_ctl_S = State_Four_iteration_unit_S;
                       end
                   end
                 2'b01: //FP64
                   begin
                     if(Full_precision_SO)
                       begin
                         State_ctl_S = 6'h0d;  //53+3 more iterations for rounding bits
                       end
                     else
                       begin
                         State_ctl_S = State_Four_iteration_unit_S;
                       end
                   end
                 2'b10: //FP16
                   begin
                     if(Full_precision_SO)
                       begin
                         State_ctl_S = 6'h03;  //11+4 more iterations for rounding bits
                       end
                     else
                       begin
                         State_ctl_S = State_Four_iteration_unit_S;
                       end
                   end
                 2'b11: //FP16ALT
                   begin
                     if(Full_precision_SO)
                       begin
                         State_ctl_S = 6'h02;  //8+4 more iterations for rounding bits
                       end
                     else
                       begin
                         State_ctl_S = State_Four_iteration_unit_S;
                       end
                  end
                endcase
              end
//////////////////////four iteration units, end///////////////////////////////////////

           endcase
        end


   /////////////////////////////////////////////////////////////////////////////
   // control logic                                                           //
   /////////////////////////////////////////////////////////////////////////////

   logic                                               Div_start_dly_S;

   always_ff @(posedge Clk_CI, negedge Rst_RBI)   //  generate Div_start_dly_S signal
     begin
        if(~Rst_RBI)
          begin
            Div_start_dly_S<=1'b0;
          end
        else if(Div_start_SI&&Ready_SO)
         begin
           Div_start_dly_S<=1'b1;
         end
        else
          begin
            Div_start_dly_S<=1'b0;
          end
    end

   assign Div_start_dly_SO=Div_start_dly_S;

  always_ff @(posedge Clk_CI, negedge Rst_RBI) begin  //  generate Div_enable_SO signal
    if(~Rst_RBI)
      Div_enable_SO<=1'b0;
    // Synchronous reset with Flush
    else if (Kill_SI)
      Div_enable_SO <= 1'b0;
    else if(Div_start_SI&&Ready_SO)
      Div_enable_SO<=1'b1;
    else if(Done_SO)
      Div_enable_SO<=1'b0;
    else
      Div_enable_SO<=Div_enable_SO;
  end

   logic                                                Sqrt_start_dly_S;

   always_ff @(posedge Clk_CI, negedge Rst_RBI)   //  generate Sqrt_start_dly_SI signal
     begin
        if(~Rst_RBI)
          begin
            Sqrt_start_dly_S<=1'b0;
          end
        else if(Sqrt_start_SI&&Ready_SO)
         begin
           Sqrt_start_dly_S<=1'b1;
         end
        else
          begin
            Sqrt_start_dly_S<=1'b0;
          end
      end
    assign Sqrt_start_dly_SO=Sqrt_start_dly_S;

   always_ff @(posedge Clk_CI, negedge Rst_RBI) begin   //  generate Sqrt_enable_SO signal
    if(~Rst_RBI)
      Sqrt_enable_SO<=1'b0;
    else if (Kill_SI)
      Sqrt_enable_SO <= 1'b0;
    else if(Sqrt_start_SI&&Ready_SO)
      Sqrt_enable_SO<=1'b1;
    else if(Done_SO)
      Sqrt_enable_SO<=1'b0;
    else
      Sqrt_enable_SO<=Sqrt_enable_SO;
  end

   logic [5:0]                                                  Crtl_cnt_S;
   logic                                                        Start_dly_S;

   assign   Start_dly_S=Div_start_dly_S |Sqrt_start_dly_S;

   logic       Fsm_enable_S;
   assign      Fsm_enable_S=( (Start_dly_S | (| Crtl_cnt_S)) && (~Kill_SI) && Special_case_dly_SBI);

   logic                                                        Final_state_S;
   assign     Final_state_S= (Crtl_cnt_S==State_ctl_S);


   always_ff @(posedge Clk_CI, negedge Rst_RBI) //control_FSM
     begin
        if (~Rst_RBI)
          begin
             Crtl_cnt_S    <= '0;
          end
          else if (Final_state_S | Kill_SI)
            begin
              Crtl_cnt_S    <= '0;
            end
          else if(Fsm_enable_S) // one cycle Start_SI
            begin
              Crtl_cnt_S    <= Crtl_cnt_S+1;
            end
          else
            begin
              Crtl_cnt_S    <= '0;
            end
     end // always_ff



    always_ff @(posedge Clk_CI, negedge Rst_RBI) //Generate  Done_SO,  they can share this Done_SO.
      begin
        if(~Rst_RBI)
          begin
            Done_SO<=1'b0;
          end
        else if(Start_SI&&Ready_SO)
          begin
            if(~Special_case_SBI)
              begin
                Done_SO<=1'b1;
              end
            else
              begin
                Done_SO<=1'b0;
              end
          end
        else if(Final_state_S)
          begin
            Done_SO<=1'b1;
          end
        else
          begin
            Done_SO<=1'b0;
          end
       end




   always_ff @(posedge Clk_CI, negedge Rst_RBI) //Generate  Ready_SO
     begin
       if(~Rst_RBI)
         begin
           Ready_SO<=1'b1;
         end

       else if(Start_SI&&Ready_SO)
         begin
            if(~Special_case_SBI)
              begin
                Ready_SO<=1'b1;
              end
            else
              begin
                Ready_SO<=1'b0;
              end
         end
       else if(Final_state_S | Kill_SI)
         begin
           Ready_SO<=1'b1;
         end
       else
         begin
           Ready_SO<=Ready_SO;
         end
     end


  /////////////////////////////////////////////////////////////////////////////
   // Declarations for square root when Iteration_unit_num_S = 2'b00, start  //
   ////////////////////////////////////////////////////////////////////////////

  logic                                    Qcnt_one_0;
  logic                                    Qcnt_one_1;
  logic [1:0]                              Qcnt_one_2;
  logic [2:0]                              Qcnt_one_3;
  logic [3:0]                              Qcnt_one_4;
  logic [4:0]                              Qcnt_one_5;
  logic [5:0]                              Qcnt_one_6;
  logic [6:0]                              Qcnt_one_7;
  logic [7:0]                              Qcnt_one_8;
  logic [8:0]                              Qcnt_one_9;
  logic [9:0]                              Qcnt_one_10;
  logic [10:0]                             Qcnt_one_11;
  logic [11:0]                             Qcnt_one_12;
  logic [12:0]                             Qcnt_one_13;
  logic [13:0]                             Qcnt_one_14;
  logic [14:0]                             Qcnt_one_15;
  logic [15:0]                             Qcnt_one_16;
  logic [16:0]                             Qcnt_one_17;
  logic [17:0]                             Qcnt_one_18;
  logic [18:0]                             Qcnt_one_19;
  logic [19:0]                             Qcnt_one_20;
  logic [20:0]                             Qcnt_one_21;
  logic [21:0]                             Qcnt_one_22;
  logic [22:0]                             Qcnt_one_23;
  logic [23:0]                             Qcnt_one_24;
  logic [24:0]                             Qcnt_one_25;
  logic [25:0]                             Qcnt_one_26;
  logic [26:0]                             Qcnt_one_27;
  logic [27:0]                             Qcnt_one_28;
  logic [28:0]                             Qcnt_one_29;
  logic [29:0]                             Qcnt_one_30;
  logic [30:0]                             Qcnt_one_31;
  logic [31:0]                             Qcnt_one_32;
  logic [32:0]                             Qcnt_one_33;
  logic [33:0]                             Qcnt_one_34;
  logic [34:0]                             Qcnt_one_35;
  logic [35:0]                             Qcnt_one_36;
  logic [36:0]                             Qcnt_one_37;
  logic [37:0]                             Qcnt_one_38;
  logic [38:0]                             Qcnt_one_39;
  logic [39:0]                             Qcnt_one_40;
  logic [40:0]                             Qcnt_one_41;
  logic [41:0]                             Qcnt_one_42;
  logic [42:0]                             Qcnt_one_43;
  logic [43:0]                             Qcnt_one_44;
  logic [44:0]                             Qcnt_one_45;
  logic [45:0]                             Qcnt_one_46;
  logic [46:0]                             Qcnt_one_47;
  logic [47:0]                             Qcnt_one_48;
  logic [48:0]                             Qcnt_one_49;
  logic [49:0]                             Qcnt_one_50;
  logic [50:0]                             Qcnt_one_51;
  logic [51:0]                             Qcnt_one_52;
  logic [52:0]                             Qcnt_one_53;
  logic [53:0]                             Qcnt_one_54;
  logic [54:0]                             Qcnt_one_55;
  logic [55:0]                             Qcnt_one_56;
  logic [56:0]                             Qcnt_one_57;
  logic [57:0]                             Qcnt_one_58;
  logic [58:0]                             Qcnt_one_59;
  logic [59:0]                             Qcnt_one_60;

  /////////////////////////////////////////////////////////////////////////////
   // Declarations for square root when Iteration_unit_num_S = 2'b00, end    //
   ////////////////////////////////////////////////////////////////////////////



  /////////////////////////////////////////////////////////////////////////////
   // Declarations for square root when Iteration_unit_num_S = 2'b01, start  //
   ////////////////////////////////////////////////////////////////////////////
  logic [1:0]                              Qcnt_two_0;
  logic [2:0]                              Qcnt_two_1;
  logic [4:0]                              Qcnt_two_2;
  logic [6:0]                              Qcnt_two_3;
  logic [8:0]                              Qcnt_two_4;
  logic [10:0]                             Qcnt_two_5;
  logic [12:0]                             Qcnt_two_6;
  logic [14:0]                             Qcnt_two_7;
  logic [16:0]                             Qcnt_two_8;
  logic [18:0]                             Qcnt_two_9;
  logic [20:0]                             Qcnt_two_10;
  logic [22:0]                             Qcnt_two_11;
  logic [24:0]                             Qcnt_two_12;
  logic [26:0]                             Qcnt_two_13;
  logic [28:0]                             Qcnt_two_14;
  logic [30:0]                             Qcnt_two_15;
  logic [32:0]                             Qcnt_two_16;
  logic [34:0]                             Qcnt_two_17;
  logic [36:0]                             Qcnt_two_18;
  logic [38:0]                             Qcnt_two_19;
  logic [40:0]                             Qcnt_two_20;
  logic [42:0]                             Qcnt_two_21;
  logic [44:0]                             Qcnt_two_22;
  logic [46:0]                             Qcnt_two_23;
  logic [48:0]                             Qcnt_two_24;
  logic [50:0]                             Qcnt_two_25;
  logic [52:0]                             Qcnt_two_26;
  logic [54:0]                             Qcnt_two_27;
  logic [56:0]                             Qcnt_two_28;
  /////////////////////////////////////////////////////////////////////////////
   // Declarations for square root when Iteration_unit_num_S = 2'b01, end    //
   ////////////////////////////////////////////////////////////////////////////


  /////////////////////////////////////////////////////////////////////////////
   // Declarations for square root when Iteration_unit_num_S = 2'b10, start  //
   ////////////////////////////////////////////////////////////////////////////
  logic [2:0]                              Qcnt_three_0;
  logic [4:0]                              Qcnt_three_1;
  logic [7:0]                              Qcnt_three_2;
  logic [10:0]                             Qcnt_three_3;
  logic [13:0]                             Qcnt_three_4;
  logic [16:0]                             Qcnt_three_5;
  logic [19:0]                             Qcnt_three_6;
  logic [22:0]                             Qcnt_three_7;
  logic [25:0]                             Qcnt_three_8;
  logic [28:0]                             Qcnt_three_9;
  logic [31:0]                             Qcnt_three_10;
  logic [34:0]                             Qcnt_three_11;
  logic [37:0]                             Qcnt_three_12;
  logic [40:0]                             Qcnt_three_13;
  logic [43:0]                             Qcnt_three_14;
  logic [46:0]                             Qcnt_three_15;
  logic [49:0]                             Qcnt_three_16;
  logic [52:0]                             Qcnt_three_17;
  logic [55:0]                             Qcnt_three_18;
  logic [58:0]                             Qcnt_three_19;
  logic [61:0]                             Qcnt_three_20;
  /////////////////////////////////////////////////////////////////////////////
   // Declarations for square root when Iteration_unit_num_S = 2'b10, end    //
   ////////////////////////////////////////////////////////////////////////////


  /////////////////////////////////////////////////////////////////////////////
   // Declarations for square root when Iteration_unit_num_S = 2'b11, start  //
   ////////////////////////////////////////////////////////////////////////////
  logic [3:0]                              Qcnt_four_0;
  logic [6:0]                              Qcnt_four_1;
  logic [10:0]                             Qcnt_four_2;
  logic [14:0]                             Qcnt_four_3;
  logic [18:0]                             Qcnt_four_4;
  logic [22:0]                             Qcnt_four_5;
  logic [26:0]                             Qcnt_four_6;
  logic [30:0]                             Qcnt_four_7;
  logic [34:0]                             Qcnt_four_8;
  logic [38:0]                             Qcnt_four_9;
  logic [42:0]                             Qcnt_four_10;
  logic [46:0]                             Qcnt_four_11;
  logic [50:0]                             Qcnt_four_12;
  logic [54:0]                             Qcnt_four_13;
  logic [58:0]                             Qcnt_four_14;

  /////////////////////////////////////////////////////////////////////////////
   // Declarations for square root when Iteration_unit_num_S = 2'b11, end    //
   ////////////////////////////////////////////////////////////////////////////



   logic [C_MANT_FP64+1+4:0]                                      Sqrt_R0,Sqrt_Q0,Q_sqrt0,Q_sqrt_com_0;
   logic [C_MANT_FP64+1+4:0]                                      Sqrt_R1,Sqrt_Q1,Q_sqrt1,Q_sqrt_com_1;
   logic [C_MANT_FP64+1+4:0]                                      Sqrt_R2,Sqrt_Q2,Q_sqrt2,Q_sqrt_com_2;
   logic [C_MANT_FP64+1+4:0]                                      Sqrt_R3,Sqrt_Q3,Q_sqrt3,Q_sqrt_com_3,Sqrt_R4; //Sqrt_Q4;


   logic [1:0]                                                    Sqrt_DI  [3:0];
   logic [1:0]                                                    Sqrt_DO  [3:0];
   logic                                                          Sqrt_carry_DO;


  logic  [C_MANT_FP64+1+4:0]                                      Iteration_cell_a_D [3:0];
  logic  [C_MANT_FP64+1+4:0]                                      Iteration_cell_b_D [3:0];
  logic  [C_MANT_FP64+1+4:0]                                      Iteration_cell_a_BMASK_D [3:0];
  logic  [C_MANT_FP64+1+4:0]                                      Iteration_cell_b_BMASK_D [3:0];
  logic                                                           Iteration_cell_carry_D [3:0];
  logic  [C_MANT_FP64+1+4:0]                                      Iteration_cell_sum_D [3:0];
  logic  [C_MANT_FP64+1+4:0]                                      Iteration_cell_sum_AMASK_D [3:0];


  logic [3:0]                                                     Sqrt_quotinent_S;


   always_comb
    begin  //
      case (Format_sel_S)
        2'b00:
          begin
            Sqrt_quotinent_S = {(~Iteration_cell_sum_AMASK_D[0][C_MANT_FP32+5]),(~Iteration_cell_sum_AMASK_D[1][C_MANT_FP32+5]),(~Iteration_cell_sum_AMASK_D[2][C_MANT_FP32+5]),(~Iteration_cell_sum_AMASK_D[3][C_MANT_FP32+5])};
            Q_sqrt_com_0 ={ {(C_MANT_FP64-C_MANT_FP32){1'b0}},~Q_sqrt0[C_MANT_FP32+5:0] };
            Q_sqrt_com_1 ={ {(C_MANT_FP64-C_MANT_FP32){1'b0}},~Q_sqrt1[C_MANT_FP32+5:0] };
            Q_sqrt_com_2 ={ {(C_MANT_FP64-C_MANT_FP32){1'b0}},~Q_sqrt2[C_MANT_FP32+5:0] };
            Q_sqrt_com_3 ={ {(C_MANT_FP64-C_MANT_FP32){1'b0}},~Q_sqrt3[C_MANT_FP32+5:0] };
          end
        2'b01:
          begin
            Sqrt_quotinent_S = {Iteration_cell_carry_D[0],Iteration_cell_carry_D[1],Iteration_cell_carry_D[2],Iteration_cell_carry_D[3]};
            Q_sqrt_com_0=~Q_sqrt0;
            Q_sqrt_com_1=~Q_sqrt1;
            Q_sqrt_com_2=~Q_sqrt2;
            Q_sqrt_com_3=~Q_sqrt3;
          end
        2'b10:
          begin
            Sqrt_quotinent_S = {(~Iteration_cell_sum_AMASK_D[0][C_MANT_FP16+5]),(~Iteration_cell_sum_AMASK_D[1][C_MANT_FP16+5]),(~Iteration_cell_sum_AMASK_D[2][C_MANT_FP16+5]),(~Iteration_cell_sum_AMASK_D[3][C_MANT_FP16+5])};
            Q_sqrt_com_0 ={ {(C_MANT_FP64-C_MANT_FP16){1'b0}},~Q_sqrt0[C_MANT_FP16+5:0] };
            Q_sqrt_com_1 ={ {(C_MANT_FP64-C_MANT_FP16){1'b0}},~Q_sqrt1[C_MANT_FP16+5:0] };
            Q_sqrt_com_2 ={ {(C_MANT_FP64-C_MANT_FP16){1'b0}},~Q_sqrt2[C_MANT_FP16+5:0] };
            Q_sqrt_com_3 ={ {(C_MANT_FP64-C_MANT_FP16){1'b0}},~Q_sqrt3[C_MANT_FP16+5:0] };
          end
        2'b11:
          begin
            Sqrt_quotinent_S = {(~Iteration_cell_sum_AMASK_D[0][C_MANT_FP16ALT+5]),(~Iteration_cell_sum_AMASK_D[1][C_MANT_FP16ALT+5]),(~Iteration_cell_sum_AMASK_D[2][C_MANT_FP16ALT+5]),(~Iteration_cell_sum_AMASK_D[3][C_MANT_FP16ALT+5])};
            Q_sqrt_com_0 ={ {(C_MANT_FP64-C_MANT_FP16ALT){1'b0}},~Q_sqrt0[C_MANT_FP16ALT+5:0] };
            Q_sqrt_com_1 ={ {(C_MANT_FP64-C_MANT_FP16ALT){1'b0}},~Q_sqrt1[C_MANT_FP16ALT+5:0] };
            Q_sqrt_com_2 ={ {(C_MANT_FP64-C_MANT_FP16ALT){1'b0}},~Q_sqrt2[C_MANT_FP16ALT+5:0] };
            Q_sqrt_com_3 ={ {(C_MANT_FP64-C_MANT_FP16ALT){1'b0}},~Q_sqrt3[C_MANT_FP16ALT+5:0] };
          end
        endcase
    end



  assign  Qcnt_one_0=    {1'b0};  //qk for each feedback
  assign  Qcnt_one_1=    {Quotient_DP[0]};
  assign  Qcnt_one_2=    {Quotient_DP[1:0]};
  assign  Qcnt_one_3=    {Quotient_DP[2:0]};
  assign  Qcnt_one_4=    {Quotient_DP[3:0]};
  assign  Qcnt_one_5=    {Quotient_DP[4:0]};
  assign  Qcnt_one_6=    {Quotient_DP[5:0]};
  assign  Qcnt_one_7=    {Quotient_DP[6:0]};
  assign  Qcnt_one_8=    {Quotient_DP[7:0]};
  assign  Qcnt_one_9=    {Quotient_DP[8:0]};
  assign  Qcnt_one_10=    {Quotient_DP[9:0]};
  assign  Qcnt_one_11=    {Quotient_DP[10:0]};
  assign  Qcnt_one_12=    {Quotient_DP[11:0]};
  assign  Qcnt_one_13=    {Quotient_DP[12:0]};
  assign  Qcnt_one_14=    {Quotient_DP[13:0]};
  assign  Qcnt_one_15=    {Quotient_DP[14:0]};
  assign  Qcnt_one_16=    {Quotient_DP[15:0]};
  assign  Qcnt_one_17=    {Quotient_DP[16:0]};
  assign  Qcnt_one_18=    {Quotient_DP[17:0]};
  assign  Qcnt_one_19=    {Quotient_DP[18:0]};
  assign  Qcnt_one_20=    {Quotient_DP[19:0]};
  assign  Qcnt_one_21=    {Quotient_DP[20:0]};
  assign  Qcnt_one_22=    {Quotient_DP[21:0]};
  assign  Qcnt_one_23=    {Quotient_DP[22:0]};
  assign  Qcnt_one_24=    {Quotient_DP[23:0]};
  assign  Qcnt_one_25=    {Quotient_DP[24:0]};
  assign  Qcnt_one_26=    {Quotient_DP[25:0]};
  assign  Qcnt_one_27=    {Quotient_DP[26:0]};
  assign  Qcnt_one_28=    {Quotient_DP[27:0]};
  assign  Qcnt_one_29=    {Quotient_DP[28:0]};
  assign  Qcnt_one_30=    {Quotient_DP[29:0]};
  assign  Qcnt_one_31=    {Quotient_DP[30:0]};
  assign  Qcnt_one_32=    {Quotient_DP[31:0]};
  assign  Qcnt_one_33=    {Quotient_DP[32:0]};
  assign  Qcnt_one_34=    {Quotient_DP[33:0]};
  assign  Qcnt_one_35=    {Quotient_DP[34:0]};
  assign  Qcnt_one_36=    {Quotient_DP[35:0]};
  assign  Qcnt_one_37=    {Quotient_DP[36:0]};
  assign  Qcnt_one_38=    {Quotient_DP[37:0]};
  assign  Qcnt_one_39=    {Quotient_DP[38:0]};
  assign  Qcnt_one_40=    {Quotient_DP[39:0]};
  assign  Qcnt_one_41=    {Quotient_DP[40:0]};
  assign  Qcnt_one_42=    {Quotient_DP[41:0]};
  assign  Qcnt_one_43=    {Quotient_DP[42:0]};
  assign  Qcnt_one_44=    {Quotient_DP[43:0]};
  assign  Qcnt_one_45=    {Quotient_DP[44:0]};
  assign  Qcnt_one_46=    {Quotient_DP[45:0]};
  assign  Qcnt_one_47=    {Quotient_DP[46:0]};
  assign  Qcnt_one_48=    {Quotient_DP[47:0]};
  assign  Qcnt_one_49=    {Quotient_DP[48:0]};
  assign  Qcnt_one_50=    {Quotient_DP[49:0]};
  assign  Qcnt_one_51=    {Quotient_DP[50:0]};
  assign  Qcnt_one_52=    {Quotient_DP[51:0]};
  assign  Qcnt_one_53=    {Quotient_DP[52:0]};
  assign  Qcnt_one_54=    {Quotient_DP[53:0]};
  assign  Qcnt_one_55=    {Quotient_DP[54:0]};
  assign  Qcnt_one_56=    {Quotient_DP[55:0]};
  assign  Qcnt_one_57=    {Quotient_DP[56:0]};


  assign  Qcnt_two_0 =    {1'b0,            Sqrt_quotinent_S[3]};  //qk for each feedback
  assign  Qcnt_two_1 =    {Quotient_DP[1:0],Sqrt_quotinent_S[3]};
  assign  Qcnt_two_2 =    {Quotient_DP[3:0],Sqrt_quotinent_S[3]};
  assign  Qcnt_two_3 =    {Quotient_DP[5:0],Sqrt_quotinent_S[3]};
  assign  Qcnt_two_4 =    {Quotient_DP[7:0],Sqrt_quotinent_S[3]};
  assign  Qcnt_two_5 =    {Quotient_DP[9:0],Sqrt_quotinent_S[3]};
  assign  Qcnt_two_6 =    {Quotient_DP[11:0],Sqrt_quotinent_S[3]};
  assign  Qcnt_two_7 =    {Quotient_DP[13:0],Sqrt_quotinent_S[3]};
  assign  Qcnt_two_8 =    {Quotient_DP[15:0],Sqrt_quotinent_S[3]};
  assign  Qcnt_two_9 =    {Quotient_DP[17:0],Sqrt_quotinent_S[3]};
  assign  Qcnt_two_10 =    {Quotient_DP[19:0],Sqrt_quotinent_S[3]};
  assign  Qcnt_two_11 =    {Quotient_DP[21:0],Sqrt_quotinent_S[3]};
  assign  Qcnt_two_12 =    {Quotient_DP[23:0],Sqrt_quotinent_S[3]};
  assign  Qcnt_two_13 =    {Quotient_DP[25:0],Sqrt_quotinent_S[3]};
  assign  Qcnt_two_14 =    {Quotient_DP[27:0],Sqrt_quotinent_S[3]};
  assign  Qcnt_two_15 =    {Quotient_DP[29:0],Sqrt_quotinent_S[3]};
  assign  Qcnt_two_16 =    {Quotient_DP[31:0],Sqrt_quotinent_S[3]};
  assign  Qcnt_two_17 =    {Quotient_DP[33:0],Sqrt_quotinent_S[3]};
  assign  Qcnt_two_18 =    {Quotient_DP[35:0],Sqrt_quotinent_S[3]};
  assign  Qcnt_two_19 =    {Quotient_DP[37:0],Sqrt_quotinent_S[3]};
  assign  Qcnt_two_20 =    {Quotient_DP[39:0],Sqrt_quotinent_S[3]};
  assign  Qcnt_two_21 =    {Quotient_DP[41:0],Sqrt_quotinent_S[3]};
  assign  Qcnt_two_22 =    {Quotient_DP[43:0],Sqrt_quotinent_S[3]};
  assign  Qcnt_two_23 =    {Quotient_DP[45:0],Sqrt_quotinent_S[3]};
  assign  Qcnt_two_24 =    {Quotient_DP[47:0],Sqrt_quotinent_S[3]};
  assign  Qcnt_two_25 =    {Quotient_DP[49:0],Sqrt_quotinent_S[3]};
  assign  Qcnt_two_26 =    {Quotient_DP[51:0],Sqrt_quotinent_S[3]};
  assign  Qcnt_two_27 =    {Quotient_DP[53:0],Sqrt_quotinent_S[3]};
  assign  Qcnt_two_28 =    {Quotient_DP[55:0],Sqrt_quotinent_S[3]};


  assign  Qcnt_three_0 =    {1'b0,            Sqrt_quotinent_S[3],Sqrt_quotinent_S[2]};  //qk for each feedback
  assign  Qcnt_three_1 =    {Quotient_DP[2:0],Sqrt_quotinent_S[3],Sqrt_quotinent_S[2]};
  assign  Qcnt_three_2 =    {Quotient_DP[5:0],Sqrt_quotinent_S[3],Sqrt_quotinent_S[2]};
  assign  Qcnt_three_3 =    {Quotient_DP[8:0],Sqrt_quotinent_S[3],Sqrt_quotinent_S[2]};
  assign  Qcnt_three_4 =    {Quotient_DP[11:0],Sqrt_quotinent_S[3],Sqrt_quotinent_S[2]};
  assign  Qcnt_three_5 =    {Quotient_DP[14:0],Sqrt_quotinent_S[3],Sqrt_quotinent_S[2]};
  assign  Qcnt_three_6 =    {Quotient_DP[17:0],Sqrt_quotinent_S[3],Sqrt_quotinent_S[2]};
  assign  Qcnt_three_7 =    {Quotient_DP[20:0],Sqrt_quotinent_S[3],Sqrt_quotinent_S[2]};
  assign  Qcnt_three_8 =    {Quotient_DP[23:0],Sqrt_quotinent_S[3],Sqrt_quotinent_S[2]};
  assign  Qcnt_three_9 =    {Quotient_DP[26:0],Sqrt_quotinent_S[3],Sqrt_quotinent_S[2]};
  assign  Qcnt_three_10 =    {Quotient_DP[29:0],Sqrt_quotinent_S[3],Sqrt_quotinent_S[2]};
  assign  Qcnt_three_11 =    {Quotient_DP[32:0],Sqrt_quotinent_S[3],Sqrt_quotinent_S[2]};
  assign  Qcnt_three_12 =    {Quotient_DP[35:0],Sqrt_quotinent_S[3],Sqrt_quotinent_S[2]};
  assign  Qcnt_three_13 =    {Quotient_DP[38:0],Sqrt_quotinent_S[3],Sqrt_quotinent_S[2]};
  assign  Qcnt_three_14 =    {Quotient_DP[41:0],Sqrt_quotinent_S[3],Sqrt_quotinent_S[2]};
  assign  Qcnt_three_15 =    {Quotient_DP[44:0],Sqrt_quotinent_S[3],Sqrt_quotinent_S[2]};
  assign  Qcnt_three_16 =    {Quotient_DP[47:0],Sqrt_quotinent_S[3],Sqrt_quotinent_S[2]};
  assign  Qcnt_three_17 =    {Quotient_DP[50:0],Sqrt_quotinent_S[3],Sqrt_quotinent_S[2]};
  assign  Qcnt_three_18 =    {Quotient_DP[53:0],Sqrt_quotinent_S[3],Sqrt_quotinent_S[2]};
  assign  Qcnt_three_19 =    {Quotient_DP[56:0],Sqrt_quotinent_S[3],Sqrt_quotinent_S[2]};


  assign      Qcnt_four_0 =    {1'b0,            Sqrt_quotinent_S[3],Sqrt_quotinent_S[2],Sqrt_quotinent_S[1]};
  assign      Qcnt_four_1 =    {Quotient_DP[3:0],Sqrt_quotinent_S[3],Sqrt_quotinent_S[2],Sqrt_quotinent_S[1]};
  assign      Qcnt_four_2 =    {Quotient_DP[7:0],Sqrt_quotinent_S[3],Sqrt_quotinent_S[2],Sqrt_quotinent_S[1]};
  assign      Qcnt_four_3 =    {Quotient_DP[11:0],Sqrt_quotinent_S[3],Sqrt_quotinent_S[2],Sqrt_quotinent_S[1]};
  assign      Qcnt_four_4 =    {Quotient_DP[15:0],Sqrt_quotinent_S[3],Sqrt_quotinent_S[2],Sqrt_quotinent_S[1]};
  assign      Qcnt_four_5 =    {Quotient_DP[19:0],Sqrt_quotinent_S[3],Sqrt_quotinent_S[2],Sqrt_quotinent_S[1]};
  assign      Qcnt_four_6 =    {Quotient_DP[23:0],Sqrt_quotinent_S[3],Sqrt_quotinent_S[2],Sqrt_quotinent_S[1]};
  assign      Qcnt_four_7 =    {Quotient_DP[27:0],Sqrt_quotinent_S[3],Sqrt_quotinent_S[2],Sqrt_quotinent_S[1]};
  assign      Qcnt_four_8 =    {Quotient_DP[31:0],Sqrt_quotinent_S[3],Sqrt_quotinent_S[2],Sqrt_quotinent_S[1]};
  assign      Qcnt_four_9 =    {Quotient_DP[35:0],Sqrt_quotinent_S[3],Sqrt_quotinent_S[2],Sqrt_quotinent_S[1]};
  assign      Qcnt_four_10 =    {Quotient_DP[39:0],Sqrt_quotinent_S[3],Sqrt_quotinent_S[2],Sqrt_quotinent_S[1]};
  assign      Qcnt_four_11 =    {Quotient_DP[43:0],Sqrt_quotinent_S[3],Sqrt_quotinent_S[2],Sqrt_quotinent_S[1]};
  assign      Qcnt_four_12 =    {Quotient_DP[47:0],Sqrt_quotinent_S[3],Sqrt_quotinent_S[2],Sqrt_quotinent_S[1]};
  assign      Qcnt_four_13 =    {Quotient_DP[51:0],Sqrt_quotinent_S[3],Sqrt_quotinent_S[2],Sqrt_quotinent_S[1]};
  assign      Qcnt_four_14 =    {Quotient_DP[55:0],Sqrt_quotinent_S[3],Sqrt_quotinent_S[2],Sqrt_quotinent_S[1]};




  always_comb begin  // the intermediate operands for sqrt

  case(Iteration_unit_num_S)
    2'b00:
      begin

  /////////////////////////////////////////////////////////////////////////////
   // Operands for square root when Iteration_unit_num_S = 2'b00, start       //
   /////////////////////////////////////////////////////////////////////////////




        case(Crtl_cnt_S)

          6'b000000:
            begin
              Sqrt_DI[0]=Mant_D_sqrt_Norm[C_MANT_FP64+1:C_MANT_FP64];
              Q_sqrt0={{(C_MANT_FP64+5){1'b0}},Qcnt_one_0};
              Sqrt_Q0=Q_sqrt_com_0;
            end
          6'b000001:
            begin
              Sqrt_DI[0]=Mant_D_sqrt_Norm[C_MANT_FP64-1:C_MANT_FP64-2];
              Q_sqrt0={{(C_MANT_FP64+5){1'b0}},Qcnt_one_1};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
            end
          6'b000010:
            begin
              Sqrt_DI[0]=Mant_D_sqrt_Norm[C_MANT_FP64-3:C_MANT_FP64-4];
              Q_sqrt0={{(C_MANT_FP64+4){1'b0}},Qcnt_one_2};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
            end
          6'b000011:
            begin
              Sqrt_DI[0]=Mant_D_sqrt_Norm[C_MANT_FP64-5:C_MANT_FP64-6];
              Q_sqrt0={{(C_MANT_FP64+3){1'b0}},Qcnt_one_3};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
            end
          6'b000100:
            begin
              Sqrt_DI[0]=Mant_D_sqrt_Norm[C_MANT_FP64-7:C_MANT_FP64-8];
              Q_sqrt0={{(C_MANT_FP64+2){1'b0}},Qcnt_one_4};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
            end
          6'b000101:
            begin
              Sqrt_DI[0]=Mant_D_sqrt_Norm[C_MANT_FP64-9:C_MANT_FP64-10];
              Q_sqrt0={{(C_MANT_FP64+1){1'b0}},Qcnt_one_5};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
            end
          6'b000110:
            begin
              Sqrt_DI[0]=Mant_D_sqrt_Norm[C_MANT_FP64-11:C_MANT_FP64-12];
              Q_sqrt0={{(C_MANT_FP64){1'b0}},Qcnt_one_6};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
            end
          6'b000111:
            begin
              Sqrt_DI[0]=Mant_D_sqrt_Norm[C_MANT_FP64-13:C_MANT_FP64-14];
              Q_sqrt0={{(C_MANT_FP64-1){1'b0}},Qcnt_one_7};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
            end
          6'b001000:
            begin
              Sqrt_DI[0]=Mant_D_sqrt_Norm[C_MANT_FP64-15:C_MANT_FP64-16];
              Q_sqrt0={{(C_MANT_FP64-2){1'b0}},Qcnt_one_8};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
            end
          6'b001001:
            begin
              Sqrt_DI[0]=Mant_D_sqrt_Norm[C_MANT_FP64-17:C_MANT_FP64-18];
              Q_sqrt0={{(C_MANT_FP64-3){1'b0}},Qcnt_one_9};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
            end
          6'b001010:
            begin
              Sqrt_DI[0]=Mant_D_sqrt_Norm[C_MANT_FP64-19:C_MANT_FP64-20];
              Q_sqrt0={{(C_MANT_FP64-4){1'b0}},Qcnt_one_10};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
            end
          6'b001011:
            begin
              Sqrt_DI[0]=Mant_D_sqrt_Norm[C_MANT_FP64-21:C_MANT_FP64-22];
              Q_sqrt0={{(C_MANT_FP64-5){1'b0}},Qcnt_one_11};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
            end
          6'b001100:
            begin
              Sqrt_DI[0]=Mant_D_sqrt_Norm[C_MANT_FP64-23:C_MANT_FP64-24];
              Q_sqrt0={{(C_MANT_FP64-6){1'b0}},Qcnt_one_12};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
            end
          6'b001101:
            begin
              Sqrt_DI[0]=Mant_D_sqrt_Norm[C_MANT_FP64-25:C_MANT_FP64-26];
              Q_sqrt0={{(C_MANT_FP64-7){1'b0}},Qcnt_one_13};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
            end
          6'b001110:
            begin
              Sqrt_DI[0]=Mant_D_sqrt_Norm[C_MANT_FP64-27:C_MANT_FP64-28];
              Q_sqrt0={{(C_MANT_FP64-8){1'b0}},Qcnt_one_14};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
            end
          6'b001111:
            begin
              Sqrt_DI[0]=Mant_D_sqrt_Norm[C_MANT_FP64-29:C_MANT_FP64-30];
              Q_sqrt0={{(C_MANT_FP64-9){1'b0}},Qcnt_one_15};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
            end
          6'b010000:
            begin
              Sqrt_DI[0]=Mant_D_sqrt_Norm[C_MANT_FP64-31:C_MANT_FP64-32];
              Q_sqrt0={{(C_MANT_FP64-10){1'b0}},Qcnt_one_16};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
            end
          6'b010001:
            begin
              Sqrt_DI[0]=Mant_D_sqrt_Norm[C_MANT_FP64-33:C_MANT_FP64-34];
              Q_sqrt0={{(C_MANT_FP64-11){1'b0}},Qcnt_one_17};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
            end
          6'b010010:
            begin
              Sqrt_DI[0]=Mant_D_sqrt_Norm[C_MANT_FP64-35:C_MANT_FP64-36];
              Q_sqrt0={{(C_MANT_FP64-12){1'b0}},Qcnt_one_18};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
            end
          6'b010011:
            begin
              Sqrt_DI[0]=Mant_D_sqrt_Norm[C_MANT_FP64-37:C_MANT_FP64-38];
              Q_sqrt0={{(C_MANT_FP64-13){1'b0}},Qcnt_one_19};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
            end
          6'b010100:
            begin
              Sqrt_DI[0]=Mant_D_sqrt_Norm[C_MANT_FP64-39:C_MANT_FP64-40];
              Q_sqrt0={{(C_MANT_FP64-14){1'b0}},Qcnt_one_20};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
            end
          6'b010101:
            begin
              Sqrt_DI[0]=Mant_D_sqrt_Norm[C_MANT_FP64-41:C_MANT_FP64-42];
              Q_sqrt0={{(C_MANT_FP64-15){1'b0}},Qcnt_one_21};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
            end
          6'b010110:
            begin
              Sqrt_DI[0]=Mant_D_sqrt_Norm[C_MANT_FP64-43:C_MANT_FP64-44];
              Q_sqrt0={{(C_MANT_FP64-16){1'b0}},Qcnt_one_22};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
            end
          6'b010111:
            begin
              Sqrt_DI[0]=Mant_D_sqrt_Norm[C_MANT_FP64-45:C_MANT_FP64-46];
              Q_sqrt0={{(C_MANT_FP64-17){1'b0}},Qcnt_one_23};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
            end
          6'b011000:
            begin
              Sqrt_DI[0]=Mant_D_sqrt_Norm[C_MANT_FP64-47:C_MANT_FP64-48];
              Q_sqrt0={{(C_MANT_FP64-18){1'b0}},Qcnt_one_24};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
            end
          6'b011001:
            begin
              Sqrt_DI[0]=Mant_D_sqrt_Norm[C_MANT_FP64-49:C_MANT_FP64-50];
              Q_sqrt0={{(C_MANT_FP64-19){1'b0}},Qcnt_one_25};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
            end
          6'b011010:
            begin
              Sqrt_DI[0]=Mant_D_sqrt_Norm[C_MANT_FP64-51:C_MANT_FP64-52];
              Q_sqrt0={{(C_MANT_FP64-20){1'b0}},Qcnt_one_26};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
            end
          6'b011011:
            begin
              Sqrt_DI[0]=2'b00;
              Q_sqrt0={{(C_MANT_FP64-21){1'b0}},Qcnt_one_27};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
            end
          6'b011100:
            begin
              Sqrt_DI[0]=2'b00;
              Q_sqrt0={{(C_MANT_FP64-22){1'b0}},Qcnt_one_28};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
            end
          6'b011101:
            begin
              Sqrt_DI[0]=2'b00;
              Q_sqrt0={{(C_MANT_FP64-23){1'b0}},Qcnt_one_29};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
            end
          6'b011110:
            begin
              Sqrt_DI[0]=2'b00;
              Q_sqrt0={{(C_MANT_FP64-24){1'b0}},Qcnt_one_30};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
            end
          6'b011111:
            begin
              Sqrt_DI[0]=2'b00;
              Q_sqrt0={{(C_MANT_FP64-25){1'b0}},Qcnt_one_31};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
            end
          6'b100000:
            begin
              Sqrt_DI[0]=2'b00;
              Q_sqrt0={{(C_MANT_FP64-26){1'b0}},Qcnt_one_32};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
            end
          6'b100001:
            begin
              Sqrt_DI[0]=2'b00;
              Q_sqrt0={{(C_MANT_FP64-27){1'b0}},Qcnt_one_33};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
            end
          6'b100010:
            begin
              Sqrt_DI[0]=2'b00;
              Q_sqrt0={{(C_MANT_FP64-28){1'b0}},Qcnt_one_34};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
            end
          6'b100011:
            begin
              Sqrt_DI[0]=2'b00;
              Q_sqrt0={{(C_MANT_FP64-29){1'b0}},Qcnt_one_35};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
            end
          6'b100100:
            begin
              Sqrt_DI[0]=2'b00;
              Q_sqrt0={{(C_MANT_FP64-30){1'b0}},Qcnt_one_36};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
            end
          6'b100101:
            begin
              Sqrt_DI[0]=2'b00;
              Q_sqrt0={{(C_MANT_FP64-31){1'b0}},Qcnt_one_37};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
            end
          6'b100110:
            begin
              Sqrt_DI[0]=2'b00;
              Q_sqrt0={{(C_MANT_FP64-32){1'b0}},Qcnt_one_38};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
            end
          6'b100111:
            begin
              Sqrt_DI[0]=2'b00;
              Q_sqrt0={{(C_MANT_FP64-33){1'b0}},Qcnt_one_39};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
            end
          6'b101000:
            begin
              Sqrt_DI[0]=2'b00;
              Q_sqrt0={{(C_MANT_FP64-34){1'b0}},Qcnt_one_40};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
            end
          6'b101001:
            begin
              Sqrt_DI[0]=2'b00;
              Q_sqrt0={{(C_MANT_FP64-35){1'b0}},Qcnt_one_41};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
            end
          6'b101010:
            begin
              Sqrt_DI[0]=2'b00;
              Q_sqrt0={{(C_MANT_FP64-36){1'b0}},Qcnt_one_42};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
            end
          6'b101011:
            begin
              Sqrt_DI[0]=2'b00;
              Q_sqrt0={{(C_MANT_FP64-37){1'b0}},Qcnt_one_43};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
            end
          6'b101100:
            begin
              Sqrt_DI[0]=2'b00;
              Q_sqrt0={{(C_MANT_FP64-38){1'b0}},Qcnt_one_44};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
            end
          6'b101101:
            begin
              Sqrt_DI[0]=2'b00;
              Q_sqrt0={{(C_MANT_FP64-39){1'b0}},Qcnt_one_45};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
            end
          6'b101110:
            begin
              Sqrt_DI[0]=2'b00;
              Q_sqrt0={{(C_MANT_FP64-40){1'b0}},Qcnt_one_46};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
            end
          6'b101111:
            begin
              Sqrt_DI[0]=2'b00;
              Q_sqrt0={{(C_MANT_FP64-41){1'b0}},Qcnt_one_47};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
            end
          6'b110000:
            begin
              Sqrt_DI[0]=2'b00;
              Q_sqrt0={{(C_MANT_FP64-42){1'b0}},Qcnt_one_48};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
            end
          6'b110001:
            begin
              Sqrt_DI[0]=2'b00;
              Q_sqrt0={{(C_MANT_FP64-43){1'b0}},Qcnt_one_49};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
            end
          6'b110010:
            begin
              Sqrt_DI[0]=2'b00;
              Q_sqrt0={{(C_MANT_FP64-44){1'b0}},Qcnt_one_50};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
            end
          6'b110011:
            begin
              Sqrt_DI[0]=2'b00;
              Q_sqrt0={{(C_MANT_FP64-45){1'b0}},Qcnt_one_51};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
            end
          6'b110100:
            begin
              Sqrt_DI[0]=2'b00;
              Q_sqrt0={{(C_MANT_FP64-46){1'b0}},Qcnt_one_52};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
            end
          6'b110101:
            begin
              Sqrt_DI[0]=2'b00;
              Q_sqrt0={{(C_MANT_FP64-47){1'b0}},Qcnt_one_53};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
            end
          6'b110110:
            begin
              Sqrt_DI[0]=2'b00;
              Q_sqrt0={{(C_MANT_FP64-48){1'b0}},Qcnt_one_54};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
            end
          6'b110111:
            begin
              Sqrt_DI[0]=2'b00;
              Q_sqrt0={{(C_MANT_FP64-49){1'b0}},Qcnt_one_55};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
            end
          6'b111000:
            begin
              Sqrt_DI[0]=2'b00;
              Q_sqrt0={{(C_MANT_FP64-50){1'b0}},Qcnt_one_56};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
            end

          default:
            begin
              Sqrt_DI[0]=2'b00;
              Q_sqrt0='0;
              Sqrt_Q0='0;
            end
        endcase
      end


   /////////////////////////////////////////////////////////////////////////////
   // Operands for square root when Iteration_unit_num_S = 2'b00, end         //
   /////////////////////////////////////////////////////////////////////////////


    2'b01:
      begin
   /////////////////////////////////////////////////////////////////////////////
   // Operands for square root when Iteration_unit_num_S = 2'b01, start       //
   /////////////////////////////////////////////////////////////////////////////
        case(Crtl_cnt_S)

          6'b000000:
            begin
              Sqrt_DI[0]=Mant_D_sqrt_Norm[C_MANT_FP64+1:C_MANT_FP64];
              Q_sqrt0={{(C_MANT_FP64+5){1'b0}},Qcnt_two_0[1]};
              Sqrt_Q0=Q_sqrt_com_0;
              Sqrt_DI[1]=Mant_D_sqrt_Norm[C_MANT_FP64-1:C_MANT_FP64-2];
              Q_sqrt1={{(C_MANT_FP64+4){1'b0}},Qcnt_two_0[1:0]};
              Sqrt_Q1=Sqrt_quotinent_S[3]?Q_sqrt_com_1:Q_sqrt1;
            end

          6'b000001:
            begin
              Sqrt_DI[0]=Mant_D_sqrt_Norm[C_MANT_FP64-3:C_MANT_FP64-4];
              Q_sqrt0={{(C_MANT_FP64+4){1'b0}},Qcnt_two_1[2:1]};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
              Sqrt_DI[1]=Mant_D_sqrt_Norm[C_MANT_FP64-5:C_MANT_FP64-6];
              Q_sqrt1={{(C_MANT_FP64+3){1'b0}},Qcnt_two_1[2:0]};
              Sqrt_Q1=Sqrt_quotinent_S[3]?Q_sqrt_com_1:Q_sqrt1;
            end

          6'b000010:
            begin
              Sqrt_DI[0]=Mant_D_sqrt_Norm[C_MANT_FP64-7:C_MANT_FP64-8];
              Q_sqrt0={{(C_MANT_FP64+2){1'b0}},Qcnt_two_2[4:1]};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
              Sqrt_DI[1]=Mant_D_sqrt_Norm[C_MANT_FP64-9:C_MANT_FP64-10];
              Q_sqrt1={{(C_MANT_FP64+1){1'b0}},Qcnt_two_2[4:0]};
              Sqrt_Q1=Sqrt_quotinent_S[3]?Q_sqrt_com_1:Q_sqrt1;
            end

          6'b000011:
            begin
              Sqrt_DI[0]=Mant_D_sqrt_Norm[C_MANT_FP64-11:C_MANT_FP64-12];
              Q_sqrt0={{(C_MANT_FP64){1'b0}},Qcnt_two_3[6:1]};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
              Sqrt_DI[1]=Mant_D_sqrt_Norm[C_MANT_FP64-13:C_MANT_FP64-14];
              Q_sqrt1={{(C_MANT_FP64-1){1'b0}},Qcnt_two_3[6:0]};
              Sqrt_Q1=Sqrt_quotinent_S[3]?Q_sqrt_com_1:Q_sqrt1;
            end

          6'b000100:
            begin
              Sqrt_DI[0]=Mant_D_sqrt_Norm[C_MANT_FP64-15:C_MANT_FP64-16];
              Q_sqrt0={{(C_MANT_FP64-2){1'b0}},Qcnt_two_4[8:1]};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
              Sqrt_DI[1]=Mant_D_sqrt_Norm[C_MANT_FP64-17:C_MANT_FP64-18];
              Q_sqrt1={{(C_MANT_FP64-3){1'b0}},Qcnt_two_4[8:0]};
              Sqrt_Q1=Sqrt_quotinent_S[3]?Q_sqrt_com_1:Q_sqrt1;
            end

            6'b000101:
            begin
              Sqrt_DI[0]=Mant_D_sqrt_Norm[C_MANT_FP64-19:C_MANT_FP64-20];
              Q_sqrt0={{(C_MANT_FP64-4){1'b0}},Qcnt_two_5[10:1]};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
              Sqrt_DI[1]=Mant_D_sqrt_Norm[C_MANT_FP64-21:C_MANT_FP64-22];
              Q_sqrt1={{(C_MANT_FP64-5){1'b0}},Qcnt_two_5[10:0]};
              Sqrt_Q1=Sqrt_quotinent_S[3]?Q_sqrt_com_1:Q_sqrt1;
            end

          6'b000110:
            begin
              Sqrt_DI[0]=Mant_D_sqrt_Norm[C_MANT_FP64-23:C_MANT_FP64-24];
              Q_sqrt0={{(C_MANT_FP64-6){1'b0}},Qcnt_two_6[12:1]};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
              Sqrt_DI[1]=Mant_D_sqrt_Norm[C_MANT_FP64-25:C_MANT_FP64-26];
              Q_sqrt1={{(C_MANT_FP64-7){1'b0}},Qcnt_two_6[12:0]};
              Sqrt_Q1=Sqrt_quotinent_S[3]?Q_sqrt_com_1:Q_sqrt1;
            end

          6'b000111:
            begin
              Sqrt_DI[0]=Mant_D_sqrt_Norm[C_MANT_FP64-27:C_MANT_FP64-28];
              Q_sqrt0={{(C_MANT_FP64-8){1'b0}},Qcnt_two_7[14:1]};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
              Sqrt_DI[1]=Mant_D_sqrt_Norm[C_MANT_FP64-29:C_MANT_FP64-30];
              Q_sqrt1={{(C_MANT_FP64-9){1'b0}},Qcnt_two_7[14:0]};
              Sqrt_Q1=Sqrt_quotinent_S[3]?Q_sqrt_com_1:Q_sqrt1;
            end

          6'b001000:
            begin
              Sqrt_DI[0]=Mant_D_sqrt_Norm[C_MANT_FP64-31:C_MANT_FP64-32];
              Q_sqrt0={{(C_MANT_FP64-10){1'b0}},Qcnt_two_8[16:1]};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
              Sqrt_DI[1]=Mant_D_sqrt_Norm[C_MANT_FP64-33:C_MANT_FP64-34];
              Q_sqrt1={{(C_MANT_FP64-11){1'b0}},Qcnt_two_8[16:0]};
              Sqrt_Q1=Sqrt_quotinent_S[3]?Q_sqrt_com_1:Q_sqrt1;
            end

          6'b001001:
            begin
              Sqrt_DI[0]=Mant_D_sqrt_Norm[C_MANT_FP64-35:C_MANT_FP64-36];
              Q_sqrt0={{(C_MANT_FP64-12){1'b0}},Qcnt_two_9[18:1]};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
              Sqrt_DI[1]=Mant_D_sqrt_Norm[C_MANT_FP64-37:C_MANT_FP64-38];
              Q_sqrt1={{(C_MANT_FP64-13){1'b0}},Qcnt_two_9[18:0]};
              Sqrt_Q1=Sqrt_quotinent_S[3]?Q_sqrt_com_1:Q_sqrt1;
            end

          6'b001010:
            begin
              Sqrt_DI[0]=Mant_D_sqrt_Norm[C_MANT_FP64-39:C_MANT_FP64-40];
              Q_sqrt0={{(C_MANT_FP64-14){1'b0}},Qcnt_two_10[20:1]};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
              Sqrt_DI[1]=Mant_D_sqrt_Norm[C_MANT_FP64-41:C_MANT_FP64-42];
              Q_sqrt1={{(C_MANT_FP64-15){1'b0}},Qcnt_two_10[20:0]};
              Sqrt_Q1=Sqrt_quotinent_S[3]?Q_sqrt_com_1:Q_sqrt1;
            end

          6'b001011:
            begin
              Sqrt_DI[0]=Mant_D_sqrt_Norm[C_MANT_FP64-43:C_MANT_FP64-44];
              Q_sqrt0={{(C_MANT_FP64-16){1'b0}},Qcnt_two_11[22:1]};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
              Sqrt_DI[1]=Mant_D_sqrt_Norm[C_MANT_FP64-45:C_MANT_FP64-46];
              Q_sqrt1={{(C_MANT_FP64-17){1'b0}},Qcnt_two_11[22:0]};
              Sqrt_Q1=Sqrt_quotinent_S[3]?Q_sqrt_com_1:Q_sqrt1;
            end

          6'b001100:
            begin
              Sqrt_DI[0]=Mant_D_sqrt_Norm[C_MANT_FP64-47:C_MANT_FP64-48];
              Q_sqrt0={{(C_MANT_FP64-18){1'b0}},Qcnt_two_12[24:1]};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
              Sqrt_DI[1]=Mant_D_sqrt_Norm[C_MANT_FP64-49:C_MANT_FP64-50];
              Q_sqrt1={{(C_MANT_FP64-19){1'b0}},Qcnt_two_12[24:0]};
              Sqrt_Q1=Sqrt_quotinent_S[3]?Q_sqrt_com_1:Q_sqrt1;
            end

          6'b001101:
            begin
              Sqrt_DI[0]=Mant_D_sqrt_Norm[C_MANT_FP64-51:C_MANT_FP64-52];
              Q_sqrt0={{(C_MANT_FP64-20){1'b0}},Qcnt_two_13[26:1]};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
              Sqrt_DI[1]=2'b00;
              Q_sqrt1={{(C_MANT_FP64-21){1'b0}},Qcnt_two_13[26:0]};
              Sqrt_Q1=Sqrt_quotinent_S[3]?Q_sqrt_com_1:Q_sqrt1;
            end

          6'b001110:
            begin
              Sqrt_DI[0]=2'b00;
              Q_sqrt0={{(C_MANT_FP64-22){1'b0}},Qcnt_two_14[28:1]};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
              Sqrt_DI[1]=2'b00;
              Q_sqrt1={{(C_MANT_FP64-23){1'b0}},Qcnt_two_14[28:0]};
              Sqrt_Q1=Sqrt_quotinent_S[3]?Q_sqrt_com_1:Q_sqrt1;
            end

          6'b001111:
            begin
              Sqrt_DI[0]=2'b00;
              Q_sqrt0={{(C_MANT_FP64-24){1'b0}},Qcnt_two_15[30:1]};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
              Sqrt_DI[1]=2'b00;
              Q_sqrt1={{(C_MANT_FP64-25){1'b0}},Qcnt_two_15[30:0]};
              Sqrt_Q1=Sqrt_quotinent_S[3]?Q_sqrt_com_1:Q_sqrt1;
            end

          6'b010000:
            begin
              Sqrt_DI[0]=2'b00;
              Q_sqrt0={{(C_MANT_FP64-26){1'b0}},Qcnt_two_16[32:1]};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
              Sqrt_DI[1]=2'b00;
              Q_sqrt1={{(C_MANT_FP64-27){1'b0}},Qcnt_two_16[32:0]};
              Sqrt_Q1=Sqrt_quotinent_S[3]?Q_sqrt_com_1:Q_sqrt1;
            end

          6'b010001:
            begin
              Sqrt_DI[0]=2'b00;
              Q_sqrt0={{(C_MANT_FP64-28){1'b0}},Qcnt_two_17[34:1]};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
              Sqrt_DI[1]=2'b00;
              Q_sqrt1={{(C_MANT_FP64-29){1'b0}},Qcnt_two_17[34:0]};
              Sqrt_Q1=Sqrt_quotinent_S[3]?Q_sqrt_com_1:Q_sqrt1;
            end

          6'b010010:
            begin
              Sqrt_DI[0]=2'b00;
              Q_sqrt0={{(C_MANT_FP64-30){1'b0}},Qcnt_two_18[36:1]};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
              Sqrt_DI[1]=2'b00;
              Q_sqrt1={{(C_MANT_FP64-31){1'b0}},Qcnt_two_18[36:0]};
              Sqrt_Q1=Sqrt_quotinent_S[3]?Q_sqrt_com_1:Q_sqrt1;
            end

          6'b010011:
            begin
              Sqrt_DI[0]=2'b00;
              Q_sqrt0={{(C_MANT_FP64-32){1'b0}},Qcnt_two_19[38:1]};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
              Sqrt_DI[1]=2'b00;
              Q_sqrt1={{(C_MANT_FP64-33){1'b0}},Qcnt_two_19[38:0]};
              Sqrt_Q1=Sqrt_quotinent_S[3]?Q_sqrt_com_1:Q_sqrt1;
            end

          6'b010100:
            begin
              Sqrt_DI[0]=2'b00;
              Q_sqrt0={{(C_MANT_FP64-34){1'b0}},Qcnt_two_20[40:1]};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
              Sqrt_DI[1]=2'b00;
              Q_sqrt1={{(C_MANT_FP64-35){1'b0}},Qcnt_two_20[40:0]};
              Sqrt_Q1=Sqrt_quotinent_S[3]?Q_sqrt_com_1:Q_sqrt1;
            end

          6'b010101:
            begin
              Sqrt_DI[0]=2'b00;
              Q_sqrt0={{(C_MANT_FP64-36){1'b0}},Qcnt_two_21[42:1]};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
              Sqrt_DI[1]=2'b00;
              Q_sqrt1={{(C_MANT_FP64-37){1'b0}},Qcnt_two_21[42:0]};
              Sqrt_Q1=Sqrt_quotinent_S[3]?Q_sqrt_com_1:Q_sqrt1;
            end

          6'b010110:
            begin
              Sqrt_DI[0]=2'b00;
              Q_sqrt0={{(C_MANT_FP64-38){1'b0}},Qcnt_two_22[44:1]};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
              Sqrt_DI[1]=2'b00;
              Q_sqrt1={{(C_MANT_FP64-39){1'b0}},Qcnt_two_22[44:0]};
              Sqrt_Q1=Sqrt_quotinent_S[3]?Q_sqrt_com_1:Q_sqrt1;
            end

          6'b010111:
            begin
              Sqrt_DI[0]=2'b00;
              Q_sqrt0={{(C_MANT_FP64-40){1'b0}},Qcnt_two_23[46:1]};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
              Sqrt_DI[1]=2'b00;
              Q_sqrt1={{(C_MANT_FP64-41){1'b0}},Qcnt_two_23[46:0]};
              Sqrt_Q1=Sqrt_quotinent_S[3]?Q_sqrt_com_1:Q_sqrt1;
            end

          6'b011000:
            begin
              Sqrt_DI[0]=2'b00;
              Q_sqrt0={{(C_MANT_FP64-42){1'b0}},Qcnt_two_24[48:1]};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
              Sqrt_DI[1]=2'b00;
              Q_sqrt1={{(C_MANT_FP64-43){1'b0}},Qcnt_two_24[48:0]};
              Sqrt_Q1=Sqrt_quotinent_S[3]?Q_sqrt_com_1:Q_sqrt1;
            end

          6'b011001:
            begin
              Sqrt_DI[0]=2'b00;
              Q_sqrt0={{(C_MANT_FP64-44){1'b0}},Qcnt_two_25[50:1]};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
              Sqrt_DI[1]=2'b00;
              Q_sqrt1={{(C_MANT_FP64-45){1'b0}},Qcnt_two_25[50:0]};
              Sqrt_Q1=Sqrt_quotinent_S[3]?Q_sqrt_com_1:Q_sqrt1;
            end

          6'b011010:
            begin
              Sqrt_DI[0]=2'b00;
              Q_sqrt0={{(C_MANT_FP64-46){1'b0}},Qcnt_two_26[52:1]};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
              Sqrt_DI[1]=2'b00;
              Q_sqrt1={{(C_MANT_FP64-47){1'b0}},Qcnt_two_26[52:0]};
              Sqrt_Q1=Sqrt_quotinent_S[3]?Q_sqrt_com_1:Q_sqrt1;
            end

          6'b011011:
            begin
              Sqrt_DI[0]=2'b00;
              Q_sqrt0={{(C_MANT_FP64-48){1'b0}},Qcnt_two_27[54:1]};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
              Sqrt_DI[1]=2'b00;
              Q_sqrt1={{(C_MANT_FP64-49){1'b0}},Qcnt_two_27[54:0]};
              Sqrt_Q1=Sqrt_quotinent_S[3]?Q_sqrt_com_1:Q_sqrt1;
            end

          6'b011100:
            begin
              Sqrt_DI[0]=2'b00;
              Q_sqrt0={{(C_MANT_FP64-50){1'b0}},Qcnt_two_28[56:1]};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
              Sqrt_DI[1]=2'b00;
              Q_sqrt1={{(C_MANT_FP64-51){1'b0}},Qcnt_two_28[56:0]};
              Sqrt_Q1=Sqrt_quotinent_S[3]?Q_sqrt_com_1:Q_sqrt1;
            end

          default:
            begin
              Sqrt_DI[0]=Mant_D_sqrt_Norm[C_MANT_FP64+1:C_MANT_FP64];
              Q_sqrt0={{(C_MANT_FP64+5){1'b0}},Qcnt_two_0[1]};
              Sqrt_Q0=Q_sqrt_com_0;
              Sqrt_DI[1]=Mant_D_sqrt_Norm[C_MANT_FP64-1:C_MANT_FP64-2];
              Q_sqrt1={{(C_MANT_FP64+4){1'b0}},Qcnt_two_0[1:0]};
              Sqrt_Q1=Sqrt_quotinent_S[3]?Q_sqrt_com_1:Q_sqrt1;
            end

        endcase
      end

   /////////////////////////////////////////////////////////////////////////////
   // Operands for square root when Iteration_unit_num_S = 2'b01, end       //
   /////////////////////////////////////////////////////////////////////////////


    2'b10:
      begin
   /////////////////////////////////////////////////////////////////////////////
   // Operands for square root when Iteration_unit_num_S = 2'b10, start       //
   /////////////////////////////////////////////////////////////////////////////

        case(Crtl_cnt_S)
          6'b000000:
            begin
              Sqrt_DI[0]=Mant_D_sqrt_Norm[C_MANT_FP64+1:C_MANT_FP64];
              Q_sqrt0={{(C_MANT_FP64+5){1'b0}},Qcnt_three_0[2]};
              Sqrt_Q0=Q_sqrt_com_0;
              Sqrt_DI[1]=Mant_D_sqrt_Norm[C_MANT_FP64-1:C_MANT_FP64-2];
              Q_sqrt1={{(C_MANT_FP64+4){1'b0}},Qcnt_three_0[2:1]};
              Sqrt_Q1=Sqrt_quotinent_S[3]?Q_sqrt_com_1:Q_sqrt1;
              Sqrt_DI[2]=Mant_D_sqrt_Norm[C_MANT_FP64-3:C_MANT_FP64-4];
              Q_sqrt2={{(C_MANT_FP64+3){1'b0}},Qcnt_three_0[2:0]};
              Sqrt_Q2=Sqrt_quotinent_S[2]?Q_sqrt_com_2:Q_sqrt2;
            end

          6'b000001:
            begin
              Sqrt_DI[0]=Mant_D_sqrt_Norm[C_MANT_FP64-5:C_MANT_FP64-6];
              Q_sqrt0={{(C_MANT_FP64+2){1'b0}},Qcnt_three_1[4:2]};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
              Sqrt_DI[1]=Mant_D_sqrt_Norm[C_MANT_FP64-7:C_MANT_FP64-8];
              Q_sqrt1={{(C_MANT_FP64+1){1'b0}},Qcnt_three_1[4:1]};
              Sqrt_Q1=Sqrt_quotinent_S[3]?Q_sqrt_com_1:Q_sqrt1;
              Sqrt_DI[2]=Mant_D_sqrt_Norm[C_MANT_FP64-9:C_MANT_FP64-10];
              Q_sqrt2={{(C_MANT_FP64){1'b0}},Qcnt_three_1[4:0]};
              Sqrt_Q2=Sqrt_quotinent_S[2]?Q_sqrt_com_2:Q_sqrt2;
            end

          6'b000010:
            begin
              Sqrt_DI[0]=Mant_D_sqrt_Norm[C_MANT_FP64-11:C_MANT_FP64-12];
              Q_sqrt0={{(C_MANT_FP64-1){1'b0}},Qcnt_three_2[7:2]};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
              Sqrt_DI[1]=Mant_D_sqrt_Norm[C_MANT_FP64-13:C_MANT_FP64-14];
              Q_sqrt1={{(C_MANT_FP64-2){1'b0}},Qcnt_three_2[7:1]};
              Sqrt_Q1=Sqrt_quotinent_S[3]?Q_sqrt_com_1:Q_sqrt1;
              Sqrt_DI[2]=Mant_D_sqrt_Norm[C_MANT_FP64-15:C_MANT_FP64-16];
              Q_sqrt2={{(C_MANT_FP64-3){1'b0}},Qcnt_three_2[7:0]};
              Sqrt_Q2=Sqrt_quotinent_S[2]?Q_sqrt_com_2:Q_sqrt2;
            end

          6'b000011:
            begin
              Sqrt_DI[0]=Mant_D_sqrt_Norm[C_MANT_FP64-17:C_MANT_FP64-18];
              Q_sqrt0={{(C_MANT_FP64-4){1'b0}},Qcnt_three_3[10:2]};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
              Sqrt_DI[1]=Mant_D_sqrt_Norm[C_MANT_FP64-19:C_MANT_FP64-20];
              Q_sqrt1={{(C_MANT_FP64-5){1'b0}},Qcnt_three_3[10:1]};
              Sqrt_Q1=Sqrt_quotinent_S[3]?Q_sqrt_com_1:Q_sqrt1;
              Sqrt_DI[2]=Mant_D_sqrt_Norm[C_MANT_FP64-21:C_MANT_FP64-22];
              Q_sqrt2={{(C_MANT_FP64-6){1'b0}},Qcnt_three_3[10:0]};
              Sqrt_Q2=Sqrt_quotinent_S[2]?Q_sqrt_com_2:Q_sqrt2;
            end

          6'b000100:
            begin
              Sqrt_DI[0]=Mant_D_sqrt_Norm[C_MANT_FP64-23:C_MANT_FP64-24];
              Q_sqrt0={{(C_MANT_FP64-7){1'b0}},Qcnt_three_4[13:2]};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
              Sqrt_DI[1]=Mant_D_sqrt_Norm[C_MANT_FP64-25:C_MANT_FP64-26];
              Q_sqrt1={{(C_MANT_FP64-8){1'b0}},Qcnt_three_4[13:1]};
              Sqrt_Q1=Sqrt_quotinent_S[3]?Q_sqrt_com_1:Q_sqrt1;
              Sqrt_DI[2]=Mant_D_sqrt_Norm[C_MANT_FP64-27:C_MANT_FP64-28];
              Q_sqrt2={{(C_MANT_FP64-9){1'b0}},Qcnt_three_4[13:0]};
              Sqrt_Q2=Sqrt_quotinent_S[2]?Q_sqrt_com_2:Q_sqrt2;
            end

          6'b000101:
            begin
              Sqrt_DI[0]=Mant_D_sqrt_Norm[C_MANT_FP64-29:C_MANT_FP64-30];
              Q_sqrt0={{(C_MANT_FP64-10){1'b0}},Qcnt_three_5[16:2]};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
              Sqrt_DI[1]=Mant_D_sqrt_Norm[C_MANT_FP64-31:C_MANT_FP64-32];
              Q_sqrt1={{(C_MANT_FP64-11){1'b0}},Qcnt_three_5[16:1]};
              Sqrt_Q1=Sqrt_quotinent_S[3]?Q_sqrt_com_1:Q_sqrt1;
              Sqrt_DI[2]=Mant_D_sqrt_Norm[C_MANT_FP64-33:C_MANT_FP64-34];
              Q_sqrt2={{(C_MANT_FP64-12){1'b0}},Qcnt_three_5[16:0]};
              Sqrt_Q2=Sqrt_quotinent_S[2]?Q_sqrt_com_2:Q_sqrt2;
            end

          6'b000110:
            begin
              Sqrt_DI[0]=Mant_D_sqrt_Norm[C_MANT_FP64-35:C_MANT_FP64-36];
              Q_sqrt0={{(C_MANT_FP64-13){1'b0}},Qcnt_three_6[19:2]};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
              Sqrt_DI[1]=Mant_D_sqrt_Norm[C_MANT_FP64-37:C_MANT_FP64-38];
              Q_sqrt1={{(C_MANT_FP64-14){1'b0}},Qcnt_three_6[19:1]};
              Sqrt_Q1=Sqrt_quotinent_S[3]?Q_sqrt_com_1:Q_sqrt1;
              Sqrt_DI[2]=Mant_D_sqrt_Norm[C_MANT_FP64-39:C_MANT_FP64-40];
              Q_sqrt2={{(C_MANT_FP64-15){1'b0}},Qcnt_three_6[19:0]};
              Sqrt_Q2=Sqrt_quotinent_S[2]?Q_sqrt_com_2:Q_sqrt2;
            end

          6'b000111:
            begin
              Sqrt_DI[0]=Mant_D_sqrt_Norm[C_MANT_FP64-41:C_MANT_FP64-42];
              Q_sqrt0={{(C_MANT_FP64-16){1'b0}},Qcnt_three_7[22:2]};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
              Sqrt_DI[1]=Mant_D_sqrt_Norm[C_MANT_FP64-43:C_MANT_FP64-44];
              Q_sqrt1={{(C_MANT_FP64-17){1'b0}},Qcnt_three_7[22:1]};
              Sqrt_Q1=Sqrt_quotinent_S[3]?Q_sqrt_com_1:Q_sqrt1;
              Sqrt_DI[2]=Mant_D_sqrt_Norm[C_MANT_FP64-45:C_MANT_FP64-46];
              Q_sqrt2={{(C_MANT_FP64-18){1'b0}},Qcnt_three_7[22:0]};
              Sqrt_Q2=Sqrt_quotinent_S[2]?Q_sqrt_com_2:Q_sqrt2;
            end

          6'b001000:
            begin
              Sqrt_DI[0]=Mant_D_sqrt_Norm[C_MANT_FP64-47:C_MANT_FP64-48];
              Q_sqrt0={{(C_MANT_FP64-19){1'b0}},Qcnt_three_8[25:2]};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
              Sqrt_DI[1]=Mant_D_sqrt_Norm[C_MANT_FP64-49:C_MANT_FP64-50];
              Q_sqrt1={{(C_MANT_FP64-20){1'b0}},Qcnt_three_8[25:1]};
              Sqrt_Q1=Sqrt_quotinent_S[3]?Q_sqrt_com_1:Q_sqrt1;
              Sqrt_DI[2]=Mant_D_sqrt_Norm[C_MANT_FP64-51:C_MANT_FP64-52];
              Q_sqrt2={{(C_MANT_FP64-21){1'b0}},Qcnt_three_8[25:0]};
              Sqrt_Q2=Sqrt_quotinent_S[2]?Q_sqrt_com_2:Q_sqrt2;
            end

          6'b001001:
            begin
              Sqrt_DI[0]=2'b00;
              Q_sqrt0={{(C_MANT_FP64-22){1'b0}},Qcnt_three_9[28:2]};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
              Sqrt_DI[1]=2'b00;
              Q_sqrt1={{(C_MANT_FP64-23){1'b0}},Qcnt_three_9[28:1]};
              Sqrt_Q1=Sqrt_quotinent_S[3]?Q_sqrt_com_1:Q_sqrt1;
              Sqrt_DI[2]=2'b00;
              Q_sqrt2={{(C_MANT_FP64-24){1'b0}},Qcnt_three_9[28:0]};
              Sqrt_Q2=Sqrt_quotinent_S[2]?Q_sqrt_com_2:Q_sqrt2;
            end

          6'b001010:
            begin
              Sqrt_DI[0]=2'b00;
              Q_sqrt0={{(C_MANT_FP64-25){1'b0}},Qcnt_three_10[31:2]};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
              Sqrt_DI[1]=2'b00;
              Q_sqrt1={{(C_MANT_FP64-26){1'b0}},Qcnt_three_10[31:1]};
              Sqrt_Q1=Sqrt_quotinent_S[3]?Q_sqrt_com_1:Q_sqrt1;
              Sqrt_DI[2]=2'b00;
              Q_sqrt2={{(C_MANT_FP64-27){1'b0}},Qcnt_three_10[31:0]};
              Sqrt_Q2=Sqrt_quotinent_S[2]?Q_sqrt_com_2:Q_sqrt2;
            end

          6'b001011:
            begin
              Sqrt_DI[0]=2'b00;
              Q_sqrt0={{(C_MANT_FP64-28){1'b0}},Qcnt_three_11[34:2]};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
              Sqrt_DI[1]=2'b00;
              Q_sqrt1={{(C_MANT_FP64-29){1'b0}},Qcnt_three_11[34:1]};
              Sqrt_Q1=Sqrt_quotinent_S[3]?Q_sqrt_com_1:Q_sqrt1;
              Sqrt_DI[2]=2'b00;
              Q_sqrt2={{(C_MANT_FP64-30){1'b0}},Qcnt_three_11[34:0]};
              Sqrt_Q2=Sqrt_quotinent_S[2]?Q_sqrt_com_2:Q_sqrt2;
            end

          6'b001100:
            begin
              Sqrt_DI[0]=2'b00;
              Q_sqrt0={{(C_MANT_FP64-31){1'b0}},Qcnt_three_12[37:2]};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
              Sqrt_DI[1]=2'b00;
              Q_sqrt1={{(C_MANT_FP64-32){1'b0}},Qcnt_three_12[37:1]};
              Sqrt_Q1=Sqrt_quotinent_S[3]?Q_sqrt_com_1:Q_sqrt1;
              Sqrt_DI[2]=2'b00;
              Q_sqrt2={{(C_MANT_FP64-33){1'b0}},Qcnt_three_12[37:0]};
              Sqrt_Q2=Sqrt_quotinent_S[2]?Q_sqrt_com_2:Q_sqrt2;
            end

          6'b001101:
            begin
              Sqrt_DI[0]=2'b00;
              Q_sqrt0={{(C_MANT_FP64-34){1'b0}},Qcnt_three_13[40:2]};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
              Sqrt_DI[1]=2'b00;
              Q_sqrt1={{(C_MANT_FP64-35){1'b0}},Qcnt_three_13[40:1]};
              Sqrt_Q1=Sqrt_quotinent_S[3]?Q_sqrt_com_1:Q_sqrt1;
              Sqrt_DI[2]=2'b00;
              Q_sqrt2={{(C_MANT_FP64-36){1'b0}},Qcnt_three_13[40:0]};
              Sqrt_Q2=Sqrt_quotinent_S[2]?Q_sqrt_com_2:Q_sqrt2;
            end

          6'b001110:
            begin
              Sqrt_DI[0]=2'b00;
              Q_sqrt0={{(C_MANT_FP64-37){1'b0}},Qcnt_three_14[43:2]};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
              Sqrt_DI[1]=2'b00;
              Q_sqrt1={{(C_MANT_FP64-38){1'b0}},Qcnt_three_14[43:1]};
              Sqrt_Q1=Sqrt_quotinent_S[3]?Q_sqrt_com_1:Q_sqrt1;
              Sqrt_DI[2]=2'b00;
              Q_sqrt2={{(C_MANT_FP64-39){1'b0}},Qcnt_three_14[43:0]};
              Sqrt_Q2=Sqrt_quotinent_S[2]?Q_sqrt_com_2:Q_sqrt2;
            end

          6'b001111:
            begin
              Sqrt_DI[0]=2'b00;
              Q_sqrt0={{(C_MANT_FP64-40){1'b0}},Qcnt_three_15[46:2]};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
              Sqrt_DI[1]=2'b00;
              Q_sqrt1={{(C_MANT_FP64-41){1'b0}},Qcnt_three_15[46:1]};
              Sqrt_Q1=Sqrt_quotinent_S[3]?Q_sqrt_com_1:Q_sqrt1;
              Sqrt_DI[2]=2'b00;
              Q_sqrt2={{(C_MANT_FP64-42){1'b0}},Qcnt_three_15[46:0]};
              Sqrt_Q2=Sqrt_quotinent_S[2]?Q_sqrt_com_2:Q_sqrt2;
            end

          6'b010000:
            begin
              Sqrt_DI[0]=2'b00;
              Q_sqrt0={{(C_MANT_FP64-43){1'b0}},Qcnt_three_16[49:2]};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
              Sqrt_DI[1]=2'b00;
              Q_sqrt1={{(C_MANT_FP64-44){1'b0}},Qcnt_three_16[49:1]};
              Sqrt_Q1=Sqrt_quotinent_S[3]?Q_sqrt_com_1:Q_sqrt1;
              Sqrt_DI[2]=2'b00;
              Q_sqrt2={{(C_MANT_FP64-45){1'b0}},Qcnt_three_16[49:0]};
              Sqrt_Q2=Sqrt_quotinent_S[2]?Q_sqrt_com_2:Q_sqrt2;
            end

          6'b010001:
            begin
              Sqrt_DI[0]=2'b00;
              Q_sqrt0={{(C_MANT_FP64-46){1'b0}},Qcnt_three_17[52:2]};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
              Sqrt_DI[1]=2'b00;
              Q_sqrt1={{(C_MANT_FP64-47){1'b0}},Qcnt_three_17[52:1]};
              Sqrt_Q1=Sqrt_quotinent_S[3]?Q_sqrt_com_1:Q_sqrt1;
              Sqrt_DI[2]=2'b00;
              Q_sqrt2={{(C_MANT_FP64-48){1'b0}},Qcnt_three_17[52:0]};
              Sqrt_Q2=Sqrt_quotinent_S[2]?Q_sqrt_com_2:Q_sqrt2;
            end

          6'b010010:
            begin
              Sqrt_DI[0]=2'b00;
              Q_sqrt0={{(C_MANT_FP64-49){1'b0}},Qcnt_three_18[55:2]};
              Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
              Sqrt_DI[1]=2'b00;
              Q_sqrt1={{(C_MANT_FP64-50){1'b0}},Qcnt_three_18[55:1]};
              Sqrt_Q1=Sqrt_quotinent_S[3]?Q_sqrt_com_1:Q_sqrt1;
              Sqrt_DI[2]=2'b00;
              Q_sqrt2={{(C_MANT_FP64-51){1'b0}},Qcnt_three_18[55:0]};
              Sqrt_Q2=Sqrt_quotinent_S[2]?Q_sqrt_com_2:Q_sqrt2;
            end

          default :
              begin
              Sqrt_DI[0]=Mant_D_sqrt_Norm[C_MANT_FP64+1:C_MANT_FP64];
              Q_sqrt0={{(C_MANT_FP64+5){1'b0}},Qcnt_three_0[2]};
              Sqrt_Q0=Q_sqrt_com_0;
              Sqrt_DI[1]=Mant_D_sqrt_Norm[C_MANT_FP64-1:C_MANT_FP64-2];
              Q_sqrt1={{(C_MANT_FP64+4){1'b0}},Qcnt_three_0[2:1]};
              Sqrt_Q1=Sqrt_quotinent_S[3]?Q_sqrt_com_1:Q_sqrt1;
              Sqrt_DI[2]=Mant_D_sqrt_Norm[C_MANT_FP64-3:C_MANT_FP64-4];
              Q_sqrt2={{(C_MANT_FP64+3){1'b0}},Qcnt_three_0[2:0]};
              Sqrt_Q2=Sqrt_quotinent_S[2]?Q_sqrt_com_2:Q_sqrt2;
            end
        endcase

      end
   /////////////////////////////////////////////////////////////////////////////
   // Operands for square root when Iteration_unit_num_S = 2'b10, end       //
   /////////////////////////////////////////////////////////////////////////////


    2'b11:
      begin
   /////////////////////////////////////////////////////////////////////////////
   // Operands for square root when Iteration_unit_num_S = 2'b11, start       //
   /////////////////////////////////////////////////////////////////////////////

              case(Crtl_cnt_S)

                6'b000000:
                  begin
                    Sqrt_DI[0]=Mant_D_sqrt_Norm[C_MANT_FP64+1:C_MANT_FP64];
                    Q_sqrt0={{(C_MANT_FP64+5){1'b0}},Qcnt_four_0[3]};
                    Sqrt_Q0=Q_sqrt_com_0;
                    Sqrt_DI[1]=Mant_D_sqrt_Norm[C_MANT_FP64-1:C_MANT_FP64-2];
                    Q_sqrt1={{(C_MANT_FP64+4){1'b0}},Qcnt_four_0[3:2]};
                    Sqrt_Q1=Sqrt_quotinent_S[3]?Q_sqrt_com_1:Q_sqrt1;
                    Sqrt_DI[2]=Mant_D_sqrt_Norm[C_MANT_FP64-3:C_MANT_FP64-4];
                    Q_sqrt2={{(C_MANT_FP64+3){1'b0}},Qcnt_four_0[3:1]};
                    Sqrt_Q2=Sqrt_quotinent_S[2]?Q_sqrt_com_2:Q_sqrt2;
                    Sqrt_DI[3]=Mant_D_sqrt_Norm[C_MANT_FP64-5:C_MANT_FP64-6];
                    Q_sqrt3={{(C_MANT_FP64+2){1'b0}},Qcnt_four_0[3:0]};
                    Sqrt_Q3=Sqrt_quotinent_S[1]?Q_sqrt_com_3:Q_sqrt3;
                  end

                6'b000001:
                  begin
                    Sqrt_DI[0]=Mant_D_sqrt_Norm[C_MANT_FP64-7:C_MANT_FP64-8];
                    Q_sqrt0={{(C_MANT_FP64+1){1'b0}},Qcnt_four_1[6:3]};
                    Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
                    Sqrt_DI[1]=Mant_D_sqrt_Norm[C_MANT_FP64-9:C_MANT_FP64-10];
                    Q_sqrt1={{(C_MANT_FP64){1'b0}},Qcnt_four_1[6:2]};
                    Sqrt_Q1=Sqrt_quotinent_S[3]?Q_sqrt_com_1:Q_sqrt1;
                    Sqrt_DI[2]=Mant_D_sqrt_Norm[C_MANT_FP64-11:C_MANT_FP64-12];
                    Q_sqrt2={{(C_MANT_FP64-1){1'b0}},Qcnt_four_1[6:1]};
                    Sqrt_Q2=Sqrt_quotinent_S[2]?Q_sqrt_com_2:Q_sqrt2;
                    Sqrt_DI[3]=Mant_D_sqrt_Norm[C_MANT_FP64-13:C_MANT_FP64-14];
                    Q_sqrt3={{(C_MANT_FP64-2){1'b0}},Qcnt_four_1[6:0]};
                    Sqrt_Q3=Sqrt_quotinent_S[1]?Q_sqrt_com_3:Q_sqrt3;
                  end

                6'b000010:
                  begin
                    Sqrt_DI[0]=Mant_D_sqrt_Norm[C_MANT_FP64-15:C_MANT_FP64-16];
                    Q_sqrt0={{(C_MANT_FP64-3){1'b0}},Qcnt_four_2[10:3]};
                    Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
                    Sqrt_DI[1]=Mant_D_sqrt_Norm[C_MANT_FP64-17:C_MANT_FP64-18];
                    Q_sqrt1={{(C_MANT_FP64-4){1'b0}},Qcnt_four_2[10:2]};
                    Sqrt_Q1=Sqrt_quotinent_S[3]?Q_sqrt_com_1:Q_sqrt1;
                    Sqrt_DI[2]=Mant_D_sqrt_Norm[C_MANT_FP64-19:C_MANT_FP64-20];
                    Q_sqrt2={{(C_MANT_FP64-5){1'b0}},Qcnt_four_2[10:1]};
                    Sqrt_Q2=Sqrt_quotinent_S[2]?Q_sqrt_com_2:Q_sqrt2;
                    Sqrt_DI[3]=Mant_D_sqrt_Norm[C_MANT_FP64-21:C_MANT_FP64-22];
                    Q_sqrt3={{(C_MANT_FP64-6){1'b0}},Qcnt_four_2[10:0]};
                    Sqrt_Q3=Sqrt_quotinent_S[1]?Q_sqrt_com_3:Q_sqrt3;
                  end

                6'b000011:
                  begin
                    Sqrt_DI[0]=Mant_D_sqrt_Norm[C_MANT_FP64-23:C_MANT_FP64-24];
                    Q_sqrt0={{(C_MANT_FP64-7){1'b0}},Qcnt_four_3[14:3]};
                    Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
                    Sqrt_DI[1]=Mant_D_sqrt_Norm[C_MANT_FP64-25:C_MANT_FP64-26];
                    Q_sqrt1={{(C_MANT_FP64-8){1'b0}},Qcnt_four_3[14:2]};
                    Sqrt_Q1=Sqrt_quotinent_S[3]?Q_sqrt_com_1:Q_sqrt1;
                    Sqrt_DI[2]=Mant_D_sqrt_Norm[C_MANT_FP64-27:C_MANT_FP64-28];
                    Q_sqrt2={{(C_MANT_FP64-9){1'b0}},Qcnt_four_3[14:1]};
                    Sqrt_Q2=Sqrt_quotinent_S[2]?Q_sqrt_com_2:Q_sqrt2;
                    Sqrt_DI[3]=Mant_D_sqrt_Norm[C_MANT_FP64-29:C_MANT_FP64-30];
                    Q_sqrt3={{(C_MANT_FP64-10){1'b0}},Qcnt_four_3[14:0]};
                    Sqrt_Q3=Sqrt_quotinent_S[1]?Q_sqrt_com_3:Q_sqrt3;
                  end

                6'b000100:
                  begin
                    Sqrt_DI[0]=Mant_D_sqrt_Norm[C_MANT_FP64-31:C_MANT_FP64-32];
                    Q_sqrt0={{(C_MANT_FP64-11){1'b0}},Qcnt_four_4[18:3]};
                    Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
                    Sqrt_DI[1]=Mant_D_sqrt_Norm[C_MANT_FP64-33:C_MANT_FP64-34];
                    Q_sqrt1={{(C_MANT_FP64-12){1'b0}},Qcnt_four_4[18:2]};
                    Sqrt_Q1=Sqrt_quotinent_S[3]?Q_sqrt_com_1:Q_sqrt1;
                    Sqrt_DI[2]=Mant_D_sqrt_Norm[C_MANT_FP64-35:C_MANT_FP64-36];
                    Q_sqrt2={{(C_MANT_FP64-13){1'b0}},Qcnt_four_4[18:1]};
                    Sqrt_Q2=Sqrt_quotinent_S[2]?Q_sqrt_com_2:Q_sqrt2;
                    Sqrt_DI[3]=Mant_D_sqrt_Norm[C_MANT_FP64-37:C_MANT_FP64-38];
                    Q_sqrt3={{(C_MANT_FP64-14){1'b0}},Qcnt_four_4[18:0]};
                    Sqrt_Q3=Sqrt_quotinent_S[1]?Q_sqrt_com_3:Q_sqrt3;
                  end

                6'b000101:
                  begin
                    Sqrt_DI[0]=Mant_D_sqrt_Norm[C_MANT_FP64-39:C_MANT_FP64-40];
                    Q_sqrt0={{(C_MANT_FP64-15){1'b0}},Qcnt_four_5[22:3]};
                    Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
                    Sqrt_DI[1]=Mant_D_sqrt_Norm[C_MANT_FP64-41:C_MANT_FP64-42];
                    Q_sqrt1={{(C_MANT_FP64-16){1'b0}},Qcnt_four_5[22:2]};
                    Sqrt_Q1=Sqrt_quotinent_S[3]?Q_sqrt_com_1:Q_sqrt1;
                    Sqrt_DI[2]=Mant_D_sqrt_Norm[C_MANT_FP64-43:C_MANT_FP64-44];
                    Q_sqrt2={{(C_MANT_FP64-17){1'b0}},Qcnt_four_5[22:1]};
                    Sqrt_Q2=Sqrt_quotinent_S[2]?Q_sqrt_com_2:Q_sqrt2;
                    Sqrt_DI[3]=Mant_D_sqrt_Norm[C_MANT_FP64-45:C_MANT_FP64-46];
                    Q_sqrt3={{(C_MANT_FP64-18){1'b0}},Qcnt_four_5[22:0]};
                    Sqrt_Q3=Sqrt_quotinent_S[1]?Q_sqrt_com_3:Q_sqrt3;
                  end

                6'b000110:
                  begin
                    Sqrt_DI[0]=Mant_D_sqrt_Norm[C_MANT_FP64-47:C_MANT_FP64-48];
                    Q_sqrt0={{(C_MANT_FP64-19){1'b0}},Qcnt_four_6[26:3]};
                    Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
                    Sqrt_DI[1]=Mant_D_sqrt_Norm[C_MANT_FP64-49:C_MANT_FP64-50];
                    Q_sqrt1={{(C_MANT_FP64-20){1'b0}},Qcnt_four_6[26:2]};
                    Sqrt_Q1=Sqrt_quotinent_S[3]?Q_sqrt_com_1:Q_sqrt1;
                    Sqrt_DI[2]=Mant_D_sqrt_Norm[C_MANT_FP64-51:C_MANT_FP64-52];
                    Q_sqrt2={{(C_MANT_FP64-21){1'b0}},Qcnt_four_6[26:1]};
                    Sqrt_Q2=Sqrt_quotinent_S[2]?Q_sqrt_com_2:Q_sqrt2;
                    Sqrt_DI[3]=2'b00;
                    Q_sqrt3={{(C_MANT_FP64-22){1'b0}},Qcnt_four_6[26:0]};
                    Sqrt_Q3=Sqrt_quotinent_S[1]?Q_sqrt_com_3:Q_sqrt3;
                  end

                6'b000111:
                  begin
                    Sqrt_DI[0]=2'b00;
                    Q_sqrt0={{(C_MANT_FP64-23){1'b0}},Qcnt_four_7[30:3]};
                    Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
                    Sqrt_DI[1]=2'b00;
                    Q_sqrt1={{(C_MANT_FP64-24){1'b0}},Qcnt_four_7[30:2]};
                    Sqrt_Q1=Sqrt_quotinent_S[3]?Q_sqrt_com_1:Q_sqrt1;
                    Sqrt_DI[2]=2'b00;
                    Q_sqrt2={{(C_MANT_FP64-25){1'b0}},Qcnt_four_7[30:1]};
                    Sqrt_Q2=Sqrt_quotinent_S[2]?Q_sqrt_com_2:Q_sqrt2;
                    Sqrt_DI[3]=2'b00;
                    Q_sqrt3={{(C_MANT_FP64-26){1'b0}},Qcnt_four_7[30:0]};
                    Sqrt_Q3=Sqrt_quotinent_S[1]?Q_sqrt_com_3:Q_sqrt3;
                  end

                6'b001000:
                  begin
                    Sqrt_DI[0]=2'b00;
                    Q_sqrt0={{(C_MANT_FP64-27){1'b0}},Qcnt_four_8[34:3]};
                    Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
                    Sqrt_DI[1]=2'b00;
                    Q_sqrt1={{(C_MANT_FP64-28){1'b0}},Qcnt_four_8[34:2]};
                    Sqrt_Q1=Sqrt_quotinent_S[3]?Q_sqrt_com_1:Q_sqrt1;
                    Sqrt_DI[2]=2'b00;
                    Q_sqrt2={{(C_MANT_FP64-29){1'b0}},Qcnt_four_8[34:1]};
                    Sqrt_Q2=Sqrt_quotinent_S[2]?Q_sqrt_com_2:Q_sqrt2;
                    Sqrt_DI[3]=2'b00;
                    Q_sqrt3={{(C_MANT_FP64-30){1'b0}},Qcnt_four_8[34:0]};
                    Sqrt_Q3=Sqrt_quotinent_S[1]?Q_sqrt_com_3:Q_sqrt3;
                  end

                6'b001001:
                  begin
                    Sqrt_DI[0]=2'b00;
                    Q_sqrt0={{(C_MANT_FP64-31){1'b0}},Qcnt_four_9[38:3]};
                    Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
                    Sqrt_DI[1]=2'b00;
                    Q_sqrt1={{(C_MANT_FP64-32){1'b0}},Qcnt_four_9[38:2]};
                    Sqrt_Q1=Sqrt_quotinent_S[3]?Q_sqrt_com_1:Q_sqrt1;
                    Sqrt_DI[2]=2'b00;
                    Q_sqrt2={{(C_MANT_FP64-33){1'b0}},Qcnt_four_9[38:1]};
                    Sqrt_Q2=Sqrt_quotinent_S[2]?Q_sqrt_com_2:Q_sqrt2;
                    Sqrt_DI[3]=2'b00;
                    Q_sqrt3={{(C_MANT_FP64-34){1'b0}},Qcnt_four_9[38:0]};
                    Sqrt_Q3=Sqrt_quotinent_S[1]?Q_sqrt_com_3:Q_sqrt3;
                  end

                6'b001010:
                  begin
                    Sqrt_DI[0]=2'b00;
                    Q_sqrt0={{(C_MANT_FP64-35){1'b0}},Qcnt_four_10[42:3]};
                    Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
                    Sqrt_DI[1]=2'b00;
                    Q_sqrt1={{(C_MANT_FP64-36){1'b0}},Qcnt_four_10[42:2]};
                    Sqrt_Q1=Sqrt_quotinent_S[3]?Q_sqrt_com_1:Q_sqrt1;
                    Sqrt_DI[2]=2'b00;
                    Q_sqrt2={{(C_MANT_FP64-37){1'b0}},Qcnt_four_10[42:1]};
                    Sqrt_Q2=Sqrt_quotinent_S[2]?Q_sqrt_com_2:Q_sqrt2;
                    Sqrt_DI[3]=2'b00;
                    Q_sqrt3={{(C_MANT_FP64-38){1'b0}},Qcnt_four_10[42:0]};
                    Sqrt_Q3=Sqrt_quotinent_S[1]?Q_sqrt_com_3:Q_sqrt3;
                  end

                6'b001011:
                  begin
                    Sqrt_DI[0]=2'b00;
                    Q_sqrt0={{(C_MANT_FP64-39){1'b0}},Qcnt_four_11[46:3]};
                    Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
                    Sqrt_DI[1]=2'b00;
                    Q_sqrt1={{(C_MANT_FP64-40){1'b0}},Qcnt_four_11[46:2]};
                    Sqrt_Q1=Sqrt_quotinent_S[3]?Q_sqrt_com_1:Q_sqrt1;
                    Sqrt_DI[2]=2'b00;
                    Q_sqrt2={{(C_MANT_FP64-41){1'b0}},Qcnt_four_11[46:1]};
                    Sqrt_Q2=Sqrt_quotinent_S[2]?Q_sqrt_com_2:Q_sqrt2;
                    Sqrt_DI[3]=2'b00;
                    Q_sqrt3={{(C_MANT_FP64-42){1'b0}},Qcnt_four_11[46:0]};
                    Sqrt_Q3=Sqrt_quotinent_S[1]?Q_sqrt_com_3:Q_sqrt3;
                  end

                6'b001100:
                  begin
                    Sqrt_DI[0]=2'b00;
                    Q_sqrt0={{(C_MANT_FP64-43){1'b0}},Qcnt_four_12[50:3]};
                    Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
                    Sqrt_DI[1]=2'b00;
                    Q_sqrt1={{(C_MANT_FP64-44){1'b0}},Qcnt_four_12[50:2]};
                    Sqrt_Q1=Sqrt_quotinent_S[3]?Q_sqrt_com_1:Q_sqrt1;
                    Sqrt_DI[2]=2'b00;
                    Q_sqrt2={{(C_MANT_FP64-45){1'b0}},Qcnt_four_12[50:1]};
                    Sqrt_Q2=Sqrt_quotinent_S[2]?Q_sqrt_com_2:Q_sqrt2;
                    Sqrt_DI[3]=2'b00;
                    Q_sqrt3={{(C_MANT_FP64-46){1'b0}},Qcnt_four_12[50:0]};
                    Sqrt_Q3=Sqrt_quotinent_S[1]?Q_sqrt_com_3:Q_sqrt3;
                  end

                6'b001101:
                  begin
                    Sqrt_DI[0]=2'b00;
                    Q_sqrt0={{(C_MANT_FP64-47){1'b0}},Qcnt_four_13[54:3]};
                    Sqrt_Q0=Quotient_DP[0]?Q_sqrt_com_0:Q_sqrt0;
                    Sqrt_DI[1]=2'b00;
                    Q_sqrt1={{(C_MANT_FP64-48){1'b0}},Qcnt_four_13[54:2]};
                    Sqrt_Q1=Sqrt_quotinent_S[3]?Q_sqrt_com_1:Q_sqrt1;
                    Sqrt_DI[2]=2'b00;
                    Q_sqrt2={{(C_MANT_FP64-49){1'b0}},Qcnt_four_13[54:1]};
                    Sqrt_Q2=Sqrt_quotinent_S[2]?Q_sqrt_com_2:Q_sqrt2;
                    Sqrt_DI[3]=2'b00;
                    Q_sqrt3={{(C_MANT_FP64-50){1'b0}},Qcnt_four_13[54:0]};
                    Sqrt_Q3=Sqrt_quotinent_S[1]?Q_sqrt_com_3:Q_sqrt3;
                  end

                default:
                  begin
                    Sqrt_DI[0]=Mant_D_sqrt_Norm[C_MANT_FP64+1:C_MANT_FP64];
                    Q_sqrt0={{(C_MANT_FP64+5){1'b0}},Qcnt_four_0[3]};
                    Sqrt_Q0=Q_sqrt_com_0;
                    Sqrt_DI[1]=Mant_D_sqrt_Norm[C_MANT_FP64-1:C_MANT_FP64-2];
                    Q_sqrt1={{(C_MANT_FP64+4){1'b0}},Qcnt_four_0[3:2]};
                    Sqrt_Q1=Sqrt_quotinent_S[3]?Q_sqrt_com_1:Q_sqrt1;
                    Sqrt_DI[2]=Mant_D_sqrt_Norm[C_MANT_FP64-3:C_MANT_FP64-4];
                    Q_sqrt2={{(C_MANT_FP64+3){1'b0}},Qcnt_four_0[3:1]};
                    Sqrt_Q2=Sqrt_quotinent_S[2]?Q_sqrt_com_2:Q_sqrt2;
                    Sqrt_DI[3]=Mant_D_sqrt_Norm[C_MANT_FP64-5:C_MANT_FP64-6];
                    Q_sqrt3={{(C_MANT_FP64+2){1'b0}},Qcnt_four_0[3:0]};
                    Sqrt_Q3=Sqrt_quotinent_S[1]?Q_sqrt_com_3:Q_sqrt3;
                  end
              endcase
            end
      endcase
   /////////////////////////////////////////////////////////////////////////////
   // Operands for square root when Iteration_unit_num_S = 2'b11, end         //
   /////////////////////////////////////////////////////////////////////////////
 end



  assign Sqrt_R0= ((Sqrt_start_dly_S)?'0:{Partial_remainder_DP[C_MANT_FP64+5:0]});
  assign Sqrt_R1= {Iteration_cell_sum_AMASK_D[0][C_MANT_FP64+5],Iteration_cell_sum_AMASK_D[0][C_MANT_FP64+2:0],Sqrt_DO[0]} ;
  assign Sqrt_R2= {Iteration_cell_sum_AMASK_D[1][C_MANT_FP64+5],Iteration_cell_sum_AMASK_D[1][C_MANT_FP64+2:0],Sqrt_DO[1]};
  assign Sqrt_R3= {Iteration_cell_sum_AMASK_D[2][C_MANT_FP64+5],Iteration_cell_sum_AMASK_D[2][C_MANT_FP64+2:0],Sqrt_DO[2]};
  assign Sqrt_R4= {Iteration_cell_sum_AMASK_D[3][C_MANT_FP64+5],Iteration_cell_sum_AMASK_D[3][C_MANT_FP64+2:0],Sqrt_DO[3]};

  logic [C_MANT_FP64+5:0]                               Denominator_se_format_DB;  //

  assign Denominator_se_format_DB={Denominator_se_DB[C_MANT_FP64+1:C_MANT_FP64-C_MANT_FP16ALT],{FP16ALT_SO?FP16ALT_SO:Denominator_se_DB[C_MANT_FP64-C_MANT_FP16ALT-1]},
                                                         Denominator_se_DB[C_MANT_FP64-C_MANT_FP16ALT-2:C_MANT_FP64-C_MANT_FP16],{FP16_SO?FP16_SO:Denominator_se_DB[C_MANT_FP64-C_MANT_FP16-1]},
                                                         Denominator_se_DB[C_MANT_FP64-C_MANT_FP16-2:C_MANT_FP64-C_MANT_FP32],{FP32_SO?FP32_SO:Denominator_se_DB[C_MANT_FP64-C_MANT_FP32-1]},
                                                         Denominator_se_DB[C_MANT_FP64-C_MANT_FP32-2:C_MANT_FP64-C_MANT_FP64],FP64_SO,3'b0} ;
  //                   for           iteration cell_U0
  logic [C_MANT_FP64+5:0]                           First_iteration_cell_div_a_D,First_iteration_cell_div_b_D;
  logic                                             Sel_b_for_first_S;


  assign First_iteration_cell_div_a_D=(Div_start_dly_S)?{Numerator_se_D[C_MANT_FP64+1:C_MANT_FP64-C_MANT_FP16ALT],{FP16ALT_SO?FP16ALT_SO:Numerator_se_D[C_MANT_FP64-C_MANT_FP16ALT-1]},
                                                         Numerator_se_D[C_MANT_FP64-C_MANT_FP16ALT-2:C_MANT_FP64-C_MANT_FP16],{FP16_SO?FP16_SO:Numerator_se_D[C_MANT_FP64-C_MANT_FP16-1]},
                                                         Numerator_se_D[C_MANT_FP64-C_MANT_FP16-2:C_MANT_FP64-C_MANT_FP32],{FP32_SO?FP32_SO:Numerator_se_D[C_MANT_FP64-C_MANT_FP32-1]},
                                                         Numerator_se_D[C_MANT_FP64-C_MANT_FP32-2:C_MANT_FP64-C_MANT_FP64],FP64_SO,3'b0}
                                                        :{Partial_remainder_DP[C_MANT_FP64+4:C_MANT_FP64-C_MANT_FP16ALT+3],{FP16ALT_SO?Quotient_DP[0]:Partial_remainder_DP[C_MANT_FP64-C_MANT_FP16ALT+2]},
                                                         Partial_remainder_DP[C_MANT_FP64-C_MANT_FP16ALT+1:C_MANT_FP64-C_MANT_FP16+3],{FP16_SO?Quotient_DP[0]:Partial_remainder_DP[C_MANT_FP64-C_MANT_FP16+2]},
                                                         Partial_remainder_DP[C_MANT_FP64-C_MANT_FP16+1:C_MANT_FP64-C_MANT_FP32+3],{FP32_SO?Quotient_DP[0]:Partial_remainder_DP[C_MANT_FP64-C_MANT_FP32+2]},
                                                         Partial_remainder_DP[C_MANT_FP64-C_MANT_FP32+1:C_MANT_FP64-C_MANT_FP64+3],FP64_SO&&Quotient_DP[0],3'b0};
  assign Sel_b_for_first_S=(Div_start_dly_S)?1:Quotient_DP[0];
  assign First_iteration_cell_div_b_D=Sel_b_for_first_S?Denominator_se_format_DB:{Denominator_se_D,4'b0};
  assign Iteration_cell_a_BMASK_D[0]=Sqrt_enable_SO?Sqrt_R0:{First_iteration_cell_div_a_D};
  assign Iteration_cell_b_BMASK_D[0]=Sqrt_enable_SO?Sqrt_Q0:{First_iteration_cell_div_b_D};



  //                   for           iteration cell_U1
  logic [C_MANT_FP64+5:0]                          Sec_iteration_cell_div_a_D,Sec_iteration_cell_div_b_D;
  logic                                            Sel_b_for_sec_S;
  generate
    if(|Iteration_unit_num_S)
      begin
        assign Sel_b_for_sec_S=~Iteration_cell_sum_AMASK_D[0][C_MANT_FP64+5];
        assign Sec_iteration_cell_div_a_D={Iteration_cell_sum_AMASK_D[0][C_MANT_FP64+4:C_MANT_FP64-C_MANT_FP16ALT+3],{FP16ALT_SO?Sel_b_for_sec_S:Iteration_cell_sum_AMASK_D[0][C_MANT_FP64-C_MANT_FP16ALT+2]},
                                           Iteration_cell_sum_AMASK_D[0][C_MANT_FP64-C_MANT_FP16ALT+1:C_MANT_FP64-C_MANT_FP16+3],{FP16_SO?Sel_b_for_sec_S:Iteration_cell_sum_AMASK_D[0][C_MANT_FP64-C_MANT_FP16+2]},
                                           Iteration_cell_sum_AMASK_D[0][C_MANT_FP64-C_MANT_FP16+1:C_MANT_FP64-C_MANT_FP32+3],{FP32_SO?Sel_b_for_sec_S:Iteration_cell_sum_AMASK_D[0][C_MANT_FP64-C_MANT_FP32+2]},
                                           Iteration_cell_sum_AMASK_D[0][C_MANT_FP64-C_MANT_FP32+1:C_MANT_FP64-C_MANT_FP64+3],FP64_SO&&Sel_b_for_sec_S,3'b0};
        assign Sec_iteration_cell_div_b_D=Sel_b_for_sec_S?Denominator_se_format_DB:{Denominator_se_D,4'b0};
        assign Iteration_cell_a_BMASK_D[1]=Sqrt_enable_SO?Sqrt_R1:{Sec_iteration_cell_div_a_D};
        assign Iteration_cell_b_BMASK_D[1]=Sqrt_enable_SO?Sqrt_Q1:{Sec_iteration_cell_div_b_D};
      end
    endgenerate

  //                   for           iteration cell_U2
  logic [C_MANT_FP64+5:0]                          Thi_iteration_cell_div_a_D,Thi_iteration_cell_div_b_D;
  logic                                            Sel_b_for_thi_S;
  generate
    if((Iteration_unit_num_S==2'b10) | (Iteration_unit_num_S==2'b11))
      begin
        assign Sel_b_for_thi_S=~Iteration_cell_sum_AMASK_D[1][C_MANT_FP64+5];
        assign Thi_iteration_cell_div_a_D={Iteration_cell_sum_AMASK_D[1][C_MANT_FP64+4:C_MANT_FP64-C_MANT_FP16ALT+3],{FP16ALT_SO?Sel_b_for_thi_S:Iteration_cell_sum_AMASK_D[1][C_MANT_FP64-C_MANT_FP16ALT+2]},
                                           Iteration_cell_sum_AMASK_D[1][C_MANT_FP64-C_MANT_FP16ALT+1:C_MANT_FP64-C_MANT_FP16+3],{FP16_SO?Sel_b_for_thi_S:Iteration_cell_sum_AMASK_D[1][C_MANT_FP64-C_MANT_FP16+2]},
                                           Iteration_cell_sum_AMASK_D[1][C_MANT_FP64-C_MANT_FP16+1:C_MANT_FP64-C_MANT_FP32+3],{FP32_SO?Sel_b_for_thi_S:Iteration_cell_sum_AMASK_D[1][C_MANT_FP64-C_MANT_FP32+2]},
                                           Iteration_cell_sum_AMASK_D[1][C_MANT_FP64-C_MANT_FP32+1:C_MANT_FP64-C_MANT_FP64+3],FP64_SO&&Sel_b_for_thi_S,3'b0};
        assign Thi_iteration_cell_div_b_D=Sel_b_for_thi_S?Denominator_se_format_DB:{Denominator_se_D,4'b0};
        assign Iteration_cell_a_BMASK_D[2]=Sqrt_enable_SO?Sqrt_R2:{Thi_iteration_cell_div_a_D};
        assign Iteration_cell_b_BMASK_D[2]=Sqrt_enable_SO?Sqrt_Q2:{Thi_iteration_cell_div_b_D};
      end
  endgenerate

  //                   for           iteration cell_U3
  logic [C_MANT_FP64+5:0]                          Fou_iteration_cell_div_a_D,Fou_iteration_cell_div_b_D;
  logic                                            Sel_b_for_fou_S;

  generate
    if(Iteration_unit_num_S==2'b11)
      begin
        assign Sel_b_for_fou_S=~Iteration_cell_sum_AMASK_D[2][C_MANT_FP64+5];
        assign Fou_iteration_cell_div_a_D={Iteration_cell_sum_AMASK_D[2][C_MANT_FP64+4:C_MANT_FP64-C_MANT_FP16ALT+3],{FP16ALT_SO?Sel_b_for_fou_S:Iteration_cell_sum_AMASK_D[2][C_MANT_FP64-C_MANT_FP16ALT+2]},
                                           Iteration_cell_sum_AMASK_D[2][C_MANT_FP64-C_MANT_FP16ALT+1:C_MANT_FP64-C_MANT_FP16+3],{FP16_SO?Sel_b_for_fou_S:Iteration_cell_sum_AMASK_D[2][C_MANT_FP64-C_MANT_FP16+2]},
                                           Iteration_cell_sum_AMASK_D[2][C_MANT_FP64-C_MANT_FP16+1:C_MANT_FP64-C_MANT_FP32+3],{FP32_SO?Sel_b_for_fou_S:Iteration_cell_sum_AMASK_D[2][C_MANT_FP64-C_MANT_FP32+2]},
                                           Iteration_cell_sum_AMASK_D[2][C_MANT_FP64-C_MANT_FP32+1:C_MANT_FP64-C_MANT_FP64+3],FP64_SO&&Sel_b_for_fou_S,3'b0};
        assign Fou_iteration_cell_div_b_D=Sel_b_for_fou_S?Denominator_se_format_DB:{Denominator_se_D,4'b0};
        assign Iteration_cell_a_BMASK_D[3]=Sqrt_enable_SO?Sqrt_R3:{Fou_iteration_cell_div_a_D};
        assign Iteration_cell_b_BMASK_D[3]=Sqrt_enable_SO?Sqrt_Q3:{Fou_iteration_cell_div_b_D};
      end
  endgenerate

   /////////////////////////////////////////////////////////////////////////////
   // Masking Contrl                                                          //
   /////////////////////////////////////////////////////////////////////////////


  logic [C_MANT_FP64+1+4:0]                          Mask_bits_ctl_S;  //For extension

  assign Mask_bits_ctl_S =58'h3ff_ffff_ffff_ffff;   //It is not needed. The corresponding process is handled the above codes

   /////////////////////////////////////////////////////////////////////////////
   // Iteration Instances  with masking control                               //
   /////////////////////////////////////////////////////////////////////////////


  logic                                             Div_enable_SI   [3:0];
  logic                                             Div_start_dly_SI   [3:0];
  logic                                             Sqrt_enable_SI   [3:0];
  generate
    genvar i,j;
      for (i=0; i <= Iteration_unit_num_S ; i++)
        begin
          for (j = 0; j <= C_MANT_FP64+5; j++) begin
              assign Iteration_cell_a_D[i][j] = Mask_bits_ctl_S[j] && Iteration_cell_a_BMASK_D[i][j];
              assign Iteration_cell_b_D[i][j] = Mask_bits_ctl_S[j] && Iteration_cell_b_BMASK_D[i][j];
              assign Iteration_cell_sum_AMASK_D[i][j] = Mask_bits_ctl_S[j] && Iteration_cell_sum_D[i][j];
          end

          assign  Div_enable_SI[i] = Div_enable_SO;
          assign  Div_start_dly_SI[i] = Div_start_dly_S;
          assign  Sqrt_enable_SI[i] = Sqrt_enable_SO;
          iteration_div_sqrt_mvp #(C_MANT_FP64+6) iteration_div_sqrt
          (
          .A_DI                                    (Iteration_cell_a_D[i]            ),
          .B_DI                                    (Iteration_cell_b_D[i]            ),
          .Div_enable_SI                           (Div_enable_SI[i]                 ),
          .Div_start_dly_SI                        (Div_start_dly_SI[i]              ),
          .Sqrt_enable_SI                          (Sqrt_enable_SI[i]                ),
          .D_DI                                    (Sqrt_DI[i]                       ),
          .D_DO                                    (Sqrt_DO[i]                       ),
          .Sum_DO                                  (Iteration_cell_sum_D[i]          ),
          .Carry_out_DO                            (Iteration_cell_carry_D[i]        )
         );

        end

  endgenerate



  always_comb
    begin
      case (Iteration_unit_num_S)
        2'b00:
          begin
            if(Fsm_enable_S)
               Partial_remainder_DN = Sqrt_enable_SO?Sqrt_R1:Iteration_cell_sum_AMASK_D[0];
            else
               Partial_remainder_DN = Partial_remainder_DP;
          end
        2'b01:
          begin
            if(Fsm_enable_S)
               Partial_remainder_DN = Sqrt_enable_SO?Sqrt_R2:Iteration_cell_sum_AMASK_D[1];
            else
               Partial_remainder_DN = Partial_remainder_DP;
          end
        2'b10:
          begin
            if(Fsm_enable_S)
               Partial_remainder_DN = Sqrt_enable_SO?Sqrt_R3:Iteration_cell_sum_AMASK_D[2];
            else
               Partial_remainder_DN = Partial_remainder_DP;
          end
        2'b11:
          begin
            if(Fsm_enable_S)
               Partial_remainder_DN = Sqrt_enable_SO?Sqrt_R4:Iteration_cell_sum_AMASK_D[3];
            else
               Partial_remainder_DN = Partial_remainder_DP;
          end
        endcase
     end



   always_ff @(posedge Clk_CI, negedge Rst_RBI)   // partial_remainder
     begin
        if(~Rst_RBI)
          begin
             Partial_remainder_DP <= '0;
          end
        else
          begin
             Partial_remainder_DP <= Partial_remainder_DN;
          end
    end

   logic [C_MANT_FP64+4:0] Quotient_DN;

  always_comb                                                      // Can choosen the different carry-outs based on different operations
    begin
      case (Iteration_unit_num_S)
        2'b00:
          begin
            if(Fsm_enable_S)
               Quotient_DN= Sqrt_enable_SO ? {Quotient_DP[C_MANT_FP64+3:0],Sqrt_quotinent_S[3]} :{Quotient_DP[C_MANT_FP64+3:0],Iteration_cell_carry_D[0]};
            else
               Quotient_DN= Quotient_DP;
          end
        2'b01:
          begin
            if(Fsm_enable_S)
               Quotient_DN= Sqrt_enable_SO ? {Quotient_DP[C_MANT_FP64+2:0],Sqrt_quotinent_S[3:2]} :{Quotient_DP[C_MANT_FP64+2:0],Iteration_cell_carry_D[0],Iteration_cell_carry_D[1]};
            else
               Quotient_DN= Quotient_DP;
          end
        2'b10:
          begin
            if(Fsm_enable_S)
               Quotient_DN= Sqrt_enable_SO ? {Quotient_DP[C_MANT_FP64+1:0],Sqrt_quotinent_S[3:1]} : {Quotient_DP[C_MANT_FP64+1:0],Iteration_cell_carry_D[0],Iteration_cell_carry_D[1],Iteration_cell_carry_D[2]};
            else
               Quotient_DN= Quotient_DP;
          end
        2'b11:
          begin
            if(Fsm_enable_S)
               Quotient_DN= Sqrt_enable_SO ? {Quotient_DP[C_MANT_FP64:0],Sqrt_quotinent_S } : {Quotient_DP[C_MANT_FP64:0],Iteration_cell_carry_D[0],Iteration_cell_carry_D[1],Iteration_cell_carry_D[2],Iteration_cell_carry_D[3]};
            else
               Quotient_DN= Quotient_DP;
          end
        endcase
     end

   always_ff @(posedge Clk_CI, negedge Rst_RBI)   // Quotient
     begin
        if(~Rst_RBI)
          begin
          Quotient_DP <= '0;
          end
        else
          Quotient_DP <= Quotient_DN;
    end


   /////////////////////////////////////////////////////////////////////////////
   // Precision Control for outputs                                          //
   /////////////////////////////////////////////////////////////////////////////


//////////////////////one iteration unit, start///////////////////////////////////////
   generate
     if(Iteration_unit_num_S==2'b00)
       begin
        always_comb
          begin
            case (Format_sel_S)
              2'b00:
                begin
                  case (Precision_ctl_S)
                    6'h00:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP32+4:0],{(C_MANT_FP64-C_MANT_FP32){1'b0}}}; //+4
                      end
                    6'h17:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP32:0],{(C_MANT_FP64-C_MANT_FP32+4){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h16:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP32-1:0],{(C_MANT_FP64-C_MANT_FP32+4+1){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h15:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP32-2:0],{(C_MANT_FP64-C_MANT_FP32+4+2){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h14:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP32-3:0],{(C_MANT_FP64-C_MANT_FP32+4+3){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h13:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP32-4:0],{(C_MANT_FP64-C_MANT_FP32+4+4){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h12:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP32-5:0],{(C_MANT_FP64-C_MANT_FP32+4+5){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h11:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP32-6:0],{(C_MANT_FP64-C_MANT_FP32+4+6){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h10:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP32-7:0],{(C_MANT_FP64-C_MANT_FP32+4+7){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h0f:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP32-8:0],{(C_MANT_FP64-C_MANT_FP32+4+8){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h0e:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP32-9:0],{(C_MANT_FP64-C_MANT_FP32+4+9){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h0d:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP32-10:0],{(C_MANT_FP64-C_MANT_FP32+4+10){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h0c:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP32-11:0],{(C_MANT_FP64-C_MANT_FP32+4+11){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h0b:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP32-12:0],{(C_MANT_FP64-C_MANT_FP32+4+12){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h0a:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP32-13:0],{(C_MANT_FP64-C_MANT_FP32+4+13){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h09:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP32-14:0],{(C_MANT_FP64-C_MANT_FP32+4+14){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h08:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP32-15:0],{(C_MANT_FP64-C_MANT_FP32+4+15){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h07:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP32-16:0],{(C_MANT_FP64-C_MANT_FP32+4+16){1'b0}}}; //Precision_ctl_S+1
                      end
                    default :
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP32+4:0],{(C_MANT_FP64-C_MANT_FP32){1'b0}}}; //+4
                      end
                  endcase
                end

              2'b01:
                begin
                  case (Precision_ctl_S)
                    6'h00:
                      begin
                        Mant_result_prenorm_DO = Quotient_DP[C_MANT_FP64+4:0]; //+4
                      end
                    6'h34:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64:0],{(4){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h33:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-1:0],{(4+1){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h32:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-2:0],{(4+2){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h31:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-3:0],{(4+3){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h30:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-4:0],{(4+4){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h2f:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-5:0],{(4+5){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h2e:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-6:0],{(4+6){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h2d:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-7:0],{(4+7){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h2c:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-8:0],{(4+8){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h2b:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-9:0],{(4+9){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h2a:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-10:0],{(4+10){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h29:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-11:0],{(4+11){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h28:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-12:0],{(4+12){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h27:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-13:0],{(4+13){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h26:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-14:0],{(4+14){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h25:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-15:0],{(4+15){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h24:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-16:0],{(4+16){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h23:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-17:0],{(4+17){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h22:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-18:0],{(4+18){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h21:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-19:0],{(4+19){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h20:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-20:0],{(4+20){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h1f:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-21:0],{(4+21){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h1e:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-22:0],{(4+22){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h1d:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-23:0],{(4+23){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h1c:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-24:0],{(4+24){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h1b:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-25:0],{(4+25){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h1a:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-26:0],{(4+26){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h19:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-27:0],{(4+27){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h18:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-28:0],{(4+28){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h17:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-29:0],{(4+29){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h16:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-30:0],{(4+30){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h15:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-31:0],{(4+31){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h14:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-32:0],{(4+32){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h13:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-33:0],{(4+33){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h12:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-34:0],{(4+34){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h11:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-35:0],{(4+35){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h10:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-36:0],{(4+36){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h0f:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-37:0],{(4+37){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h0e:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-38:0],{(4+38){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h0d:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-39:0],{(4+39){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h0c:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-40:0],{(4+40){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h0b:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-41:0],{(4+41){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h0a:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-42:0],{(4+42){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h09:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-43:0],{(4+43){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h08:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-44:0],{(4+44){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h07:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-45:0],{(4+45){1'b0}}}; //Precision_ctl_S+1
                      end
                    default:
                      begin
                        Mant_result_prenorm_DO = Quotient_DP[C_MANT_FP64+4:0]; //+4
                      end
                  endcase
                end

              2'b10:
                begin
                  case (Precision_ctl_S)
                    6'b00:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP16+4:0],{(C_MANT_FP64-C_MANT_FP16){1'b0}}}; //+4
                      end
                    6'h0a:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP16:0],{(C_MANT_FP64-C_MANT_FP16+4){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h09:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP16-1:0],{(C_MANT_FP64-C_MANT_FP16+4+1){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h08:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP16-2:0],{(C_MANT_FP64-C_MANT_FP16+4+2){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h07:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP16-3:0],{(C_MANT_FP64-C_MANT_FP16+4+3){1'b0}}}; //Precision_ctl_S+1
                      end
                    default :
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP16+4:0],{(C_MANT_FP64-C_MANT_FP16){1'b0}}}; //+4
                      end
                  endcase
                end

              2'b11:
                begin

                  case (Precision_ctl_S)
                    6'b00:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP16ALT+4:0],{(C_MANT_FP64-C_MANT_FP16ALT){1'b0}}}; //+4
                      end
                    6'h07:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP16ALT:0],{(C_MANT_FP64-C_MANT_FP16ALT+4){1'b0}}}; //Precision_ctl_S+1
                      end
                    default :
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP16ALT+4:0],{(C_MANT_FP64-C_MANT_FP16ALT){1'b0}}}; //+4
                      end
                  endcase
                end
            endcase
          end
        end
      endgenerate
//////////////////////one iteration unit, end//////////////////////////////////////////

//////////////////////two iteration units, start///////////////////////////////////////
   generate
     if(Iteration_unit_num_S==2'b01)
       begin
        always_comb
          begin
            case (Format_sel_S)
              2'b00:
                begin
                  case (Precision_ctl_S)
                    6'h00:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP32+4:0],{(C_MANT_FP64-C_MANT_FP32){1'b0}}}; //+4
                      end
                    6'h17,6'h16:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP32:0],{(C_MANT_FP64-C_MANT_FP32+4){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h15,6'h14:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP32-2:0],{(C_MANT_FP64-C_MANT_FP32+4+2){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h13,6'h12:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP32-4:0],{(C_MANT_FP64-C_MANT_FP32+4+4){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h11,6'h10:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP32-6:0],{(C_MANT_FP64-C_MANT_FP32+4+6){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h0f,6'h0e:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP32-8:0],{(C_MANT_FP64-C_MANT_FP32+4+8){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h0d,6'h0c:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP32-10:0],{(C_MANT_FP64-C_MANT_FP32+4+10){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h0b,6'h0a:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP32-12:0],{(C_MANT_FP64-C_MANT_FP32+4+12){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h09,6'h08:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP32-14:0],{(C_MANT_FP64-C_MANT_FP32+4+14){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h07,6'h06:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP32-16:0],{(C_MANT_FP64-C_MANT_FP32+4+16){1'b0}}}; //Precision_ctl_S+1
                      end
                    default:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP32+4:0],{(C_MANT_FP64-C_MANT_FP32){1'b0}}}; //+4
                      end
                  endcase
                end
              2'b01:
                begin
                  case (Precision_ctl_S)
                    6'h00:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64+3:0],1'b0}; //+3
                      end
                    6'h34:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64+1:1],{(4){1'b0}} }; //Precision_ctl_S+1
                      end
                    6'h33,6'h32:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-1:0],{(4+1){1'b0}} }; //Precision_ctl_S+1
                      end
                    6'h31,6'h30:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-3:0],{(4+3){1'b0}} }; //Precision_ctl_S+1
                      end
                    6'h2f,6'h2e:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-5:0],{(4+5){1'b0}} }; //Precision_ctl_S+1
                      end
                    6'h2d,6'h2c:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-7:0],{(4+7){1'b0}} }; //Precision_ctl_S+1
                      end
                    6'h2b,6'h2a:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-9:0],{(4+9){1'b0}} }; //Precision_ctl_S+1
                      end
                    6'h29,6'h28:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-11:0],{(4+11){1'b0}} }; //Precision_ctl_S+1
                      end
                    6'h27,6'h26:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-13:0],{(4+13){1'b0}} }; //Precision_ctl_S+1
                      end
                    6'h25,6'h24:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-15:0],{(4+15){1'b0}} }; //Precision_ctl_S+1
                      end
                    6'h23,6'h22:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-17:0],{(4+17){1'b0}} }; //Precision_ctl_S+1
                      end
                    6'h21,6'h20:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-19:0],{(4+19){1'b0}} }; //Precision_ctl_S+1
                      end
                    6'h1f,6'h1e:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-21:0],{(4+21){1'b0}} }; //Precision_ctl_S+1
                      end
                    6'h1d,6'h1c:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-23:0],{(4+23){1'b0}} }; //Precision_ctl_S+1
                      end
                    6'h1b,6'h1a:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-25:0],{(4+25){1'b0}} }; //Precision_ctl_S+1
                      end
                    6'h19,6'h18:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-27:0],{(4+27){1'b0}} }; //Precision_ctl_S+1
                      end
                    6'h17,6'h16:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-29:0],{(4+29){1'b0}} }; //Precision_ctl_S+1
                      end
                    6'h15,6'h14:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-31:0],{(4+31){1'b0}} }; //Precision_ctl_S+1
                      end
                    6'h13,6'h12:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-33:0],{(4+33){1'b0}} }; //Precision_ctl_S+1
                      end
                    6'h11,6'h10:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-35:0],{(4+35){1'b0}} }; //Precision_ctl_S+1
                      end
                    6'h0f,6'h0e:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-37:0],{(4+37){1'b0}} }; //Precision_ctl_S+1
                      end
                    6'h0d,6'h0c:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-39:0],{(4+39){1'b0}} }; //Precision_ctl_S+1
                      end
                    6'h0b,6'h0a:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-41:0],{(4+41){1'b0}} }; //Precision_ctl_S+1
                      end
                    6'h09,6'h08:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-43:0],{(4+43){1'b0}} }; //Precision_ctl_S+1
                      end
                    6'h07:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-45:0],{(4+45){1'b0}} }; //Precision_ctl_S+1
                      end
                    default:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64+3:0],1'b0}; //+3
                      end
                  endcase
                end

              2'b10:
                begin
                  case (Precision_ctl_S)
                    6'b00:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP16+3:0],{(C_MANT_FP64-C_MANT_FP16+1){1'b0}} }; //+3
                      end
                    6'h0a:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP16+1:1],{(C_MANT_FP64-C_MANT_FP16+4){1'b0}} }; //Precision_ctl_S+1
                      end
                    6'h09,6'h08:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP16-1:0],{(C_MANT_FP64-C_MANT_FP16+4+1){1'b0}} }; //Precision_ctl_S+1
                      end
                    6'h07:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP16-3:0],{(C_MANT_FP64-C_MANT_FP16+4+3){1'b0}} }; //Precision_ctl_S+1
                      end
                    default :
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP16+4:0],{(C_MANT_FP64-C_MANT_FP16){1'b0}} }; //+4
                      end
                  endcase
                end

              2'b11:
                begin

                  case (Precision_ctl_S)
                    6'b00:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP16ALT+4:0],{(C_MANT_FP64-C_MANT_FP16ALT){1'b0}} }; //+4
                      end
                    6'h07:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP16ALT:0],{(C_MANT_FP64-C_MANT_FP16ALT+4){1'b0}} }; //Precision_ctl_S+1
                      end
                    default :
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP16ALT+4:0],{(C_MANT_FP64-C_MANT_FP16ALT){1'b0}} }; //+4
                      end
                  endcase
                end
            endcase
          end
       end
     endgenerate
//////////////////////two iteration units, end//////////////////////////////////////////

//////////////////////three iteration units, start///////////////////////////////////////
   generate
     if(Iteration_unit_num_S==2'b10)
       begin
        always_comb
          begin
            case (Format_sel_S)
              2'b00:
                begin
                  case (Precision_ctl_S)
                    6'h00:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP32+3:0],{(C_MANT_FP64-C_MANT_FP32+1){1'b0}}}; //+3
                      end
                    6'h17,6'h16,6'h15:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP32:0],{(C_MANT_FP64-C_MANT_FP32+4){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h14,6'h13,6'h12:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP32-3:0],{(C_MANT_FP64-C_MANT_FP32+4+3){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h11,6'h10,6'h0f:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP32-6:0],{(C_MANT_FP64-C_MANT_FP32+4+6){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h0e,6'h0d,6'h0c:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP32-9:0],{(C_MANT_FP64-C_MANT_FP32+4+9){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h0b,6'h0a,6'h09:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP32-12:0],{(C_MANT_FP64-C_MANT_FP32+4+12){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h08,6'h07,6'h06:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP32-15:0],{(C_MANT_FP64-C_MANT_FP32+4+15){1'b0}}}; //Precision_ctl_S+1
                      end
                    default:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP32+3:0],{(C_MANT_FP64-C_MANT_FP32+1){1'b0}}}; //+3
                      end
                  endcase
                end

              2'b01:
                begin
                  case (Precision_ctl_S)
                    6'h00:
                      begin
                        Mant_result_prenorm_DO = Quotient_DP[C_MANT_FP64+4:0]; //+4
                      end
                    6'h34,6'h33:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64+1:1],{(4){1'b0}} }; //Precision_ctl_S+1
                      end
                    6'h32,6'h31,6'h30:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-2:0],{(4+2){1'b0}} }; //Precision_ctl_S+1
                      end
                    6'h2f,6'h2e,6'h2d:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-5:0],{(4+5){1'b0}} }; //Precision_ctl_S+1
                      end
                    6'h2c,6'h2b,6'h2a:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-8:0],{(4+8){1'b0}} }; //Precision_ctl_S+1
                      end
                    6'h29,6'h28,6'h27:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-11:0],{(4+11){1'b0}} }; //Precision_ctl_S+1
                      end
                    6'h26,6'h25,6'h24:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-14:0],{(4+14){1'b0}} }; //Precision_ctl_S+1
                      end
                    6'h23,6'h22,6'h21:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-17:0],{(4+17){1'b0}} }; //Precision_ctl_S+1
                      end
                    6'h20,6'h1f,6'h1e:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-20:0],{(4+20){1'b0}} }; //Precision_ctl_S+1
                      end
                    6'h1d,6'h1c,6'h1b:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-23:0],{(4+23){1'b0}} }; //Precision_ctl_S+1
                      end
                    6'h1a,6'h19,6'h18:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-26:0],{(4+26){1'b0}} }; //Precision_ctl_S+1
                      end
                    6'h17,6'h16,6'h15:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-29:0],{(4+29){1'b0}} }; //Precision_ctl_S+1
                      end
                    6'h14,6'h13,6'h12:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-32:0],{(4+32){1'b0}} }; //Precision_ctl_S+1
                      end
                    6'h11,6'h10,6'h0f:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-35:0],{(4+35){1'b0}} }; //Precision_ctl_S+1
                      end
                    6'h0e,6'h0d,6'h0c:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-38:0],{(4+38){1'b0}} }; //Precision_ctl_S+1
                      end
                    6'h0b,6'h0a,6'h09:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-41:0],{(4+41){1'b0}} }; //Precision_ctl_S+1
                      end
                    6'h08,6'h07,6'h06:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-44:0],{(4+44){1'b0}} }; //Precision_ctl_S+1
                      end
                    default:
                      begin
                        Mant_result_prenorm_DO = Quotient_DP[C_MANT_FP64+4:0]; //+4
                      end
                  endcase
                end

              2'b10:
                begin
                  case (Precision_ctl_S)
                    6'b00:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP16+4:0],{(C_MANT_FP64-C_MANT_FP16){1'b0}} }; //+4
                      end
                    6'h0a,6'h09:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP16+1:1],{(C_MANT_FP64-C_MANT_FP16+4){1'b0}} }; //Precision_ctl_S+1
                      end
                    6'h08,6'h07,6'h06:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP16-2:0],{(C_MANT_FP64-C_MANT_FP16+4+2){1'b0}} }; //Precision_ctl_S+1
                      end
                    default :
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP16+4:0],{(C_MANT_FP64-C_MANT_FP16){1'b0}} }; //+4
                      end
                  endcase
                end

              2'b11:
                begin

                  case (Precision_ctl_S)
                    6'b00:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP16ALT+4:0],{(C_MANT_FP64-C_MANT_FP16ALT){1'b0}} }; //+4
                      end
                    6'h07,6'h06:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP16ALT+1:1],{(C_MANT_FP64-C_MANT_FP16ALT+4){1'b0}} }; //Precision_ctl_S+1
                      end
                    default :
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP16ALT+4:0],{(C_MANT_FP64-C_MANT_FP16ALT){1'b0}} }; //+4
                      end
                  endcase
                end
            endcase
          end
        end
      endgenerate
//////////////////////three iteration units, end//////////////////////////////////////////

//////////////////////four iteration units, start///////////////////////////////////////
   generate
     if(Iteration_unit_num_S==2'b11)
       begin
        always_comb
          begin
            case (Format_sel_S)
              2'b00:
                begin
                  case (Precision_ctl_S)
                    6'h00:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP32+4:0],{(C_MANT_FP64-C_MANT_FP32){1'b0}}}; //+4
                      end
                    6'h17,6'h16,6'h15,6'h14:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP32:0],{(C_MANT_FP64-C_MANT_FP32+4){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h13,6'h12,6'h11,6'h10:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP32-4:0],{(C_MANT_FP64-C_MANT_FP32+4+4){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h0f,6'h0e,6'h0d,6'h0c:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP32-8:0],{(C_MANT_FP64-C_MANT_FP32+4+8){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h0b,6'h0a,6'h09,6'h08:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP32-12:0],{(C_MANT_FP64-C_MANT_FP32+4+12){1'b0}}}; //Precision_ctl_S+1
                      end
                    6'h07,6'h06:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP32-16:0],{(C_MANT_FP64-C_MANT_FP32+4+16){1'b0}}}; //Precision_ctl_S+1
                      end
                    default:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP32+4:0],{(C_MANT_FP64-C_MANT_FP32){1'b0}}}; //+4
                      end
                  endcase
                end

              2'b01:
                begin
                  case (Precision_ctl_S)
                    6'h00:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64+3:0],{(1){1'b0}}}; //+3
                      end
                    6'h34:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64+3:0],{(1){1'b0}} }; //Precision_ctl_S+1
                      end
                    6'h33,6'h32,6'h31,6'h30:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-1:0],{(5){1'b0}} }; //Precision_ctl_S+1
                      end
                    6'h2f,6'h2e,6'h2d,6'h2c:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-5:0],{(9){1'b0}} }; //Precision_ctl_S+1
                      end
                    6'h2b,6'h2a,6'h29,6'h28:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-9:0],{(13){1'b0}} }; //Precision_ctl_S+1
                      end
                    6'h27,6'h26,6'h25,6'h24:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-13:0],{(17){1'b0}} }; //Precision_ctl_S+1
                      end
                    6'h23,6'h22,6'h21,6'h20:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-17:0],{(21){1'b0}} }; //Precision_ctl_S+1
                      end
                    6'h1f,6'h1e,6'h1d,6'h1c:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-21:0],{(25){1'b0}} }; //Precision_ctl_S+1
                      end
                    6'h1b,6'h1a,6'h19,6'h18:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-25:0],{(29){1'b0}} }; //Precision_ctl_S+1
                      end
                    6'h17,6'h16,6'h15,6'h14:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-29:0],{(33){1'b0}} }; //Precision_ctl_S+1
                      end
                    6'h13,6'h12,6'h11,6'h10:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-33:0],{(37){1'b0}} }; //Precision_ctl_S+1
                      end
                    6'h0f,6'h0e,6'h0d,6'h0c:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-37:0],{(41){1'b0}} }; //Precision_ctl_S+1
                      end
                    6'h0b,6'h0a,6'h09,6'h08:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-41:0],{(45){1'b0}} }; //Precision_ctl_S+1
                      end
                    6'h07,6'h06:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64-45:0],{(49){1'b0}} }; //Precision_ctl_S+1
                      end
                    default:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP64+3:0],{(1){1'b0}}}; //+3
                      end
                  endcase
                end

              2'b10:
                begin
                  case (Precision_ctl_S)
                    6'b00:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP16+5:0],{(C_MANT_FP64-C_MANT_FP16-1){1'b0}} }; //+5
                      end
                    6'h0a,6'h09,6'h08:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP16+1:1],{(C_MANT_FP64-C_MANT_FP16+4){1'b0}} }; //Precision_ctl_S+1
                      end
                    6'h07,6'h06:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP16+1-4:0],{(C_MANT_FP64-C_MANT_FP16+4+3){1'b0}} }; //Precision_ctl_S+1
                      end
                    default :
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP16+5:0],{(C_MANT_FP64-C_MANT_FP16-1){1'b0}} }; //+5
                      end
                  endcase
                end

              2'b11:
                begin

                  case (Precision_ctl_S)
                    6'b00:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP16ALT+4:0],{(C_MANT_FP64-C_MANT_FP16ALT){1'b0}} }; //+4
                      end
                    6'h07,6'h06:
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP16ALT:0],{(C_MANT_FP64-C_MANT_FP16ALT+4){1'b0}} }; //Precision_ctl_S+1
                      end
                    default :
                      begin
                        Mant_result_prenorm_DO = {Quotient_DP[C_MANT_FP16ALT+4:0],{(C_MANT_FP64-C_MANT_FP16ALT){1'b0}} }; //+4
                      end
                  endcase
                end
            endcase
          end
        end
      endgenerate
//////////////////////four iteration units, end///////////////////////////////////////





// resultant exponent
   logic   [C_EXP_FP64+1:0]    Exp_result_prenorm_DN,Exp_result_prenorm_DP;

   logic   [C_EXP_FP64+1:0]                                Exp_add_a_D;
   logic   [C_EXP_FP64+1:0]                                Exp_add_b_D;
   logic   [C_EXP_FP64+1:0]                                Exp_add_c_D;

  integer                                                 C_BIAS_AONE, C_HALF_BIAS;
  always_comb
    begin  //
      case (Format_sel_S)
        2'b00:
          begin
            C_BIAS_AONE =C_BIAS_AONE_FP32;
            C_HALF_BIAS =C_HALF_BIAS_FP32;
          end
        2'b01:
          begin
            C_BIAS_AONE =C_BIAS_AONE_FP64;
            C_HALF_BIAS =C_HALF_BIAS_FP64;
          end
        2'b10:
          begin
            C_BIAS_AONE =C_BIAS_AONE_FP16;
            C_HALF_BIAS =C_HALF_BIAS_FP16;
          end
        2'b11:
          begin
            C_BIAS_AONE =C_BIAS_AONE_FP16ALT;
            C_HALF_BIAS =C_HALF_BIAS_FP16ALT;
          end
        endcase
    end

//For division, exponent=(Exp_a_D-LZ1)-(Exp_b_D-LZ2)+BIAS
//For square root, exponent=(Exp_a_D-LZ1)/2+(Exp_a_D-LZ1)%2+C_HALF_BIAS
//For exponent, in preprorces module, (Exp_a_D-LZ1) and (Exp_b_D-LZ2) have been processed with the corresponding process for denormal numbers.

  assign Exp_add_a_D = {Sqrt_start_dly_S?{Exp_num_DI[C_EXP_FP64],Exp_num_DI[C_EXP_FP64],Exp_num_DI[C_EXP_FP64],Exp_num_DI[C_EXP_FP64:1]}:{Exp_num_DI[C_EXP_FP64],Exp_num_DI[C_EXP_FP64],Exp_num_DI}};
  assign Exp_add_b_D = {Sqrt_start_dly_S?{1'b0,{C_EXP_ZERO_FP64},Exp_num_DI[0]}:{~Exp_den_DI[C_EXP_FP64],~Exp_den_DI[C_EXP_FP64],~Exp_den_DI}};
  assign Exp_add_c_D = {Div_start_dly_S?{{C_BIAS_AONE}}:{{C_HALF_BIAS}}};
  assign Exp_result_prenorm_DN  = (Start_dly_S)?{Exp_add_a_D + Exp_add_b_D + Exp_add_c_D}:Exp_result_prenorm_DP;


  always_ff @(posedge Clk_CI, negedge Rst_RBI)
   begin
      if(~Rst_RBI)
        begin
          Exp_result_prenorm_DP <= '0;
        end
      else
        begin
          Exp_result_prenorm_DP<=  Exp_result_prenorm_DN;
        end
   end

  assign Exp_result_prenorm_DO = Exp_result_prenorm_DP;

endmodule
