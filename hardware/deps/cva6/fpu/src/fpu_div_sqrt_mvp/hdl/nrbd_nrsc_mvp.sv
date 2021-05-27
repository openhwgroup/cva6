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
// Engineers:      Lei Li      lile@iis.ee.ethz.ch                            //
//                                                                            //
// Additional contributions by:                                               //
//                                                                            //
//                                                                            //
//                                                                            //
// Create Date:    10/04/2018                                                 //
// Design Name:    FPU                                                        //
// Module Name:    nrbd_nrsc_mvp.sv                                           //
// Project Name:   Private FPU                                                //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:   non restroring binary  divisior/ square root                //
//                                                                            //
// Revision Date:  12/04/2018                                                 //
//                 Lei Li                                                     //
//                 To address some requirements by Stefan and add low power   //
//                 control for special cases                                  //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

import defs_div_sqrt_mvp::*;

module nrbd_nrsc_mvp

  (//Input
   input logic                                 Clk_CI,
   input logic                                 Rst_RBI,
   input logic                                 Div_start_SI,
   input logic                                 Sqrt_start_SI,
   input logic                                 Start_SI,
   input logic                                 Kill_SI,
   input logic                                 Special_case_SBI,
   input logic                                 Special_case_dly_SBI,
   input logic [C_PC-1:0]                      Precision_ctl_SI,
   input logic [1:0]                           Format_sel_SI,
   input logic [C_MANT_FP64:0]                 Mant_a_DI,
   input logic [C_MANT_FP64:0]                 Mant_b_DI,
   input logic [C_EXP_FP64:0]                  Exp_a_DI,
   input logic [C_EXP_FP64:0]                  Exp_b_DI,
  //output
   output logic                                Div_enable_SO,
   output logic                                Sqrt_enable_SO,

   output logic                                Full_precision_SO,
   output logic                                FP32_SO,
   output logic                                FP64_SO,
   output logic                                FP16_SO,
   output logic                                FP16ALT_SO,
   output logic                                Ready_SO,
   output logic                                Done_SO,
   output logic  [C_MANT_FP64+4:0]             Mant_z_DO,
   output logic [C_EXP_FP64+1:0]               Exp_z_DO
    );


    logic                                     Div_start_dly_S,Sqrt_start_dly_S;


control_mvp         control_U0
(  .Clk_CI                                   (Clk_CI                          ),
   .Rst_RBI                                  (Rst_RBI                         ),
   .Div_start_SI                             (Div_start_SI                    ),
   .Sqrt_start_SI                            (Sqrt_start_SI                   ),
   .Start_SI                                 (Start_SI                        ),
   .Kill_SI                                  (Kill_SI                         ),
   .Special_case_SBI                         (Special_case_SBI                ),
   .Special_case_dly_SBI                     (Special_case_dly_SBI            ),
   .Precision_ctl_SI                         (Precision_ctl_SI                ),
   .Format_sel_SI                            (Format_sel_SI                   ),
   .Numerator_DI                             (Mant_a_DI                       ),
   .Exp_num_DI                               (Exp_a_DI                        ),
   .Denominator_DI                           (Mant_b_DI                       ),
   .Exp_den_DI                               (Exp_b_DI                        ),
   .Div_start_dly_SO                         (Div_start_dly_S                 ),
   .Sqrt_start_dly_SO                        (Sqrt_start_dly_S                ),
   .Div_enable_SO                            (Div_enable_SO                   ),
   .Sqrt_enable_SO                           (Sqrt_enable_SO                  ),
   .Full_precision_SO                        (Full_precision_SO               ),
   .FP32_SO                                  (FP32_SO                         ),
   .FP64_SO                                  (FP64_SO                         ),
   .FP16_SO                                  (FP16_SO                         ),
   .FP16ALT_SO                               (FP16ALT_SO                      ),
   .Ready_SO                                 (Ready_SO                        ),
   .Done_SO                                  (Done_SO                         ),
   .Mant_result_prenorm_DO                   (Mant_z_DO                       ),
   .Exp_result_prenorm_DO                    (Exp_z_DO                        )
);



endmodule
