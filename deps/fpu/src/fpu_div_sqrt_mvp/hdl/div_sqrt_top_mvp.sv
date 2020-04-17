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
// Create Date:    03/03/2018                                                 //
// Design Name:    div_sqrt_top_mvp                                           //
// Module Name:    div_sqrt_top_mvp.sv                                        //
// Project Name:   The shared divisor and square root                         //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    The top of div and sqrt                                    //
//                                                                            //
//                                                                            //
// Revision Date:  12/04/2018                                                 //
//                 Lei Li                                                     //
//                 To address some requirements by Stefan and add low power   //
//                 control for special cases                                  //
////////////////////////////////////////////////////////////////////////////////

import defs_div_sqrt_mvp::*;

module div_sqrt_top_mvp

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





   //Operand components
   logic [C_EXP_FP64:0]                 Exp_a_D;
   logic [C_EXP_FP64:0]                 Exp_b_D;
   logic [C_MANT_FP64:0]                Mant_a_D;
   logic [C_MANT_FP64:0]                Mant_b_D;

   logic [C_EXP_FP64+1:0]               Exp_z_D;
   logic [C_MANT_FP64+4:0]              Mant_z_D;
   logic                                Sign_z_D;
   logic                                Start_S;
   logic [C_RM-1:0]                     RM_dly_S;
   logic                                Div_enable_S;
   logic                                Sqrt_enable_S;
   logic                                Inf_a_S;
   logic                                Inf_b_S;
   logic                                Zero_a_S;
   logic                                Zero_b_S;
   logic                                NaN_a_S;
   logic                                NaN_b_S;
   logic                                SNaN_S;
   logic                                Special_case_SB,Special_case_dly_SB;

   logic Full_precision_S;
   logic FP32_S;
   logic FP64_S;
   logic FP16_S;
   logic FP16ALT_S;


 preprocess_mvp  preprocess_U0
 (
   .Clk_CI                (Clk_CI             ),
   .Rst_RBI               (Rst_RBI            ),
   .Div_start_SI          (Div_start_SI       ),
   .Sqrt_start_SI         (Sqrt_start_SI      ),
   .Ready_SI              (Ready_SO           ),
   .Operand_a_DI          (Operand_a_DI       ),
   .Operand_b_DI          (Operand_b_DI       ),
   .RM_SI                 (RM_SI              ),
   .Format_sel_SI         (Format_sel_SI      ),
   .Start_SO              (Start_S            ),
   .Exp_a_DO_norm         (Exp_a_D            ),
   .Exp_b_DO_norm         (Exp_b_D            ),
   .Mant_a_DO_norm        (Mant_a_D           ),
   .Mant_b_DO_norm        (Mant_b_D           ),
   .RM_dly_SO             (RM_dly_S           ),
   .Sign_z_DO             (Sign_z_D           ),
   .Inf_a_SO              (Inf_a_S            ),
   .Inf_b_SO              (Inf_b_S            ),
   .Zero_a_SO             (Zero_a_S           ),
   .Zero_b_SO             (Zero_b_S           ),
   .NaN_a_SO              (NaN_a_S            ),
   .NaN_b_SO              (NaN_b_S            ),
   .SNaN_SO               (SNaN_S             ),
   .Special_case_SBO      (Special_case_SB    ),
   .Special_case_dly_SBO  (Special_case_dly_SB)
   );

 nrbd_nrsc_mvp   nrbd_nrsc_U0
  (
   .Clk_CI                (Clk_CI             ),
   .Rst_RBI               (Rst_RBI            ),
   .Div_start_SI          (Div_start_SI       ) ,
   .Sqrt_start_SI         (Sqrt_start_SI      ),
   .Start_SI              (Start_S            ),
   .Kill_SI               (Kill_SI            ),
   .Special_case_SBI      (Special_case_SB    ),
   .Special_case_dly_SBI  (Special_case_dly_SB),
   .Div_enable_SO         (Div_enable_S       ),
   .Sqrt_enable_SO        (Sqrt_enable_S      ),
   .Precision_ctl_SI      (Precision_ctl_SI   ),
   .Format_sel_SI         (Format_sel_SI      ),
   .Exp_a_DI              (Exp_a_D            ),
   .Exp_b_DI              (Exp_b_D            ),
   .Mant_a_DI             (Mant_a_D           ),
   .Mant_b_DI             (Mant_b_D           ),
   .Full_precision_SO     (Full_precision_S   ),
   .FP32_SO               (FP32_S             ),
   .FP64_SO               (FP64_S             ),
   .FP16_SO               (FP16_S             ),
   .FP16ALT_SO            (FP16ALT_S          ),
   .Ready_SO              (Ready_SO           ),
   .Done_SO               (Done_SO            ),
   .Exp_z_DO              (Exp_z_D            ),
   .Mant_z_DO             (Mant_z_D           )
    );


 norm_div_sqrt_mvp  fpu_norm_U0
  (
   .Mant_in_DI            (Mant_z_D           ),
   .Exp_in_DI             (Exp_z_D            ),
   .Sign_in_DI            (Sign_z_D           ),
   .Div_enable_SI         (Div_enable_S       ),
   .Sqrt_enable_SI        (Sqrt_enable_S      ),
   .Inf_a_SI              (Inf_a_S            ),
   .Inf_b_SI              (Inf_b_S            ),
   .Zero_a_SI             (Zero_a_S           ),
   .Zero_b_SI             (Zero_b_S           ),
   .NaN_a_SI              (NaN_a_S            ),
   .NaN_b_SI              (NaN_b_S            ),
   .SNaN_SI               (SNaN_S             ),
   .RM_SI                 (RM_dly_S           ),
   .Full_precision_SI     (Full_precision_S   ),
   .FP32_SI               (FP32_S             ),
   .FP64_SI               (FP64_S             ),
   .FP16_SI               (FP16_S             ),
   .FP16ALT_SI            (FP16ALT_S          ),
   .Result_DO             (Result_DO          ),
   .Fflags_SO             (Fflags_SO          ) //{NV,DZ,OF,UF,NX}
   );

endmodule
