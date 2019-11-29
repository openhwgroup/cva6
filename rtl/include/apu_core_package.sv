// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Engineer:       Michael Gautschi - gautschi@iis.ee.ethz.ch                 //
//                                                                            //
// Design Name:    APU-core package                                           //
// Project Name:   RISC-V                                                     //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    core package of RISC-V core for shared APU                 //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

package apu_core_package;

   /////////////////////////////////////////////////////////////////////////////
   //  IMPORTANT!!                                                            //
   /////////////////////////////////////////////////////////////////////////////
   // THESE PARAMETERS HAVE TO MATCH THE ones in ulpcluster/apu_package.sv    //
   /////////////////////////////////////////////////////////////////////////////

   // by default set to 0
   parameter SHARED_INT_MULT   = 0;

   /////////////////////////////////////////////////////////////////////////////
   // until here                                                              //
   /////////////////////////////////////////////////////////////////////////////

   // FP-general
   parameter APU_FLAGS_FP    = 2;
   parameter APU_FLAGS_FPNEW = 3;

   // DSP-Mult
   parameter PIPE_REG_DSP_MULT  = 1;
   parameter APU_FLAGS_DSP_MULT = 0;

   // Int-Mult
   parameter APU_FLAGS_INT_MULT = 1;

   // Int-div

   // addsub
   parameter PIPE_REG_ADDSUB  = 1;

   // mult
   parameter PIPE_REG_MULT = 1;

   // casts
   parameter PIPE_REG_CAST = 1;

   // mac
   parameter PIPE_REG_MAC = 2;

   // div
   parameter PIPE_REG_DIV = 4;

   // sqrt
   parameter PIPE_REG_SQRT = 5;

   // iter divsqrt

endpackage // apu_core_package
