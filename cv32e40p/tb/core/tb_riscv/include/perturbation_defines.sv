// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
//                                                                                                          //
// Author:                              Francesco Minervini - minervif@student.ethz.ch                      //
//                                                                                                          //
// Additional contributions by:                                                                             //
// Design Name:                         Interrupt generator                                                 //
// Project Name:                        RI5CY, Zeroriscy                                                    //
// Language:                            SystemVerilog                                                       //
//                                                                                                          //
// Description:                         Defines for the perturbation module                                 //
//////////////////////////////////////////////////////////////////////////////////////////////////////////////

package perturbation_defines;

    parameter STANDARD   =  32'h1;
    parameter RANDOM     =  32'h2;
    parameter PC_TRIG    =  32'h3;

endpackage