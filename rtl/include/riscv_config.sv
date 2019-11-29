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
// Additional contributions by:                                               //
//                                                                            //
// Design Name:    RISC-V config file                                         //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Configure optional simulation modules                      //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

// no traces for synthesis, they are not synthesizable
`ifndef VERILATOR
`ifndef SYNTHESIS
`ifndef PULP_FPGA_EMUL
`define TRACE_EXECUTION
`endif
`endif
`endif

`ifdef PULP_FPGA_SIM
`define TRACE_EXECUTION
`endif

// to store traces of FPU/APU operations
//`define APU_TRACE
