// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Michael Schaffner (schaffner@iis.ee.ethz.ch), ETH Zurich
//         Andreas Traber    (traber@iis.ee.ethz.ch), ETH Zurich
//
// Date: 18.10.2018
// Description: testbench for serial 64bit divider

///////////////////////////////////////////////
// unsigned division test

// init
num_stim   = 5+1000;

test_name  = "rem test";

acq_trig     <= 1;
`APPL_WAIT_CYC(clk_i, 2)
acq_trig     <= 0;
`APPL_WAIT_CYC(clk_i, 2)

///////////////////////////////////////////////
`APPL_WAIT_SIG(clk_i, in_rdy_o)

opcode_i   = 3;

op_a       = 100;
op_b       = -10;

op_a_i      = op_a;
op_b_i      = op_b;

in_vld_i    = 1;
`APPL_WAIT_CYC(clk_i, 1)
in_vld_i    = 0;
///////////////////////////////////////////////
`APPL_WAIT_SIG(clk_i, in_rdy_o)

in_vld_i    = 0;

op_a       = -100;
op_b       = -10;

op_a_i      = op_a;
op_b_i      = op_b;

in_vld_i    = 1;
`APPL_WAIT_CYC(clk_i, 1)
in_vld_i    = 0;
///////////////////////////////////////////////
`APPL_WAIT_SIG(clk_i, in_rdy_o)

op_a       = -100;
op_b       = 0;

op_a_i      = op_a;
op_b_i      = op_b;

in_vld_i    = 1;
`APPL_WAIT_CYC(clk_i, 1)
in_vld_i    = 0;
///////////////////////////////////////////////
`APPL_WAIT_SIG(clk_i, in_rdy_o)

op_a       = MIN_NUM;
op_b       = 1;

op_a_i      = op_a;
op_b_i      = op_b;

in_vld_i    = 1;
`APPL_WAIT_CYC(clk_i, 1)
in_vld_i    = 0;
///////////////////////////////////////////////
`APPL_WAIT_SIG(clk_i, in_rdy_o)

op_a       = MIN_NUM;
op_b       = -1;

op_a_i      = op_a;
op_b_i      = op_b;

in_vld_i    = 1;
`APPL_WAIT_CYC(clk_i, 1)
in_vld_i    = 0;
////////////////////
`APPL_WAIT_SIG(clk_i, in_rdy_o)

////////////////////
// a couple of random stimuli

for (k = 0; k < 1000; k++) begin

  void'(randomize(op_a_i));
  void'(randomize(op_b_i));
  op_a = $signed(op_a_i);
  op_b = $signed(op_b_i);

  in_vld_i    = 1;
  `APPL_WAIT_CYC(clk_i, 1)
  in_vld_i    = 0;
  `APPL_WAIT_SIG(clk_i, in_rdy_o)

end

`APPL_WAIT_CYC(clk_i, 400)

///////////////////////////////////////////////
