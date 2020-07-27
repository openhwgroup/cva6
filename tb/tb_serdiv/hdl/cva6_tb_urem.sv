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
num_stim   = 6+1000;

test_name  = "urem test";

acq_trig     <= 1;
`APPL_WAIT_CYC(clk_i, 2)
acq_trig     <= 0;
`APPL_WAIT_CYC(clk_i, 2)

///////////////////////////////////////////////
`APPL_WAIT_SIG(clk_i, in_rdy_o)

opcode_i   = 2;

op_a       = 100;
op_b       = 2;

op_a_i      = op_a;
op_b_i      = op_b;

in_vld_i    = 1;
`APPL_WAIT_CYC(clk_i, 1)
in_vld_i    = 0;
////////////////////
`APPL_WAIT_SIG(clk_i, in_rdy_o)

op_a       = MAX_NUM64;
op_b       = 1;

op_a_i      = op_a;
op_b_i      = op_b;

in_vld_i    = 1;
`APPL_WAIT_CYC(clk_i, 1)
in_vld_i    = 0;
////////////////////
`APPL_WAIT_SIG(clk_i, in_rdy_o)

op_a       = 1;
op_b       = MAX_NUM64;

op_a_i      = op_a;
op_b_i      = op_b;

in_vld_i    = 1;
`APPL_WAIT_CYC(clk_i, 1)
in_vld_i    = 0;
////////////////////
`APPL_WAIT_SIG(clk_i, in_rdy_o)

op_a       = 0;
op_b       = 5456;

op_a_i      = op_a;
op_b_i      = op_b;

in_vld_i    = 1;
`APPL_WAIT_CYC(clk_i, 1)
in_vld_i    = 0;
////////////////////
`APPL_WAIT_SIG(clk_i, in_rdy_o)

op_a       = 875;
op_b       = 0;

op_a_i      = op_a;
op_b_i      = op_b;

in_vld_i    = 1;
`APPL_WAIT_CYC(clk_i, 1)
in_vld_i    = 0;
////////////////////
`APPL_WAIT_SIG(clk_i, in_rdy_o)

op_a       = 0;
op_b       = 0;

op_a_i      = op_a;
op_b_i      = op_b;

in_vld_i    = 1;
`APPL_WAIT_CYC(clk_i, 1)
in_vld_i    = 0;
`APPL_WAIT_SIG(clk_i, in_rdy_o)


////////////////////
// a couple of random stimuli

for (k = 0; k < 1000; k++) begin

    `APPL_WAIT_SIG(clk_i, in_rdy_o)

    void'(randomize(op_a_i));
    void'(randomize(op_b_i));
    op_a = op_a_i;
    op_b = op_b_i;

    in_vld_i    = 1;
    `APPL_WAIT_CYC(clk_i, 1)
    in_vld_i    = 0;
    `APPL_WAIT_SIG(clk_i, in_rdy_o)

end

`APPL_WAIT_CYC(clk_i, 400)
///////////////////////////////////////////////
