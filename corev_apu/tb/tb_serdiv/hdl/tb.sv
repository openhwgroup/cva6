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
//

`include "tb.svh"

import ariane_pkg::*;
import tb_pkg::*;

// tb package
module tb;

///////////////////////////////////////////////////////////////////////////////
// config
///////////////////////////////////////////////////////////////////////////////

  // leave this
  timeunit 1ps;
  timeprecision 1ps;

  parameter                          VERBOSE   = 1;
  parameter                          WIDTH     = 64;
  parameter logic        [WIDTH-1:0] MAX_NUM64 = '1;
  parameter logic        [WIDTH-2:0] MAX_NUM63 = '1;
  parameter logic signed [WIDTH-1:0] MIN_NUM   = {1'b1,{WIDTH-1{1'b0}}};

///////////////////////////////////////////////////////////////////////////////
// MUT signal declarations
///////////////////////////////////////////////////////////////////////////////


  logic signed [WIDTH:0]      op_a, op_b;
  logic signed [WIDTH:0]      op_a_tmp, op_b_tmp;

  logic                       flush_i;
  logic [TRANS_ID_BITS-1:0]   id_i;
  logic [TRANS_ID_BITS-1:0]   id_o;

  logic [WIDTH-1:0]           op_a_i;
  logic [WIDTH-1:0]           op_b_i;

  logic [1:0]                 opcode_i;
  logic [1:0]                 opcode_tmp;

  logic                       in_rdy_o;
  logic                       in_vld_i;
  logic                       out_rdy_i;
  logic                       out_vld_o;
  logic [WIDTH-1:0]           res_o;

///////////////////////////////////////////////////////////////////////////////
// TB signal declarations
///////////////////////////////////////////////////////////////////////////////

  logic   clk_i, rst_ni;
  logic   stim_start, stim_end, end_of_sim;
  longint num_stim;
  logic   acq_trig;
  string  test_name;

///////////////////////////////////////////////////////////////////////////////
// Clock Process
///////////////////////////////////////////////////////////////////////////////

  always @*
  begin
    do begin
      clk_i = 1; #(CLK_HI);
      clk_i = 0; #(CLK_LO);
    end while (end_of_sim == 1'b0);
    // generate one extra cycle to allow response acquisition to complete
    clk_i = 1; #(CLK_HI);
    clk_i = 0; #(CLK_LO);
  end


///////////////////////////////////////////////////////////////////////////////
// MUT
///////////////////////////////////////////////////////////////////////////////


  assign OpBIsZero_SI = ~(|op_b_i);
  serdiv #(.WIDTH(WIDTH)) i_dut (.*);

///////////////////////////////////////////////////////////////////////////////
// application process
///////////////////////////////////////////////////////////////////////////////

  initial begin : p_stim
    longint signed k;
    bit randBit;

    stim_start = 0;
    stim_end   = 0;
    num_stim   = 0;
    test_name  = "";
    acq_trig   = 0;

    rst_ni     = 0;

    op_a       = 0;
    op_b       = 0;

    op_a_i      = 0;
    op_b_i      = 0;
    opcode_i   = 0;
    in_vld_i    = 0;
    flush_i    = 0;
    id_i  = 0;

    `APPL_WAIT_CYC(clk_i, 100)

    rst_ni <= 1'b1;

    `APPL_WAIT_CYC(clk_i, 100)

    $display("TB> stimuli application started");
    stim_start <= 1'b1;
    `APPL_WAIT_CYC(clk_i, 100)

    ///////////////////////////////////////////////
    // unsigned division test

    `include "tb_udiv.sv"

    ///////////////////////////////////////////////
    // unsigned modulo test

    `include "tb_urem.sv"

    ///////////////////////////////////////////////
    // signed division test

    `include "tb_div.sv"

    ///////////////////////////////////////////////
    // signed modulo test

    `include "tb_rem.sv"

    ///////////////////////////////////////////////

    `APPL_WAIT_CYC(clk_i, 400)

    stim_end <= 1;
    $display("TB> stimuli application ended");

  end


///////////////////////////////////////////////////////////////////////////////
// acquisition process
///////////////////////////////////////////////////////////////////////////////


  initial begin : p_acq

    ///////////////////////////////////////////////
    // define vars, init...
    ///////////////////////////////////////////////
    bit ok;
    string opStr;
    progress status;
    string failingTests, tmpstr;
    longint acqCnt, res, act;

    status       = new("TB");
    failingTests = "";

    out_rdy_i  = 0;
    end_of_sim = 0;

    `ACQ_WAIT_SIG(clk_i, stim_start)

    $display("TB> response acquisition started");

    ///////////////////////////////////////////////
    // acquisiton and verification
    ///////////////////////////////////////////////
    repeat(4) begin

      // wait for acquisition trigger
      do begin
        `ACQ_WAIT_CYC(clk_i, 1)
        if (stim_end == 1) begin
          end_of_sim <= 1;
          $display("response acquisition ended");
          $finish();
        end
      end while(acq_trig == 1'b0);

      acqCnt = 0;

      $display("");
      $display("TB> ----------------------------------------------------------------------");
      $display("TB> %s", test_name);
      $display("TB> ----------------------------------------------------------------------\n");
      $display("");

      $display("TB> checking %00d vectors",num_stim);
      $display("");
      status.reset(num_stim);

      do begin



        out_rdy_i = 1'b1;

        `ACQ_WAIT_SIG(clk_i, in_vld_i)

        opcode_tmp = opcode_i;
        op_a_tmp    = op_a;
        op_b_tmp    = op_b;

        //////////////////////////
        // udiv / udiv
        if(opcode_i[1] == 1'b0) begin

          res = op_a_tmp/op_b_tmp;

          if((op_b_tmp == 0) && (opcode_i[0] == 0)) begin
            res = MAX_NUM64;
          end else if ((op_b_tmp == 0) && (opcode_i[0] == 1'b1)) begin
            res = -1;
          end else if ((op_a_tmp == MIN_NUM)  && (op_b_tmp == -1) && (opcode_i[0] == 1'b1)) begin
            res = MIN_NUM;
          end

          `ACQ_WAIT_SIG(clk_i, out_vld_o)

          // interpret result correctly!
          if (opcode_tmp[0] == 1'b1)
            act = $signed(res_o);
          else
            act = $unsigned(res_o);

            opStr="/";
        //////////////////////////
        // rem / urem
        end else if(opcode_i[1] == 1'b1) begin

          res = op_a_tmp % op_b_tmp;

          if((op_b_tmp == 0)) begin
            res = op_a_tmp;
          end

          `ACQ_WAIT_SIG(clk_i, out_vld_o)

          // interpret result correctly!
          if (opcode_tmp[0] == 1'b1)
            act = $signed(res_o);
          else
            act = $unsigned(res_o);

          opStr="\%";
        end

        ok = (res==act);

        if(VERBOSE | !ok) begin
            if(!ok) tmpstr =  $psprintf("vector: %04d> %d %s %d = %d != %d -> error!", acqCnt, op_a_tmp, opStr, op_b_tmp, res, act);
            else    tmpstr =  $psprintf("vector: %04d> %d %s %d = %d == %d "         , acqCnt, op_a_tmp, opStr, op_b_tmp, res, act);
            $display("TB> %s", tmpstr);
        end

        if(!ok) begin
          failingTests = $psprintf("%sTB> %s\n", failingTests, tmpstr);
        end

        status.addRes(!ok);
        status.print();

        // status
        acqCnt++;
      end
      while (acqCnt < num_stim);
    end
    ///////////////////////////////////////////////

    status.printToFile("summary.rep", 1);

    if(status.totErrCnt == 0) begin
        $display("TB> ----------------------------------------------------------------------");
        $display("TB> PASSED %0d VECTORS", status.totAcqCnt);
        $display("TB> ----------------------------------------------------------------------\n");
    end else begin
        $display("TB> ----------------------------------------------------------------------\n");
        $display("TB> FAILED %0d OF %0d VECTORS\n" , status.totErrCnt, status.totAcqCnt);
        $display("TB> failing tests:");
        $display("TB", failingTests);
        $display("TB> ----------------------------------------------------------------------\n");
    end

    end_of_sim <= 1;
    $finish();
    ///////////////////////////////////////////////
  end

endmodule
