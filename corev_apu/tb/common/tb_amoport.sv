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
// Author: Michael Schaffner <schaffner@iis.ee.ethz.ch>, ETH Zurich
//         Nils Wistoff <nwistoff@iis.ee.ethz.ch>, ETH Zurich
// Date: 25.08.2020
// Description: program that emulates an atomic memory operation (AMO) agent.
//

`include "tb.svh"

program tb_amoport import ariane_pkg::*; import tb_pkg::*; #(
  parameter string       PortName      = "atomics port 0",
  parameter              MemWords      = 1024*1024,// in 64bit words
  parameter logic [63:0] CachedAddrBeg = 0,
  parameter logic [63:0] CachedAddrEnd = 0,
  parameter              RndSeed       = 1110,
  parameter              Verbose       = 0
) (
  input logic           clk_i,
  input logic           rst_ni,

  // to testbench master
  ref    string         test_name_i,
  input  logic          seq_run_i,
  input  logic [31:0]   seq_num_amo_i,
  input  logic          seq_last_i,
  output logic          seq_done_o,

  // expresp interface
  input logic [63:0]    act_mem_i,
  input logic [63:0]    exp_mem_i,
  input logic [63:0]    exp_result_i,

  // interface to DUT
  output amo_req_t  dut_amo_req_port_o,
  input  amo_resp_t dut_amo_resp_port_i
  );

  // leave this
  timeunit 1ps;
  timeprecision 1ps;

  logic seq_end_req, seq_end_ack, prog_end;

///////////////////////////////////////////////////////////////////////////////
// Helper tasks
///////////////////////////////////////////////////////////////////////////////

  task automatic applyAtomics();
    automatic logic [63:0] paddr;
    automatic logic [63:0] data;
    automatic logic [1:0]  size;
    automatic amo_t amo_op;
    automatic logic [63:0] delay;

    void'($urandom(RndSeed));

    paddr = 0;
    dut_amo_req_port_o.req       = '0;
    dut_amo_req_port_o.amo_op    = AMO_NONE;
    dut_amo_req_port_o.size      = '0;
    dut_amo_req_port_o.operand_a = 'x;
    dut_amo_req_port_o.operand_b = 'x;

    repeat (seq_num_amo_i) begin
      dut_amo_req_port_o.req       = '0;
      dut_amo_req_port_o.operand_a = 'x;
      dut_amo_req_port_o.operand_b = 'x;

      // Add random delay
      void'(randomize(delay) with {delay >= 0; delay < 32;});
      `APPL_WAIT_CYC(clk_i, delay)

      // Apply random stimuli, choose random AMO operand
      void'(randomize(amo_op) with {!(amo_op inside {AMO_NONE, AMO_CAS1, AMO_CAS2});});
      void'(randomize(data));
      if (riscv::XLEN == 64)
        void'(randomize(size) with {size >= 2; size <= 3;});
      else
        size = 'h2;

      // For LRs/SCs, choose from only 4 adresses,
      // so that valid LR/SC combinations become more likely.
      // Note: AMOs to address 0 are not supported in axi_riscv_atomics module
      //       so we start at 8 (for alignment purposes)
      if (amo_op inside {AMO_LR, AMO_SC})
        void'(randomize(paddr) with {paddr >= 8; paddr < 12;});
      else
        void'(randomize(paddr) with {paddr >= 8; paddr < (MemWords<<3);});

      // Align adress
      if (size == 2)
        paddr[1:0] = '0;
      else
        paddr[2:0] = '0;

      // Apply stimuli
      dut_amo_req_port_o.req       = '1;
      dut_amo_req_port_o.amo_op    = amo_op;
      dut_amo_req_port_o.size      = size;
      dut_amo_req_port_o.operand_a = paddr;
      dut_amo_req_port_o.operand_b = data;

      // wait for ack
      `APPL_WAIT_COMB_SIG(clk_i, dut_amo_resp_port_i.ack)
      `APPL_WAIT_CYC(clk_i, 1)
    end

    dut_amo_req_port_o.req       = '0;
    dut_amo_req_port_o.amo_op    = AMO_NONE;
    dut_amo_req_port_o.size      = '0;
    dut_amo_req_port_o.operand_a = 'x;
    dut_amo_req_port_o.operand_b = 'x;
  endtask : applyAtomics

///////////////////////////////////////////////////////////////////////////////
// Sequence application
///////////////////////////////////////////////////////////////////////////////

  initial begin : p_stim
    dut_amo_req_port_o.req       = '0;
    dut_amo_req_port_o.amo_op    = AMO_NONE;
    dut_amo_req_port_o.size      = '0;
    dut_amo_req_port_o.operand_a = 'x;
    dut_amo_req_port_o.operand_b = 'x;

    seq_done_o                   = 1'b0;

    // print some info
    $display("%s> current configuration:",  PortName);
    $display("%s> RndSeed           %d",   PortName, RndSeed);

    `APPL_WAIT_CYC(clk_i,1)
    `APPL_WAIT_SIG(clk_i,~rst_ni)

    $display("%s> starting application", PortName);
    while(~seq_last_i) begin
      `APPL_WAIT_SIG(clk_i,seq_run_i)
      seq_done_o = 1'b0;
      $display("%s> start random AMOs with %04d vectors", PortName, seq_num_amo_i);
      applyAtomics();
      seq_done_o = 1'b1;
      $display("%s> stop sequence", PortName);
      `APPL_WAIT_CYC(clk_i,1)
    end
    $display("%s> ending application", PortName);
  end

///////////////////////////////////////////////////////////////////////////////
// Response acquisition
///////////////////////////////////////////////////////////////////////////////

  initial begin : p_acq
    bit ok;
    progress status;
    string failingTests, tmpstr0, tmpstr1, tmpstr2;
    int    n;
    logic [63:0] exp_res;

    status       = new(PortName);
    failingTests = "";
    seq_done_o   = 1'b0;
    seq_end_req  = 1'b0;
    prog_end     = 1'b0;

    `ACQ_WAIT_CYC(clk_i,1)
    `ACQ_WAIT_SIG(clk_i,~rst_ni)

    ///////////////////////////////////////////////
    // loop over tests
    n=0;
    while(~seq_last_i) begin
      `ACQ_WAIT_SIG(clk_i,seq_run_i)
      seq_done_o = 1'b0;

      $display("%s> %s", PortName, test_name_i);
      status.reset(seq_num_amo_i);
      for (int k=0;k<seq_num_amo_i;k++) begin
        `ACQ_WAIT_SIG(clk_i, dut_amo_resp_port_i.ack)

        // Assert expected data is not 'x, protects against ineffective ==? comparisons
        assert(exp_result_i !== 'x) else $error("Expected result is unknown");
        // note: wildcard as defined in right operand!
        ok=(dut_amo_resp_port_i.result ==? exp_result_i) && (act_mem_i == exp_mem_i);

        if(Verbose | !ok) begin
          tmpstr0 =  $psprintf("vector: %02d - %06d -- paddr:   %16X -- AMO: 0x%2X -- size: %X  -- op_a: %16X -- op_b: %16X",
                      n, k, dut_amo_req_port_o.operand_a, dut_amo_req_port_o.amo_op, 2**dut_amo_req_port_o.size, dut_amo_req_port_o.operand_a, dut_amo_req_port_o.operand_b);
          tmpstr1 =  $psprintf("vector: %02d - %06d -- exp_res: %16X -- exp_mem: %16X",
                      n, k, exp_result_i, exp_mem_i);
          tmpstr2 =  $psprintf("vector: %02d - %06d -- result:  %16X -- memory: %16X",
                      n, k, dut_amo_resp_port_i.result, act_mem_i);
          $display("%s> %s", PortName, tmpstr0);
          $display("%s> %s", PortName, tmpstr1);
          $display("%s> %s", PortName, tmpstr2);
        end

        if(!ok) begin
          failingTests = $psprintf("%s%s> %s\n%s> %s\n", failingTests, PortName, tmpstr1, PortName, tmpstr2);
        end
        status.addRes(!ok);
        status.print();
      end
      seq_end_req = 1'b1;
      `ACQ_WAIT_SIG(clk_i, seq_end_ack)
      seq_end_req = 1'b0;

      `ACQ_WAIT_CYC(clk_i,1)
      seq_done_o = 1'b1;
      n++;
    end

    status.printToFile({PortName, "_summary.rep"}, 1);

    if(status.totErrCnt == 0) begin
      $display("%s> ----------------------------------------------------------------------", PortName);
      $display("%s> PASSED %0d VECTORS", PortName, status.totAcqCnt);
      $display("%s> ----------------------------------------------------------------------\n", PortName);
    end else begin
      $display("%s> ----------------------------------------------------------------------\n", PortName);
      $display("%s> FAILED %0d OF %0d VECTORS\n", PortName , status.totErrCnt, status.totAcqCnt);
      $display("%s> failing tests:", PortName);
      $display("%s", failingTests);
      $display("%s> ----------------------------------------------------------------------\n", PortName);
    end
    prog_end = 1'b1;

  end
    ///////////////////////////////////////////////

endprogram // tb_amoport
