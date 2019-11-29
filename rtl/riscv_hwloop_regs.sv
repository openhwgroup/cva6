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
// Design Name:    hwloop regs                                                //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Hardware loop registers                                    //
//                 a) store start/end address of N=4 hardware loops           //
//                 b) store init value of counter for each hardware loop      //
//                 c) decrement counter if hwloop taken                       //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module riscv_hwloop_regs
#(
  parameter N_REGS     = 2,
  parameter N_REG_BITS = $clog2(N_REGS)
)
(
  input  logic                     clk,
  input  logic                     rst_n,

  // from ex stage
  input  logic           [31:0]    hwlp_start_data_i,
  input  logic           [31:0]    hwlp_end_data_i,
  input  logic           [31:0]    hwlp_cnt_data_i,
  input  logic            [2:0]    hwlp_we_i,
  input  logic [N_REG_BITS-1:0]    hwlp_regid_i,         // selects the register set

  // from controller
  input  logic                     valid_i,

  // from hwloop controller
  input  logic [N_REGS-1:0]        hwlp_dec_cnt_i,

  // to hwloop controller
  output logic [N_REGS-1:0] [31:0] hwlp_start_addr_o,
  output logic [N_REGS-1:0] [31:0] hwlp_end_addr_o,
  output logic [N_REGS-1:0] [31:0] hwlp_counter_o
);


  logic [N_REGS-1:0] [31:0] hwlp_start_q;
  logic [N_REGS-1:0] [31:0] hwlp_end_q;
  logic [N_REGS-1:0] [31:0] hwlp_counter_q, hwlp_counter_n;

  int unsigned i;


  assign hwlp_start_addr_o = hwlp_start_q;
  assign hwlp_end_addr_o   = hwlp_end_q;
  assign hwlp_counter_o    = hwlp_counter_q;


  /////////////////////////////////////////////////////////////////////////////////
  // HWLOOP start-address register                                               //
  /////////////////////////////////////////////////////////////////////////////////
  always_ff @(posedge clk, negedge rst_n)
  begin : HWLOOP_REGS_START
    if (rst_n == 1'b0)
    begin
      hwlp_start_q <= '{default: 32'b0};
    end
    else if (hwlp_we_i[0] == 1'b1)
    begin
      hwlp_start_q[hwlp_regid_i] <= hwlp_start_data_i;
    end
  end


  /////////////////////////////////////////////////////////////////////////////////
  // HWLOOP end-address register                                                 //
  /////////////////////////////////////////////////////////////////////////////////
  always_ff @(posedge clk, negedge rst_n)
  begin : HWLOOP_REGS_END
    if (rst_n == 1'b0)
    begin
      hwlp_end_q <= '{default: 32'b0};
    end
    else if (hwlp_we_i[1] == 1'b1)
    begin
      hwlp_end_q[hwlp_regid_i] <= hwlp_end_data_i;
    end
  end


  /////////////////////////////////////////////////////////////////////////////////
  // HWLOOP counter register with decrement logic                                //
  /////////////////////////////////////////////////////////////////////////////////
  genvar k;
  for (k = 0; k < N_REGS; k++) begin
    assign hwlp_counter_n[k] = hwlp_counter_q[k] - 1;
  end

  always_ff @(posedge clk, negedge rst_n)
  begin : HWLOOP_REGS_COUNTER
    if (rst_n == 1'b0)
    begin
      hwlp_counter_q <= '{default: 32'b0};
    end
    else
    begin
      for (i = 0; i < N_REGS; i++)
      begin
        if ((hwlp_we_i[2] == 1'b1) && (i == hwlp_regid_i)) begin
          hwlp_counter_q[i] <= hwlp_cnt_data_i;
        end else begin
          if (hwlp_dec_cnt_i[i] && valid_i)
            hwlp_counter_q[i] <= hwlp_counter_n[i];
        end
      end
    end
  end

  //----------------------------------------------------------------------------
  // Assertions
  //----------------------------------------------------------------------------
  `ifndef VERILATOR
    // do not decrement more than one counter at once
    assert property (
      @(posedge clk) (valid_i) |-> ($countones(hwlp_dec_cnt_i) <= 1) );
  `endif
endmodule
