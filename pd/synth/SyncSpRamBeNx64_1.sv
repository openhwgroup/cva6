// Copyright 2014 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

/**
 * Inferable, Synchronous Single-Port N x 64bit RAM with Byte-Wise Enable
 *
 * This module contains an implementation for either Xilinx or Altera FPGAs.  To synthesize for
 * Xilinx, define `FPGA_TARGET_XILINX`.  To synthesize for Altera, define `FPGA_TARGET_ALTERA`.  The
 * implementations follow the respective guidelines:
 * - Xilinx UG901 Vivado Design Suite User Guide: Synthesis (p. 106)
 * - Altera Quartus II Handbook Volume 1: Design and Synthesis (p. 768)
 *
 * Current Maintainers:
 * - Michael Schaffner  <schaffer@iis.ee.ethz.ch>
 */

`ifndef FPGA_TARGET_ALTERA
  `define FPGA_TARGET_XILINX
`endif

module SyncSpRamBeNx64_1
#(
  parameter ADDR_WIDTH = 10,
  parameter DATA_DEPTH = 1024, // usually 2**ADDR_WIDTH, but can be lower
  parameter OUT_REGS   = 0,    // set to 1 to enable outregs
  parameter SIM_INIT   = 0     // for simulation only, will not be synthesized
                               // 0: no init, 1: zero init, 2: random init, 3: deadbeef init
                               // note: on verilator, 2 is not supported. define the VERILATOR macro to work around.
)(
  input  logic                  clk_ci,
  input  logic                  rst_rbi,
  input  logic                  csel_si,
  input  logic                  wren_si,
  input  logic [7:0]            ben_si,
  input  logic [63:0]           wrdata_di,
  input  logic [ADDR_WIDTH-1:0] addr_di,
  output logic [63:0]           rddata_do
);

// synthesis translate_off

  ////////////////////////////
  // signals, localparams
  ////////////////////////////

  // needs to be consistent with the Altera implemenation below
  localparam DATA_BYTES = 8;

  logic [DATA_BYTES*8-1:0] RdData_DN;
  logic [DATA_BYTES*8-1:0] RdData_DP;

  ////////////////////////////
  // XILINX implementation
  ////////////////////////////

  `ifdef FPGA_TARGET_XILINX
    logic [DATA_BYTES*8-1:0] Mem_DP[DATA_DEPTH-1:0];

    always_ff @(posedge clk_ci) begin
      //pragma translate_off
      automatic logic [63:0] val;
      if(rst_rbi == 1'b0 && SIM_INIT>0) begin
        for(int k=0; k<DATA_DEPTH;k++) begin
          if(SIM_INIT==1) val = '0;
      `ifndef VERILATOR
          else if(SIM_INIT==2) void'(randomize(val));
      `endif
          else val = 64'hdeadbeefdeadbeef;
          Mem_DP[k] = val;
        end
      end else
      //pragma translate_on
      if(csel_si) begin
        if(wren_si) begin
          if(ben_si[0]) Mem_DP[addr_di][7:0]   <= wrdata_di[7:0];
          if(ben_si[1]) Mem_DP[addr_di][15:8]  <= wrdata_di[15:8];
          if(ben_si[2]) Mem_DP[addr_di][23:16] <= wrdata_di[23:16];
          if(ben_si[3]) Mem_DP[addr_di][31:24] <= wrdata_di[31:24];
          if(ben_si[4]) Mem_DP[addr_di][39:32] <= wrdata_di[39:32];
          if(ben_si[5]) Mem_DP[addr_di][47:40] <= wrdata_di[47:40];
          if(ben_si[6]) Mem_DP[addr_di][55:48] <= wrdata_di[55:48];
          if(ben_si[7]) Mem_DP[addr_di][63:56] <= wrdata_di[63:56];
        end
        RdData_DN <= Mem_DP[addr_di];
      end
    end
  `endif

  ////////////////////////////
  // ALTERA implementation
  ////////////////////////////

  `ifdef FPGA_TARGET_ALTERA
    logic [DATA_BYTES-1:0][7:0] Mem_DP[0:DATA_DEPTH-1];

    always_ff @(posedge clk_ci) begin
      //pragma translate_off
      automatic logic [63:0] val;
      if(rst_rbi == 1'b0 && SIM_INIT>0) begin
        for(int k=0; k<DATA_DEPTH;k++) begin
          if(SIM_INIT==1) val = '0;
      `ifndef VERILATOR
          else if(SIM_INIT==2) void'(randomize(val));
      `endif
          else val = 64'hdeadbeefdeadbeef;
          Mem_DP[k] = val;
        end
      end else
      //pragma translate_on
      if(csel_si) begin
        if(wren_si) begin // needs to be static, otherwise Altera wont infer it
          if(ben_si[0]) Mem_DP[addr_di][0] <= wrdata_di[7:0];
          if(ben_si[1]) Mem_DP[addr_di][1] <= wrdata_di[15:8];
          if(ben_si[2]) Mem_DP[addr_di][2] <= wrdata_di[23:16];
          if(ben_si[3]) Mem_DP[addr_di][3] <= wrdata_di[31:24];
          if(ben_si[4]) Mem_DP[addr_di][4] <= wrdata_di[39:32];
          if(ben_si[5]) Mem_DP[addr_di][5] <= wrdata_di[47:40];
          if(ben_si[6]) Mem_DP[addr_di][6] <= wrdata_di[55:48];
          if(ben_si[7]) Mem_DP[addr_di][7] <= wrdata_di[63:56];
        end
        RdData_DN <= Mem_DP[addr_di];
      end
    end
  `endif

  ////////////////////////////
  // optional output regs
  ////////////////////////////

  // output regs
  generate
    if (OUT_REGS>0) begin : g_outreg
      always_ff @(posedge clk_ci or negedge rst_rbi) begin
        if(rst_rbi == 1'b0)
        begin
          RdData_DP  <= 0;
        end
        else
        begin
          RdData_DP  <= RdData_DN;
        end
      end
    end
  endgenerate // g_outreg

  // output reg bypass
  generate
    if (OUT_REGS==0) begin : g_oureg_byp
      assign RdData_DP  = RdData_DN;
    end
  endgenerate// g_oureg_byp

  assign rddata_do = RdData_DP;

  ////////////////////////////
  // assertions
  ////////////////////////////

  // pragma translate_off
  assert property
    (@(posedge clk_ci) (longint'(2)**longint'(ADDR_WIDTH) >= longint'(DATA_DEPTH)))
    else $error("depth out of bounds");
  // pragma translate_on

  `ifndef FPGA_TARGET_XILINX
    `ifndef FPGA_TARGET_ALTERA
      $error("FPGA target not defined, define  FPGA_TARGET_XILINX or FPGA_TARGET_ALTERA.");
    `endif
  `endif

// synthesis translate_on

endmodule // SyncSpRamBeNx64
