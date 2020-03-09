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
 * Inferable, Synchronous Dual-Port RAM
 *
 * This module is designed to work with both Xilinx and Altera tools by following the respective
 * guidelines:
 * - Xilinx UG901 Vivado Design Suite User Guide: Synthesis (p. 106)
 * - Altera Quartus II Handbook Volume 1: Design and Synthesis (p. 768)
 *
 * Current Maintainers:
 * - Michael Schaffner  <schaffer@iis.ee.ethz.ch>
 */

// this automatically switches the behavioral description
// pragma translate_off
`define SIMULATION
// pragma translate_on

module SyncDpRam
#(
  parameter ADDR_WIDTH = 10,
  parameter DATA_DEPTH = 1024, // usually 2**ADDR_WIDTH, but can be lower
  parameter DATA_WIDTH = 32,
  parameter OUT_REGS   = 0,
  parameter SIM_INIT   = 0     // for simulation only, will not be synthesized
                               // 0: no init, 1: zero init, 2: random init
                               // note: on verilator, 2 is not supported. define the VERILATOR macro to work around.
)(
  input  logic                  Clk_CI,
  input  logic                  Rst_RBI,
  // port A
  input  logic                  CSelA_SI,
  input  logic                  WrEnA_SI,
  input  logic [DATA_WIDTH-1:0] WrDataA_DI,
  input  logic [ADDR_WIDTH-1:0] AddrA_DI,
  output logic [DATA_WIDTH-1:0] RdDataA_DO,
  // port B
  input  logic                  CSelB_SI,
  input  logic                  WrEnB_SI,
  input  logic [DATA_WIDTH-1:0] WrDataB_DI,
  input  logic [ADDR_WIDTH-1:0] AddrB_DI,
  output logic [DATA_WIDTH-1:0] RdDataB_DO
);

  ////////////////////////////
  // signals, localparams
  ////////////////////////////

  logic [DATA_WIDTH-1:0] RdDataA_DN;
  logic [DATA_WIDTH-1:0] RdDataA_DP;
  logic [DATA_WIDTH-1:0] RdDataB_DN;
  logic [DATA_WIDTH-1:0] RdDataB_DP;
  logic [DATA_WIDTH-1:0] Mem_DP [DATA_DEPTH-1:0];

  ////////////////////////////
  // XILINX/ALTERA implementation
  ////////////////////////////

  `ifdef SIMULATION
    always_ff @(posedge Clk_CI)
    begin
      automatic logic [DATA_WIDTH-1:0] val;
      if(Rst_RBI == 1'b0 && SIM_INIT>0) begin
        for(int k=0; k<DATA_DEPTH;k++) begin
          if(SIM_INIT==1) val = '0;
          `ifndef VERILATOR
          else if(SIM_INIT==2) void'(randomize(val));
          `endif
          Mem_DP[k] = val;
        end
      end else begin
        if (CSelA_SI) begin
          if (WrEnA_SI) begin
            Mem_DP[AddrA_DI] <= WrDataA_DI;
          end
          else
          begin
            RdDataA_DN <= Mem_DP[AddrA_DI];
          end
        end

        if (CSelB_SI) begin
          if (WrEnB_SI) begin
            Mem_DP[AddrB_DI] <= WrDataB_DI;
          end
          else
          begin
            RdDataB_DN <= Mem_DP[AddrB_DI];
          end
        end
      end
    end
  `endif

  ////////////////////////////
  // XILINX/ALTERA implementation
  ////////////////////////////

  `ifndef SIMULATION
    always_ff @(posedge Clk_CI)
    begin
      if (CSelA_SI) begin
        if (WrEnA_SI) begin
          Mem_DP[AddrA_DI] <= WrDataA_DI;
        end
        else
        begin
          RdDataA_DN <= Mem_DP[AddrA_DI];
        end
      end
    end

    always_ff @(posedge Clk_CI)
    begin
      if (CSelB_SI) begin
        if (WrEnB_SI) begin
          Mem_DP[AddrB_DI] <= WrDataB_DI;
        end
        else
        begin
          RdDataB_DN <= Mem_DP[AddrB_DI];
        end
      end
    end
  `endif

  ////////////////////////////
  // optional output regs
  ////////////////////////////

  // output regs
  generate
    if (OUT_REGS>0) begin : g_outreg
      always_ff @(posedge Clk_CI or negedge Rst_RBI) begin
        if(Rst_RBI == 1'b0)
        begin
          RdDataA_DP  <= 0;
          RdDataB_DP  <= 0;
        end
        else
        begin
          RdDataA_DP  <= RdDataA_DN;
          RdDataB_DP  <= RdDataB_DN;
        end
      end
    end
  endgenerate // g_outreg

  // output reg bypass
  generate
    if (OUT_REGS==0) begin : g_oureg_byp
      assign RdDataA_DP  = RdDataA_DN;
      assign RdDataB_DP  = RdDataB_DN;
    end
  endgenerate// g_oureg_byp

  assign RdDataA_DO = RdDataA_DP;
  assign RdDataB_DO = RdDataB_DP;

  ////////////////////////////
  // assertions
  ////////////////////////////

  // pragma translate_off
  assert property
    (@(posedge Clk_CI) (longint'(2)**longint'(ADDR_WIDTH) >= longint'(DATA_DEPTH)))
    else $error("depth out of bounds");
  assert property
    (@(posedge Clk_CI) (CSelA_SI & CSelB_SI & WrEnA_SI & WrEnB_SI) |-> (AddrA_DI != AddrB_DI))
    else $error("A and B write to the same address");
  // pragma translate_on

endmodule // SyncDpRam
