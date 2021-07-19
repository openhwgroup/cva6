////////////////////////////////////////////////////////////////////////////////
//
// Copyright 2021 OpenHW Group
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://solderpad.org/licenses/
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
//
////////////////////////////////////////////////////////////////////////////////
//
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
////////////////////////////////////////////////////////////////////////////////
// Description: Synchronous single-port synchronous memory model for the CVA6
//              core testbench. Support byte-wise enables.  Size of memory is
//              $ceil(DATA_WIDTH%64)-by-NUM_WORDS. (which may be overkill)
//              Author: Mike Thompson, OpenHW Group
//
//              Adapted from FPGA wrapper (requires the fpga-support submodule)
//              and "SyncSpRamBeNx64" originally developed for the Ariane
//              testharness by:
//                Florian Zaruba    <zarubaf@iis.ee.ethz.ch>, ETH Zurich
//                Michael Schaffner <schaffner@iis.ee.ethz.ch>, ETH Zurich
//                Date: 15.08.2018
////////////////////////////////////////////////////////////////////////////////

module cva6_core_tb_sram #(
    parameter DATA_WIDTH  = 64,
    parameter NUM_WORDS   = 1024,
    parameter OUT_REGS    = 0    // enables output registers in FPGA macro (read lat = 2)
)(
   input  logic                          clk_i,
   input  logic                          rstn_i,
   input  logic                          req_i,
   input  logic                          we_i,
   input  logic [$clog2(NUM_WORDS)-1:0]  addr_i,
   input  logic [DATA_WIDTH-1:0]         wdata_i,
   input  logic [(DATA_WIDTH+7)/8-1:0]   be_i,
   output logic [DATA_WIDTH-1:0]         rdata_o
);

localparam DATA_WIDTH_ALIGNED = ((DATA_WIDTH+63)/64)*64;
localparam BE_WIDTH_ALIGNED   = (((DATA_WIDTH+7)/8+7)/8)*8;

logic [DATA_WIDTH_ALIGNED-1:0]  wdata_aligned;
logic [BE_WIDTH_ALIGNED-1:0]    be_aligned;
logic [DATA_WIDTH_ALIGNED-1:0]  rdata_aligned;

// align to 64 bits for inferrable macro below
always_comb begin : p_align
    wdata_aligned                    ='0;
    be_aligned                       ='0;
    wdata_aligned[DATA_WIDTH-1:0]    = wdata_i;
    be_aligned[BE_WIDTH_ALIGNED-1:0] = be_i;

    rdata_o = rdata_aligned[DATA_WIDTH-1:0];
end

  for (genvar k = 0; k<(DATA_WIDTH+63)/64; k++) begin : gen_cut
      // unused byte-enable segments (8bits) are culled by the tool
      sync_sram_nx64 #(
        .ADDR_WIDTH($clog2(NUM_WORDS)),
        .DATA_DEPTH(NUM_WORDS),
        .SIM_INIT (4) // 0: no init, 1: zero init, 2: random init, 3: deadbeef init, 4: init from file
      ) i_ram (
          .Clk_CI    ( clk_i                     ),
          .Rst_RBI   ( rstn_i                    ),
          .CSel_SI   ( req_i                     ),
          .WrEn_SI   ( we_i                      ),
          .BEn_SI    ( be_aligned[k*8 +: 8]      ),
          .WrData_DI ( wdata_aligned[k*64 +: 64] ),
          .Addr_DI   ( addr_i                    ),
          .RdData_DO ( rdata_aligned[k*64 +: 64] )
      );
  end
endmodule : cva6_core_tb_sram


////////////////////////////////////////////////////////////////////////////////
// N-word by 64-bit synchronous SRAM model
////////////////////////////////////////////////////////////////////////////////
module sync_sram_nx64
#(
  parameter ADDR_WIDTH = 10,
  parameter DATA_DEPTH = 1024, // usually 2**ADDR_WIDTH, but can be lower
  parameter SIM_INIT   = 0     // for simulation only, will not be synthesized
                               // 0: no init, 1: zero init, 2: random init, 3: deadbeef init, 4: init from file
                               // note: on verilator, 2 is not supported. define the VERILATOR macro to work around.
)(
  input  logic                  Clk_CI,
  input  logic                  Rst_RBI,
  input  logic                  CSel_SI,
  input  logic                  WrEn_SI,
  input  logic [7:0]            BEn_SI,
  input  logic [63:0]           WrData_DI,
  input  logic [ADDR_WIDTH-1:0] Addr_DI,
  output logic [63:0]           RdData_DO
);

  ////////////////////////////
  // signals, localparams
  ////////////////////////////

  localparam DATA_BYTES = 8;

  logic [DATA_BYTES*8-1:0] RdData_DN;
  logic [DATA_BYTES*8-1:0] RdData_DP;

  logic [DATA_BYTES*8-1:0] Mem_DP[DATA_DEPTH-1:0];
  logic [7:0] Mem_init[0:'hFFFFFF];

  initial begin
    for(int k=0; k<'hFFFFFF;k++) Mem_init[k] = 'h0;
    $readmemh("./Mem_init.txt", Mem_init);
  end

  assign RdData_DO = RdData_DP;
  assign RdData_DP = RdData_DN;

  always_ff @(posedge Clk_CI) begin
    automatic logic [63:0] val;
    if(Rst_RBI == 1'b0 && SIM_INIT>0) begin
      for(int k=0; k<DATA_DEPTH;k++) begin
        // 0: no init, 1: zero init, 2: random init, 3: deadbeef init, 4: init from file
        if(SIM_INIT==1) val = '0;
    `ifndef VERILATOR
        else if(SIM_INIT==2) void'(randomize(val));
    `endif
        else if(SIM_INIT==3) val = 64'hdeadbeefdeadbeef;
        else val = {Mem_init[8*k+7], Mem_init[8*k+6],
                    Mem_init[8*k+5], Mem_init[8*k+4],
                    Mem_init[8*k+3], Mem_init[8*k+2],
                    Mem_init[8*k+1], Mem_init[8*k+0]};
        Mem_DP[k] = val;
        //$write("%m @ %0t: Mem_DP[%0d] = %h\n", $time, k, val);
      end
    end
    else begin
      if(CSel_SI) begin
        if(WrEn_SI) begin
          if(BEn_SI[0]) Mem_DP[Addr_DI][ 7: 0] <= WrData_DI[ 7: 0];
          if(BEn_SI[1]) Mem_DP[Addr_DI][15: 8] <= WrData_DI[15: 8];
          if(BEn_SI[2]) Mem_DP[Addr_DI][23:16] <= WrData_DI[23:16];
          if(BEn_SI[3]) Mem_DP[Addr_DI][31:24] <= WrData_DI[31:24];
          if(BEn_SI[4]) Mem_DP[Addr_DI][39:32] <= WrData_DI[39:32];
          if(BEn_SI[5]) Mem_DP[Addr_DI][47:40] <= WrData_DI[47:40];
          if(BEn_SI[6]) Mem_DP[Addr_DI][55:48] <= WrData_DI[55:48];
          if(BEn_SI[7]) Mem_DP[Addr_DI][63:56] <= WrData_DI[63:56];
        end
        RdData_DN <= Mem_DP[Addr_DI];
      end
    end
  end

  ////////////////////////////
  // assertions
  ////////////////////////////

  assert property
    (@(posedge Clk_CI) (longint'(2)**longint'(ADDR_WIDTH) >= longint'(DATA_DEPTH)))
    else $error("depth out of bounds");

endmodule : sync_sram_nx64
