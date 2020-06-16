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
 * This is the copied and modified version of Inferable, Synchronous Single
 * -Port N x 64bit RAM with Byte-Wise Enable to support dromajo cosimulation
 * 
 * Current Maintainers:
 * - Nursultan Kabylkas
 */

module dromajo_ram
#(
  parameter ADDR_WIDTH = 10,
  parameter DATA_DEPTH = 1024, // usually 2**ADDR_WIDTH, but can be lower
  parameter OUT_REGS   = 0     // set to 1 to enable outregs
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

  // needs to be consistent with the Altera implemenation below
  localparam DATA_BYTES = 8;

  logic [DATA_BYTES*8-1:0] RdData_DN;
  logic [DATA_BYTES*8-1:0] RdData_DP;

  logic [DATA_BYTES*8-1:0] Mem_DP[DATA_DEPTH-1:0];

  ////////////////////////////
  // DROMAJO COSIM OPTION
  // sync rams
  ////////////////////////////\
  initial begin
    integer hex_file, num_bytes;
    longint address, value;
    string f_name;
    // init to 0
    for (int k=0; k<DATA_DEPTH; k++) begin
      Mem_DP[k] = 0;
    end

    // sync with dromajo
    if ($value$plusargs("checkpoint=%s", f_name)) begin
      hex_file = $fopen({f_name,".mainram.hex"}, "r");
      while (!$feof(hex_file)) begin
        num_bytes = $fscanf(hex_file, "%d %h\n", address, value);
        //$display("%d %h", address, value);
        Mem_DP[address] = value;
      end
      $display("Done syncing RAM with dromajo...\n");
    end else begin
      $display("Failed syncing RAM: provide path to a checkpoint.\n");
    end
  end

  always_ff @(posedge Clk_CI) begin
    if(CSel_SI) begin
      if(WrEn_SI) begin
        if(BEn_SI[0]) Mem_DP[Addr_DI][7:0]   <= WrData_DI[7:0];
        if(BEn_SI[1]) Mem_DP[Addr_DI][15:8]  <= WrData_DI[15:8];
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

  ////////////////////////////
  // optional output regs
  ////////////////////////////

  // output regs
  generate
    if (OUT_REGS>0) begin : g_outreg
      always_ff @(posedge Clk_CI or negedge Rst_RBI) begin
        if(Rst_RBI == 1'b0)
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

  assign RdData_DO = RdData_DP;

  ////////////////////////////
  // assertions
  ////////////////////////////

  // pragma translate_off
  assert property
    (@(posedge Clk_CI) (longint'(2)**longint'(ADDR_WIDTH) >= longint'(DATA_DEPTH)))
    else $error("depth out of bounds");
  // pragma translate_on

endmodule //dromajo_ram
