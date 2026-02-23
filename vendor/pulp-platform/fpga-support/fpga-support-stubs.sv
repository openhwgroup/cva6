// Copyright 2024 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

module SyncDpRam
#(
  parameter ADDR_WIDTH = 10,
  parameter DATA_DEPTH = 1024,
  parameter DATA_WIDTH = 32,
  parameter OUT_REGS   = 0,
  parameter SIM_INIT   = 0
)(
  input  logic                  Clk_CI,
  input  logic                  Rst_RBI,
  input  logic                  CSelA_SI,
  input  logic                  WrEnA_SI,
  input  logic [DATA_WIDTH-1:0] WrDataA_DI,
  input  logic [ADDR_WIDTH-1:0] AddrA_DI,
  output logic [DATA_WIDTH-1:0] RdDataA_DO,
  input  logic                  CSelB_SI,
  input  logic                  WrEnB_SI,
  input  logic [DATA_WIDTH-1:0] WrDataB_DI,
  input  logic [ADDR_WIDTH-1:0] AddrB_DI,
  output logic [DATA_WIDTH-1:0] RdDataB_DO
);

  if (1) begin : assert_instantiation
    $fatal( 1, "Instantiated FPGA-specific cell; this is illegal in PULP CVA6 (%m)");
  end

endmodule


module AsyncDpRam
#(
  parameter ADDR_WIDTH = 10,
  parameter DATA_DEPTH = 1024, // usually 2**ADDR_WIDTH, but can be lower
  parameter DATA_WIDTH = 32
)(
  input  logic                    Clk_CI,
  input  logic                    WrEn_SI,
  input  logic [ADDR_WIDTH-1:0]   WrAddr_DI,
  input  logic [DATA_WIDTH-1:0]   WrData_DI,
  input  logic [ADDR_WIDTH-1:0]   RdAddr_DI,
  output logic [DATA_WIDTH-1:0]   RdData_DO
);

  if (1) begin : assert_instantiation
    $fatal( 1, "Instantiated FPGA-specific cell; this is illegal in PULP CVA6 (%m)");
  end

endmodule


module AsyncThreePortRam
#(
  parameter ADDR_WIDTH = 10,
  parameter DATA_DEPTH = 1024,
  parameter DATA_WIDTH = 32
)(
  input  logic                    Clk_CI,
  input  logic                    WrEn_SI,
  input  logic [ADDR_WIDTH-1:0]   WrAddr_DI,
  input  logic [DATA_WIDTH-1:0]   WrData_DI,
  input  logic [ADDR_WIDTH-1:0]   RdAddr_DI_0,
  input  logic [ADDR_WIDTH-1:0]   RdAddr_DI_1,
  output logic [DATA_WIDTH-1:0]   RdData_DO_0,
  output logic [DATA_WIDTH-1:0]   RdData_DO_1
);

  if (1) begin : assert_instantiation
    $fatal( 1, "Instantiated FPGA-specific cell; this is illegal in PULP CVA6 (%m)");
  end

endmodule
