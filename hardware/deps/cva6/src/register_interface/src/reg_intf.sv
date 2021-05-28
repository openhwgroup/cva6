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
// Fabian Schuiki <fschuiki@iis.ee.ethz.ch>

/// A simple register interface.
///
/// This is pretty much as simple as it gets. Transactions consist of only one
/// phase. The master sets the address, write, write data, and write strobe
/// signals and pulls valid high. Once pulled high, valid must remain high and
/// none of the signals may change. The transaction completes when both valid
/// and ready are high. Valid must not depend on ready. The slave presents the
/// read data and error signals. These signals must be constant while valid and
/// ready are both high.
interface REG_BUS #(
  /// The width of the address.
  parameter int ADDR_WIDTH = -1,
  /// The width of the data.
  parameter int DATA_WIDTH = -1
)(
  input logic clk_i
);

  logic [ADDR_WIDTH-1:0]   addr;
  logic                    write; // 0=read, 1=write
  logic [DATA_WIDTH-1:0]   rdata;
  logic [DATA_WIDTH-1:0]   wdata;
  logic [DATA_WIDTH/8-1:0] wstrb; // byte-wise strobe
  logic                    error; // 0=ok, 1=error
  logic                    valid;
  logic                    ready;

  modport in  (input  addr, write, wdata, wstrb, valid, output rdata, error, ready);
  modport out (output addr, write, wdata, wstrb, valid, input  rdata, error, ready);

endinterface
