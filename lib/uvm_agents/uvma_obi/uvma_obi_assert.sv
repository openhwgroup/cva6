// Copyright 2020 OpenHW Group
// Copyright 2020 Datum Technology Corporation
// Copyright 2020 Silicon Labs, Inc.
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

module uvma_obi_assert
  #(
    parameter int ADDR_WIDTH=32,
    parameter int DATA_WIDTH=32
  )
  (
    input                    clk,
    input                    reset_n,

    input                    req,
    input                    gnt,
    input [ADDR_WIDTH-1:0]   addr,
    input                    we,
    input [DATA_WIDTH/8-1:0] be,
    input [DATA_WIDTH-1:0]   wdata,
    input [DATA_WIDTH-1:0]   rdata,
    input                    rvalid,
    input                    rready
  );

  // Sunil: Insert assertions here

endmodule : uvma_obi_assert
