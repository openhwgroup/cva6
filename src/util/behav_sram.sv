// Copyright 2017, 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the “License”); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an “AS IS” BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Date: 13.10.2017
// Description: SRAM Behavioral Model
//

module sram #(
    int unsigned DATA_WIDTH = 64,
    int unsigned NUM_WORDS  = 1024
)(
    // Clock and Reset
    input  logic                          clk_i,

    input  logic                          req_i,
    input  logic [$clog2(NUM_WORDS)-1:0]  addr_i,
    input  logic [DATA_WIDTH-1:0]         wdata_i,
    output logic [DATA_WIDTH-1:0]         rdata_o,
    input  logic                          we_i,
    input  logic [DATA_WIDTH-1:0]         be_i
  );

    localparam words = NUM_WORDS/(DATA_WIDTH/8);

    localparam ADDR_WIDTH = $clog2(NUM_WORDS);

    logic [DATA_WIDTH-1:0] mem[words];
    logic [DATA_WIDTH-1:0] wdata;
    logic [ADDR_WIDTH-1-$clog2(DATA_WIDTH/8):0] addr;

    integer i;

    assign addr = addr_i[ADDR_WIDTH-1:$clog2(DATA_WIDTH/8)];

    always @(posedge clk_i) begin
        if (req_i && we_i) begin
            for (i = 0; i < DATA_WIDTH; i++) begin
                if (be_i[i])
                  mem[addr][i] <= wdata[i];
            end
        end

        rdata_o <= mem[addr];
    end

    assign wdata = wdata_i;

endmodule
