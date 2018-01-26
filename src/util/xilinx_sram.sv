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
// Author: Florian Zaruba, ETH Zurich
// Date: 13.11.2017
// Description: SRAM Model for Xilinx FPGA

module sram #(
    int unsigned DATA_WIDTH = 64,
    int unsigned NUM_WORDS  = 1024
)(
   input  logic                          clk_i,

   input  logic                          req_i,
   input  logic                          we_i,
   input  logic [$clog2(NUM_WORDS)-1:0]  addr_i,
   input  logic [DATA_WIDTH-1:0]         wdata_i,
   input  logic [DATA_WIDTH-1:0]         be_i,
   output logic [DATA_WIDTH-1:0]         rdata_o
);

    generate
        if (NUM_WORDS == 256) begin

            // Dirty RAM
            if (DATA_WIDTH == 16) begin

                localparam NUM_WORDS = 2**8;

                logic [NUM_WORDS-1:0][15:0] mem;

                always_ff @(posedge clk_i) begin
                    // write
                    if (req_i && we_i) begin
                        for (int unsigned i = 0; i < 16; i++) begin
                            if (be_i[i])
                                mem[addr_i][i] <= wdata_i[i];
                        end
                    // read
                    end else if (req_i) begin
                        rdata_o <= mem[addr_i];
                    end
                end
            end

            // Data RAM
            if (DATA_WIDTH == 44) begin
                logic [47:0] data_o;
                assign rdata_o = data_o[43:0];

                // this is actually 48 bits wide
                xilinx_dcache_bank_tag_256x46 TAG_RAM (
                    .clka  ( clk_i           ),
                    .ena   ( req_i           ),
                    .wea   ( {{be_i[40] & we_i}, {be_i[32] & we_i}, {be_i[24] & we_i}, {be_i[16] & we_i}, {be_i[8] & we_i}, {be_i[0] & we_i}} ),
                    .addra ( addr_i          ),
                    .dina  ( {4'b0, wdata_i} ),
                    .douta ( data_o          )
                );
            end

            // Data RAM
            if (DATA_WIDTH == 128) begin
                xilinx_dcache_bank_data_256x128 DATA_RAM (
                    .clka       ( clk_i   ),
                    .ena        ( req_i   ),
                    .wea        ( {{be_i[15] & we_i}, {be_i[14] & we_i}, {be_i[13] & we_i}, {be_i[12] & we_i}, {be_i[11] & we_i}, {be_i[10] & we_i}, {be_i[9] & we_i}, {be_i[8] & we_i}, {be_i[7] & we_i}, {be_i[6] & we_i}, {be_i[5] & we_i}, {be_i[4] & we_i}, {be_i[3] & we_i}, {be_i[2] & we_i}, {be_i[1] & we_i}, {be_i[0] & we_i}}),
                    .addra      ( addr_i  ),
                    .dina       ( wdata_i ),
                    .douta      ( rdata_o )
                );
            end
        end
    endgenerate

endmodule
