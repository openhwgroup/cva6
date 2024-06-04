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
// Author: Florian Zaruba    <zarubaf@iis.ee.ethz.ch>, ETH Zurich
//         Michael Schaffner <schaffner@iis.ee.ethz.ch>, ETH Zurich
// Date: 15.08.2018
// Description: SRAM wrapper for FPGA (requires the fpga-support submodule)
//
// Note: the wrapped module contains two different implementations for
// ALTERA and XILINX tools, since these follow different coding styles for
// inferrable RAMS with byte enable. define `FPGA_TARGET_XILINX or
// `FPGA_TARGET_ALTERA in your build environment (default is ALTERA)

module sram_cache #(
    parameter DATA_WIDTH = 64,
    parameter USER_WIDTH = 1,
    parameter USER_EN    = 0,
    parameter NUM_WORDS  = 1024,
    parameter SIM_INIT   = "none",
    parameter BYTE_ACCESS = 1,
    parameter TECHNO_CUT = 0,
    parameter OUT_REGS   = 0     // enables output registers in FPGA macro (read lat = 2)
)(
   input  logic                          clk_i,
   input  logic                          rst_ni,
   input  logic                          req_i,
   input  logic                          we_i,
   input  logic [$clog2(NUM_WORDS)-1:0]  addr_i,
   input  logic [USER_WIDTH-1:0]         wuser_i,
   input  logic [DATA_WIDTH-1:0]         wdata_i,
   input  logic [(DATA_WIDTH+7)/8-1:0]   be_i,
   output logic [USER_WIDTH-1:0]         ruser_o,
   output logic [DATA_WIDTH-1:0]         rdata_o
);
  localparam DATA_AND_USER_WIDTH = USER_EN ? DATA_WIDTH + USER_WIDTH : DATA_WIDTH;
  if (TECHNO_CUT) begin : gen_techno_cut
    if (USER_EN > 0) begin
      logic [DATA_WIDTH + USER_WIDTH-1:0] wdata_user;
      logic [DATA_WIDTH + USER_WIDTH-1:0] rdata_user;
      logic [(DATA_WIDTH+7)/8+(DATA_WIDTH+7)/8-1:0] be;

      always_comb begin
        wdata_user = {wdata_i, wuser_i};
        be         = {be_i, be_i};
        rdata_o    = rdata_user[DATA_AND_USER_WIDTH-1:DATA_WIDTH];
        ruser_o    = rdata_user[USER_WIDTH-1:0];
      end
      tc_sram_wrapper_cache_techno #(
        .NumWords(NUM_WORDS),           // Number of Words in data array
        .DataWidth(DATA_AND_USER_WIDTH),// Data signal width
        .ByteWidth(32'd8),              // Width of a data byte
        .NumPorts(32'd1),               // Number of read and write ports
        .Latency(32'd1),                // Latency when the read data is available
        .SimInit(SIM_INIT),             // Simulation initialization
        .BYTE_ACCESS(BYTE_ACCESS),      // ACCESS byte or full word
        .PrintSimCfg(1'b0)              // Print configuration
      ) i_tc_sram_wrapper (
        .clk_i    ( clk_i                     ),
        .rst_ni   ( rst_ni                    ),
        .req_i    ( req_i                     ),
        .we_i     ( we_i                      ),
        .be_i     ( be                        ),
        .wdata_i  ( wdata_user                ),
        .addr_i   ( addr_i                    ),
        .rdata_o  ( rdata_user                )
      );
    end else begin
      logic [DATA_WIDTH-1:0] wdata_user;
      logic [DATA_WIDTH-1:0] rdata_user;
      logic [(DATA_WIDTH+7)/8-1:0] be;

      always_comb begin
        wdata_user = wdata_i;
        be         = be_i;
        rdata_o    = rdata_user;
        ruser_o    = '0;
      end
      tc_sram_wrapper_cache_techno #(
        .NumWords(NUM_WORDS),           // Number of Words in data array
        .DataWidth(DATA_AND_USER_WIDTH),// Data signal width
        .ByteWidth(32'd8),              // Width of a data byte
        .NumPorts(32'd1),               // Number of read and write ports
        .Latency(32'd1),                // Latency when the read data is available
        .SimInit(SIM_INIT),             // Simulation initialization
        .BYTE_ACCESS(BYTE_ACCESS),      // ACCESS byte or full word
        .PrintSimCfg(1'b0)              // Print configuration
      ) i_tc_sram_wrapper (
        .clk_i    ( clk_i                     ),
        .rst_ni   ( rst_ni                    ),
        .req_i    ( req_i                     ),
        .we_i     ( we_i                      ),
        .be_i     ( be                        ),
        .wdata_i  ( wdata_user                ),
        .addr_i   ( addr_i                    ),
        .rdata_o  ( rdata_user                )
      );
    end
  end else begin
    sram #(
          .USER_WIDTH (USER_WIDTH),
          .DATA_WIDTH (DATA_WIDTH),
          .USER_EN    (USER_EN),
          .NUM_WORDS  (NUM_WORDS)
      ) data_sram (
          .clk_i  (clk_i),
          .rst_ni (rst_ni),
          .req_i  (req_i),
          .we_i   (we_i),
          .addr_i (addr_i),
          .wuser_i(wuser_i),
          .wdata_i(wdata_i),
          .be_i   (be_i),
          .ruser_o(ruser_o),
          .rdata_o(rdata_o)
      );
  end


endmodule : sram_cache
