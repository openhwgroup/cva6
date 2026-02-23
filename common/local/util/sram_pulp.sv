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
//         Nils Wistoff      <nwistoff@iis.ee.ethz.ch>, ETH Zurich
// Date: 15.08.2018
// Description: generic tc_sram wrapper for CVA6
//
// Note: the wrapped module contains two different implementations for
// ALTERA and XILINX tools, since these follow different coding styles for
// inferrable RAMS with byte enable. define `FPGA_TARGET_XILINX or
// `FPGA_TARGET_ALTERA in your build environment (default is ALTERA)

module sram #(
    parameter DATA_WIDTH = 64,
    parameter BYTE_WIDTH = 8,
    parameter USER_WIDTH = 1,
    parameter USER_EN    = 0,
    parameter NUM_WORDS  = 1024,
    parameter SIM_INIT   = "none",
    parameter OUT_REGS   = 0     // enables output registers in FPGA macro (read lat = 2)
)(
   input  logic                          clk_i,
   input  logic                          rst_ni,
   input  logic                          req_i,
   input  logic                          we_i,
   input  logic [$clog2(NUM_WORDS)-1:0]  addr_i,
   input  logic [USER_WIDTH-1:0]         wuser_i,
   input  logic [DATA_WIDTH-1:0]         wdata_i,
   input  logic [(DATA_WIDTH+BYTE_WIDTH-1)/BYTE_WIDTH-1:0] be_i,
   output logic [USER_WIDTH-1:0]         ruser_o,
   output logic [DATA_WIDTH-1:0]         rdata_o
);

  tc_sram #(
    .NumWords    ( NUM_WORDS  ),
    .DataWidth   ( DATA_WIDTH ),
    .ByteWidth   ( BYTE_WIDTH ),
    .NumPorts    ( 32'd1      ),
    .Latency     ( 32'd1      ),
    .SimInit     ( SIM_INIT   ),
    .PrintSimCfg ( 1'b0       )
  ) i_tc_sram (
    .clk_i   ( clk_i   ),
    .rst_ni  ( rst_ni  ),
    .req_i   ( req_i   ),
    .we_i    ( we_i    ),
    .be_i    ( be_i    ),
    .wdata_i ( wdata_i ),
    .addr_i  ( addr_i  ),
    .rdata_o ( rdata_o )
  );

  if (USER_EN > 0) begin : gen_mem_user
    tc_sram #(
      .NumWords    ( NUM_WORDS  ),
      .DataWidth   ( DATA_WIDTH ),
      .ByteWidth   ( BYTE_WIDTH ),
      .NumPorts    ( 32'd1      ),
      .Latency     ( 32'd1      ),
      .SimInit     ( SIM_INIT   ),
      .PrintSimCfg ( 1'b0       )
    ) i_tc_sram_user (
      .clk_i   ( clk_i   ),
      .rst_ni  ( rst_ni  ),
      .req_i   ( req_i   ),
      .we_i    ( we_i    ),
      .be_i    ( be_i    ),
      .wdata_i ( wuser_i ),
      .addr_i  ( addr_i  ),
      .rdata_o ( ruser_o )
    );

    if (USER_WIDTH != DATA_WIDTH) begin : gen_err_data_user_width
      $fatal(1, "sram_pulp: USER_WIDTH needs to be equal to DATA_WIDTH (if USER_EN is set).");
    end

  end else begin : gen_mem_user
    assign ruser_o = '0;
    // synthesis translate_off
    begin : i_tc_sram_user
      localparam type data_t = logic [DATA_WIDTH-1:0];
      data_t init_val [0:0];
      data_t sram [NUM_WORDS-1:0] /* verilator public_flat */;
    end
    // synthesis translate_on
  end
endmodule : sram
