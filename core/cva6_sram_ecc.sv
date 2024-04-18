// Copyright 2024 OpenHW Group.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

module cva6_sram_ecc #(
  parameter DATA_WIDTH = 64,
  parameter USER_WIDTH = 1,
  parameter USER_EN    = 0,
  parameter NUM_WORDS  = 1024,
  parameter SIM_INIT   = "none",
  parameter OUT_REGS   = 0,     // enables output registers in FPGA macro (read lat = 2)
  parameter bit ECC_EN = 1'b0,
  parameter type parity_t = logic [ecc_pkg::get_parity_width(DATA_WIDTH)-1:0]
)(
  input  logic                          clk_i,
  input  logic                          rst_ni,
  input  logic                          req_i,
  input  logic                          we_i,
  input  logic [$clog2(NUM_WORDS)-1:0]  addr_i,
  input  logic [USER_WIDTH-1:0]         wuser_i,
  input  logic [DATA_WIDTH-1:0]         wdata_i,
  output logic [USER_WIDTH-1:0]         ruser_o,
  output logic [DATA_WIDTH-1:0]         rdata_o,
  /// Error syndrome indicates the erroneous bit position
  output parity_t                       syndrome_o,
  /// A single error occurred
  output logic                          single_error_o,
  /// Error received in parity bit (MSB)
  output logic                          parity_error_o,
  /// A double error occurred
  output logic                          double_error_o
);

  // SRAM data width depends on whether ECC is enable or not.
  localparam int unsigned SRAM_DATA_WIDTH = ECC_EN ? ecc_pkg::get_cw_width(DATA_WIDTH) + 1 : DATA_WIDTH;

  logic [SRAM_DATA_WIDTH-1:0] rdata_sram, wdata_sram;

  sram #(
      .USER_WIDTH(USER_WIDTH),
      .DATA_WIDTH(SRAM_DATA_WIDTH),
      .USER_EN   (USER_EN),
      .NUM_WORDS (NUM_WORDS)
  ) i_sram (
      .clk_i,
      .rst_ni,
      .req_i,
      .we_i,
      .addr_i,
      .wuser_i (wuser_i),
      .wdata_i (wdata_sram),
      .be_i ('1),
      .ruser_o (ruser_o),
      .rdata_o (rdata_sram)
  );

  if (ECC_EN) begin: gen_ecc
    ecc_encode #(
      .DataWidth (DATA_WIDTH)
    ) i_ecc_encode_tag_sram (
      .data_i (wdata_i),
      .data_o (wdata_sram)
    );

    ecc_decode #(
      .DataWidth(DATA_WIDTH)
    ) i_ecc_decode_tag_sram (
      .data_i (rdata_sram),
      .data_o (rdata_o),
      .syndrome_o (),
      .single_error_o,
      .parity_error_o,
      .double_error_o
    );

  end else begin : gen_no_ecc
    assign wdata_sram = wdata_i;
    assign rdata_o = rdata_sram;
    assign syndrome_o = '0;
    assign single_error_o = '0;
    assign parity_error_o = '0;
    assign double_error_o = '0;
  end

endmodule
