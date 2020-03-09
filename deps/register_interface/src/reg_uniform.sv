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

/// A uniform register file.
module reg_uniform #(
  /// The width of the address.
  parameter int ADDR_WIDTH = -1,
  /// The width of the data.
  parameter int DATA_WIDTH = -1,
  /// The number of registers.
  parameter int NUM_REG = -1,
  /// The width of each register.
  parameter int REG_WIDTH = -1,
  /// The register write mask
  parameter logic [NUM_REG-1:0] REG_WRITABLE = '1
)(
  input  logic                              clk_i      ,
  input  logic                              rst_ni     ,
  input  logic [NUM_REG-1:0][REG_WIDTH-1:0] init_val_i , // initial register value
  input  logic [NUM_REG-1:0][REG_WIDTH-1:0] rd_val_i   , // register read value
  output logic [NUM_REG-1:0][REG_WIDTH-1:0] wr_val_o   , // register written value
  output logic [NUM_REG-1:0]                wr_evt_o   ,
  REG_BUS.in   reg_i
);

  // Generate the flip flops for the registers.
  logic [NUM_REG-1:0][REG_WIDTH-1:0] reg_q;
  logic [NUM_REG-1:0][REG_WIDTH/8-1:0] reg_wr;

  for (genvar i = 0; i < NUM_REG; i++) begin
    // If this register is writable, create a flip flop for it. Otherwise map it
    // to the initial value.
    if (REG_WRITABLE[i]) begin
      // Generate one flip-flop per byte enable.
      for (genvar j = 0; j < REG_WIDTH/8; j++) begin
        always_ff @(posedge clk_i, negedge rst_ni) begin
          if (!rst_ni)
            reg_q[i][j*8+7 -: 8] <= init_val_i[i][j*8+7 -: 8];
          else if (reg_wr[i][j])
            reg_q[i][j*8+7 -: 8] <= reg_i.wdata[(i*REG_WIDTH+j*8+7)%DATA_WIDTH -: 8];
        end
      end
    end else begin
      assign reg_q[i] = init_val_i[i];
    end
  end

  // Generate the written register value and event signals.
  always_comb begin
    wr_val_o = reg_q;
    for (int i = 0; i < NUM_REG; i++)
      wr_evt_o[i] = |reg_wr[i];
  end

  // Map the byte address of the bus to a bus word address.
  localparam int ADDR_SHIFT = $clog2(DATA_WIDTH/8);
  logic [ADDR_WIDTH-ADDR_SHIFT-1:0] bus_word_addr;
  assign bus_word_addr = reg_i.addr >> ADDR_SHIFT;

  // Map the register dimensions to bus dimensions.
  localparam int NUM_BUS_WORDS = (NUM_REG * REG_WIDTH + DATA_WIDTH - 1) / DATA_WIDTH;
  logic [NUM_BUS_WORDS-1:0][DATA_WIDTH-1:0] reg_busmapped;
  logic [NUM_BUS_WORDS-1:0][DATA_WIDTH/8-1:0] reg_wr_busmapped;
  assign reg_busmapped = rd_val_i;
  assign reg_wr = reg_wr_busmapped;

  // Implement the communication via the register interface.
  always_comb begin
    reg_wr_busmapped = '0;
    reg_i.ready = 1;
    reg_i.rdata = '0;
    reg_i.error = 0;
    if (reg_i.valid) begin
      if (bus_word_addr < NUM_BUS_WORDS) begin
        reg_i.rdata = reg_busmapped[bus_word_addr];
        if (reg_i.write) begin
          reg_wr_busmapped[bus_word_addr] = reg_i.wstrb;
        end
      end else begin
        reg_i.error = 1;
      end
    end
  end

endmodule
