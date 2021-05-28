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
//
// Fabian Schuiki <fschuiki@iis.ee.ethz.ch>

/// A protocol converter from AXI4-Lite to a register interface.
module axi_lite_to_reg #(
  /// The width of the address.
  parameter int ADDR_WIDTH = -1,
  /// The width of the data.
  parameter int DATA_WIDTH = -1,
  /// Whether the AXI-Lite W channel should be decoupled with a register. This
  /// can help break long paths at the expense of registers.
  parameter bit DECOUPLE_W = 1
)(
  input  logic clk_i  ,
  input  logic rst_ni ,
  AXI_LITE.in  axi_i  ,
  REG_BUS.out  reg_o
);

  `ifndef SYNTHESIS
  initial begin
    assert(ADDR_WIDTH > 0);
    assert(DATA_WIDTH > 0);
  end
  `endif

  // Define some useful types.
  typedef logic [ADDR_WIDTH-1:0]   addr_t;
  typedef logic [DATA_WIDTH-1:0]   data_t;
  typedef logic [DATA_WIDTH/8-1:0] strb_t;

  // Signals to the register bus multiplexer.
  addr_t reg_wr_addr;
  data_t reg_wr_data;
  strb_t reg_wr_strb;
  logic  reg_wr_req;
  logic  reg_wr_error;
  logic  reg_wr_ack;

  addr_t reg_rd_addr;
  logic  reg_rd_req;
  data_t reg_rd_data;
  logic  reg_rd_error;
  logic  reg_rd_ack;

  // Write address register.
  addr_t wr0_addr_q;
  logic wr0_valid_q;
  logic wr0_ready;
  assign axi_i.aw_ready = wr0_ready;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      wr0_addr_q <= '0;
      wr0_valid_q <= '0;
    end else begin
      if (axi_i.aw_valid && wr0_ready)
        wr0_addr_q <= axi_i.aw_addr;
      if (wr0_ready)
        wr0_valid_q <= axi_i.aw_valid;
    end
  end

  // Write data register. Optional, as specified by DECOUPLE_W.
  addr_t wr1_addr_q;
  data_t wr1_data_q;
  strb_t wr1_strb_q;
  logic wr1_valid_q;
  logic wr1_ready;
  assign wr0_ready = !wr1_valid_q || wr1_ready;
  assign axi_i.w_ready = wr1_ready;
  if (DECOUPLE_W) begin : g_decouple_w
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        wr1_addr_q <= '0;
        wr1_data_q <= '0;
        wr1_strb_q <= '0;
        wr1_valid_q <= '0;
      end else begin
        if (axi_i.w_valid && wr0_valid_q && wr1_ready) begin
          wr1_addr_q <= wr0_addr_q;
          wr1_data_q <= axi_i.w_data;
          wr1_strb_q <= axi_i.w_strb;
        end
        if (wr1_ready)
          wr1_valid_q <= axi_i.w_valid && wr0_valid_q;
      end
    end
  end else begin : g_passthru_w
    assign wr1_addr_q = wr0_addr_q;
    assign wr1_data_q = axi_i.w_data;
    assign wr1_strb_q = axi_i.w_strb;
    assign wr1_valid_q = axi_i.w_valid && wr0_valid_q;
  end

  // Write response register.
  logic wr2_error_q;
  logic wr2_valid_q;
  logic wr2_ready;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      wr2_error_q <= '0;
      wr2_valid_q <= '0;
    end else begin
      if (reg_wr_ack && wr2_ready)
        wr2_error_q <= reg_wr_error;
      if (wr2_ready)
        wr2_valid_q <= reg_wr_ack;
    end
  end

  // Write emission.
  assign reg_wr_addr = wr1_addr_q;
  assign reg_wr_data = wr1_data_q;
  assign reg_wr_strb = wr1_strb_q;
  assign reg_wr_req  = wr1_valid_q && wr2_ready;
  assign wr1_ready = reg_wr_ack || ~reg_wr_req;

  // Write response decoupling register.
  logic wr3_error_q, wr3_error_z;
  logic wr3_valid_q, wr3_valid_z;
  logic wr3_ready;
  assign wr2_ready = !wr3_valid_q;
  assign wr3_error_z = wr3_valid_q ? wr3_error_q : wr2_error_q;
  assign wr3_valid_z = wr3_valid_q || wr2_valid_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      wr3_error_q <= '0;
      wr3_valid_q <= '0;
    end else begin
      if (wr2_valid_q && !wr3_ready)
        wr3_error_q <= wr2_error_q;
      if (wr3_ready)
        wr3_valid_q <= wr2_valid_q && !wr3_ready;
    end
  end

  assign axi_i.b_valid = wr3_valid_z;
  assign axi_i.b_resp  = wr3_error_z << 1;
  assign wr3_ready = axi_i.b_ready;

  // Read address register.
  addr_t rd0_addr_q;
  logic rd0_valid_q;
  logic rd0_ready;
  assign axi_i.ar_ready = rd0_ready;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rd0_addr_q <= '0;
      rd0_valid_q <= '0;
    end else begin
      if (axi_i.ar_valid && rd0_ready)
        rd0_addr_q <= axi_i.ar_addr;
      if (rd0_ready)
        rd0_valid_q <= axi_i.ar_valid;
    end
  end

  // Read response register.
  data_t rd1_data_q;
  logic  rd1_error_q;
  logic  rd1_valid_q;
  logic  rd1_ready;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rd1_data_q <= '0;
      rd1_error_q <= '0;
      rd1_valid_q <= '0;
    end else begin
      if (reg_rd_ack && rd1_ready) begin
        rd1_data_q <= reg_rd_data;
        rd1_error_q <= reg_rd_error;
      end
      if (rd1_ready)
        rd1_valid_q <= reg_rd_ack;
    end
  end

  // Read emission.
  assign reg_rd_addr = rd0_addr_q;
  assign reg_rd_req  = rd0_valid_q && rd1_ready;
  assign rd0_ready = reg_rd_ack || ~reg_rd_req;

  // Read response decoupling register.
  data_t rd2_data_q, rd2_data_z;
  logic  rd2_error_q, rd2_error_z;
  logic  rd2_valid_q, rd2_valid_z;
  logic  rd2_ready;
  assign rd1_ready = !rd2_valid_q;
  assign rd2_data_z = rd2_valid_q ? rd2_data_q : rd1_data_q;
  assign rd2_error_z = rd2_valid_q ? rd2_error_q : rd1_error_q;
  assign rd2_valid_z = rd2_valid_q || rd1_valid_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rd2_data_q <= '0;
      rd2_error_q <= '0;
      rd2_valid_q <= '0;
    end else begin
      if (rd1_valid_q && !rd2_ready) begin
        rd2_data_q <= rd1_data_q;
        rd2_error_q <= rd1_error_q;
      end
      if (rd1_valid_q || rd2_ready)
        rd2_valid_q <= rd1_valid_q && !rd2_ready;
    end
  end

  assign axi_i.r_valid = rd2_valid_z;
  assign axi_i.r_data  = rd2_data_z;
  assign axi_i.r_resp  = rd2_error_z << 1;
  assign rd2_ready = axi_i.r_ready;

  // Register bus multiplexer. Provides fair arbitration between write and read
  // accesses.
  logic reg_arb_q;
  logic reg_sel; // 1=write, 0=read

  assign reg_o.addr   = reg_sel ? reg_wr_addr : reg_rd_addr;
  assign reg_o.write  = reg_sel;
  assign reg_rd_data  = reg_sel ? '0 : reg_o.rdata;
  assign reg_o.wdata  = reg_sel ? reg_wr_data : '0;
  assign reg_o.wstrb  = reg_sel ? reg_wr_strb : '0;
  assign reg_wr_error = reg_sel ? reg_o.error : 0;
  assign reg_rd_error = reg_sel ? 0 : reg_o.error;
  assign reg_o.valid  = reg_sel ? reg_wr_req : reg_rd_req;
  assign reg_wr_ack   = reg_sel ? reg_o.ready && reg_wr_req : 0;
  assign reg_rd_ack   = reg_sel ? 0 : reg_o.ready && reg_rd_req;

  // Register bus arbitration. The scheme works as follows: The reg_arb_q
  // register is held at reg_sel as long as no transaction finishes on the
  // register bus. As soon as a transaction finishes, reg_arb_q is set to the
  // inverse of reg_sel. Thus reg_arb_q indicates who should have priority at
  // any given point in time. The reg_sel signal then performs the arbitration,
  // resorting to the reg_arb_q signal in case both requests are high. This
  // scheme ensures that reg_sel does not change while a valid request is
  // presented on the register bus.
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni)
      reg_arb_q <= '0;
    else
      reg_arb_q <= reg_o.valid && reg_o.ready ? ~reg_sel : reg_sel;
  end

  always_comb begin
    if (reg_wr_req && reg_rd_req)
      reg_sel = reg_arb_q;
    else if (reg_wr_req)
      reg_sel = 1;
    else if (reg_rd_req)
      reg_sel = 0;
    else
      reg_sel = 0;
  end

endmodule
