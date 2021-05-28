// Copyright (c) 2014-2018 ETH Zurich, University of Bologna
//
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

import axi_pkg::*;


/// An AXI4-Lite crossbar.
module axi_lite_xbar #(
  /// The address width.
  parameter int ADDR_WIDTH = -1,
  /// The data width.
  parameter int DATA_WIDTH = -1,
  /// The number of master ports.
  parameter int NUM_MASTER = 1,
  /// The number of slave ports.
  parameter int NUM_SLAVE = 1,
  /// The number of routing rules.
  parameter int NUM_RULES = -1
)(
  input logic            clk_i               ,
  input logic            rst_ni              ,
  AXI_LITE.Slave         master [NUM_MASTER] ,
  AXI_LITE.Master        slave  [NUM_SLAVE]  ,
  AXI_ROUTING_RULES.xbar rules
);

  // The arbitration bus.
  AXI_ARBITRATION #(.NUM_REQ(NUM_MASTER)) s_arb_rd(), s_arb_wr();

  // For now just instantiate the simple crossbar. We may want to add different
  // implementations later.
  axi_lite_xbar_simple #(
    .ADDR_WIDTH ( ADDR_WIDTH ),
    .DATA_WIDTH ( DATA_WIDTH ),
    .NUM_MASTER ( NUM_MASTER ),
    .NUM_SLAVE  ( NUM_SLAVE  ),
    .NUM_RULES  ( NUM_RULES  )
  ) i_simple (
    .clk_i  ( clk_i        ),
    .rst_ni ( rst_ni       ),
    .master ( master       ),
    .slave  ( slave        ),
    .rules  ( rules        ),
    .arb_rd ( s_arb_rd.req ),
    .arb_wr ( s_arb_wr.req )
  );

  // Instantiate round-robin arbiters for the read and write channels.
  axi_arbiter #(
    .NUM_REQ ( NUM_MASTER )
  ) i_arb_rd (
    .clk_i  ( clk_i        ),
    .rst_ni ( rst_ni       ),
    .arb    ( s_arb_rd.arb )
  );

  axi_arbiter #(
    .NUM_REQ ( NUM_MASTER )
  ) i_arb_wr (
    .clk_i  ( clk_i        ),
    .rst_ni ( rst_ni       ),
    .arb    ( s_arb_wr.arb )
  );

endmodule


/// A simple implementation of an AXI4-Lite crossbar. Can only serve one master
/// at a time.
module axi_lite_xbar_simple #(
  /// The address width.
  parameter int ADDR_WIDTH = -1,
  /// The data width.
  parameter int DATA_WIDTH = -1,
  /// The number of master ports.
  parameter int NUM_MASTER = 1,
  /// The number of slave ports.
  parameter int NUM_SLAVE = 1,
  /// The number of routing rules.
  parameter int NUM_RULES = -1
)(
  input logic            clk_i               ,
  input logic            rst_ni              ,
  AXI_LITE.Slave         master [NUM_MASTER] ,
  AXI_LITE.Master        slave  [NUM_SLAVE]  ,
  AXI_ROUTING_RULES.xbar rules               ,
  AXI_ARBITRATION.req    arb_rd              ,
  AXI_ARBITRATION.req    arb_wr
);

  `ifndef SYNTHESIS
  initial begin
    assert(NUM_MASTER > 0);
    assert(NUM_SLAVE > 0);
    assert(NUM_RULES > 0);
    assert(rules.AXI_ADDR_WIDTH == ADDR_WIDTH);
    assert(rules.NUM_SLAVE == NUM_SLAVE);
  end

  // Check master address widths are all equal.
  for (genvar i = 0; i < NUM_MASTER; i++) begin : g_chk_master
    initial begin
      assert(master[i].AXI_ADDR_WIDTH == ADDR_WIDTH);
      assert(master[i].AXI_DATA_WIDTH == DATA_WIDTH);
    end
  end

  // Check slave address widths are all equal.
  for (genvar i = 0; i < NUM_SLAVE; i++) begin
    initial begin
      assert(slave[i].AXI_ADDR_WIDTH == ADDR_WIDTH);
      assert(slave[i].AXI_DATA_WIDTH == DATA_WIDTH);
    end
  end
  `endif

  typedef logic [ADDR_WIDTH-1:0]   addr_t;
  typedef logic [DATA_WIDTH-1:0]   data_t;
  typedef logic [DATA_WIDTH/8-1:0] strb_t;

  typedef logic [$clog2(NUM_MASTER)-1:0] master_id_t;
  typedef logic [$clog2(NUM_SLAVE)-1:0]  slave_id_t;

  // The tag specifies which master is currently being served, and what slave it
  // is targeting. There are independent tags for read and write.
  struct packed {
    master_id_t master;
    slave_id_t  slave;
  } tag_rd_d, tag_wr_d, tag_rd_q, tag_wr_q;

  enum { RD_IDLE, RD_REQ, RD_RESP, RD_ERR_RESP } state_rd_d, state_rd_q;
  enum { WR_IDLE, WR_REQ, WR_DATA, WR_RESP, WR_ERR_DATA, WR_ERR_RESP } state_wr_d, state_wr_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) begin
      state_rd_q <= RD_IDLE;
      state_wr_q <= WR_IDLE;
      tag_rd_q <= '0;
      tag_wr_q <= '0;
    end else begin
      state_rd_q <= state_rd_d;
      state_wr_q <= state_wr_d;
      tag_rd_q <= tag_rd_d;
      tag_wr_q <= tag_wr_d;
    end
  end

  // Generate the master-side multiplexer. This allows one of the masters to be
  // contacted by setting the master_sel_{rd,wr} signal.
  master_id_t master_sel_rd, master_sel_wr;

  addr_t [NUM_MASTER-1:0] master_araddr_pack;
  logic  [NUM_MASTER-1:0] master_rready_pack;

  addr_t [NUM_MASTER-1:0] master_awaddr_pack;
  data_t [NUM_MASTER-1:0] master_wdata_pack;
  strb_t [NUM_MASTER-1:0] master_wstrb_pack;
  logic  [NUM_MASTER-1:0] master_wvalid_pack;
  logic  [NUM_MASTER-1:0] master_bready_pack;

  addr_t master_araddr;
  logic  master_arready;
  data_t master_rdata;
  resp_t master_rresp;
  logic  master_rvalid;
  logic  master_rready;

  addr_t master_awaddr;
  logic  master_awready;
  data_t master_wdata;
  strb_t master_wstrb;
  logic  master_wvalid;
  logic  master_wready;
  resp_t master_bresp;
  logic  master_bvalid;
  logic  master_bready;

  for (genvar i = 0; i < NUM_MASTER; i++) begin
    assign master_araddr_pack[i]   = master[i].ar_addr;
    assign master[i].ar_ready      = master_arready && (i == master_sel_rd);
    assign master[i].r_data        = master_rdata;
    assign master[i].r_resp        = master_rresp;
    assign master[i].r_valid       = master_rvalid && (i == master_sel_rd);
    assign master_rready_pack[i]   = master[i].r_ready;

    assign master_awaddr_pack[i]   = master[i].aw_addr;
    assign master[i].aw_ready      = master_awready && (i == master_sel_wr);
    assign master_wdata_pack[i]    = master[i].w_data;
    assign master_wstrb_pack[i]    = master[i].w_strb;
    assign master_wvalid_pack[i]   = master[i].w_valid;
    assign master[i].w_ready       = master_wready && (i == master_sel_wr);
    assign master[i].b_resp        = master_bresp;
    assign master_bready_pack[i]   = master[i].b_ready;
    assign master[i].b_valid       = master_bvalid && (i == master_sel_wr);
  end

  assign master_araddr  = master_araddr_pack  [master_sel_rd];
  assign master_rready  = master_rready_pack  [master_sel_rd];

  assign master_awaddr  = master_awaddr_pack  [master_sel_wr];
  assign master_wdata   = master_wdata_pack   [master_sel_wr];
  assign master_wstrb   = master_wstrb_pack   [master_sel_wr];
  assign master_wvalid  = master_wvalid_pack  [master_sel_wr];
  assign master_bready  = master_bready_pack  [master_sel_wr];

  // Generate the slave-side multiplexer. This allows one of the slaves to be
  // contacted by setting the slave_sel_{rd,wr} signal.
  slave_id_t slave_sel_rd, slave_sel_wr;

  logic  [NUM_SLAVE-1:0] slave_arready_pack;
  data_t [NUM_SLAVE-1:0] slave_rdata_pack;
  resp_t [NUM_SLAVE-1:0] slave_rresp_pack;
  logic  [NUM_SLAVE-1:0] slave_rvalid_pack;

  logic  [NUM_SLAVE-1:0] slave_awready_pack;
  logic  [NUM_SLAVE-1:0] slave_wready_pack;
  resp_t [NUM_SLAVE-1:0] slave_bresp_pack;
  logic  [NUM_SLAVE-1:0] slave_bvalid_pack;

  addr_t slave_araddr;
  logic  slave_arvalid;
  logic  slave_arready;
  data_t slave_rdata;
  resp_t slave_rresp;
  logic  slave_rvalid;
  logic  slave_rready;

  addr_t slave_awaddr;
  logic  slave_awvalid;
  logic  slave_awready;
  data_t slave_wdata;
  strb_t slave_wstrb;
  logic  slave_wvalid;
  logic  slave_wready;
  resp_t slave_bresp;
  logic  slave_bvalid;
  logic  slave_bready;

  for (genvar i = 0; i < NUM_SLAVE; i++) begin
    assign slave[i].ar_addr      = slave_araddr;
    assign slave[i].ar_valid     = slave_arvalid && (i == slave_sel_rd);
    assign slave_arready_pack[i] = slave[i].ar_ready;
    assign slave_rdata_pack[i]   = slave[i].r_data;
    assign slave_rresp_pack[i]   = slave[i].r_resp;
    assign slave_rvalid_pack[i]  = slave[i].r_valid;
    assign slave[i].r_ready      = slave_rready && (i == slave_sel_rd);

    assign slave[i].aw_addr      = slave_awaddr;
    assign slave[i].aw_valid     = slave_awvalid && (i == slave_sel_wr);
    assign slave_awready_pack[i] = slave[i].aw_ready;
    assign slave[i].w_data       = slave_wdata;
    assign slave[i].w_strb       = slave_wstrb;
    assign slave[i].w_valid      = slave_wvalid && (i == slave_sel_wr);
    assign slave_wready_pack[i]  = slave[i].w_ready;
    assign slave_bresp_pack[i]   = slave[i].b_resp;
    assign slave_bvalid_pack[i]  = slave[i].b_valid;
    assign slave[i].b_ready      = slave_bready && (i == slave_sel_wr);
  end

  assign slave_arready = slave_arready_pack [slave_sel_rd];
  assign slave_rdata   = slave_rdata_pack   [slave_sel_rd];
  assign slave_rresp   = slave_rresp_pack   [slave_sel_rd];
  assign slave_rvalid  = slave_rvalid_pack  [slave_sel_rd];

  assign slave_awready = slave_awready_pack [slave_sel_wr];
  assign slave_wready  = slave_wready_pack  [slave_sel_wr];
  assign slave_bresp   = slave_bresp_pack   [slave_sel_wr];
  assign slave_bvalid  = slave_bvalid_pack  [slave_sel_wr];

  // Route the valid signals of the masters to the arbiters. They will decide
  // which request will be granted.
  for (genvar i = 0; i < NUM_MASTER; i++) begin
    assign arb_rd.in_req[i] = master[i].ar_valid;
    assign arb_wr.in_req[i] = master[i].aw_valid;
  end

  // Perform address resolution.
  addr_t rd_resolve_addr, wr_resolve_addr;
  logic [$clog2(NUM_SLAVE)-1:0] rd_match_idx, wr_match_idx;
  logic rd_match_ok, wr_match_ok;

  axi_address_resolver #(
    .ADDR_WIDTH( ADDR_WIDTH ),
    .NUM_SLAVE ( NUM_SLAVE  ),
    .NUM_RULES ( NUM_RULES  )
  ) i_rd_resolver (
    .rules       ( rules           ),
    .addr_i      ( rd_resolve_addr ),
    .match_idx_o ( rd_match_idx    ),
    .match_ok_o  ( rd_match_ok     )
  );

  axi_address_resolver #(
    .ADDR_WIDTH( ADDR_WIDTH ),
    .NUM_SLAVE ( NUM_SLAVE  ),
    .NUM_RULES ( NUM_RULES  )
  ) i_wr_resolver (
    .rules       ( rules           ),
    .addr_i      ( wr_resolve_addr ),
    .match_idx_o ( wr_match_idx    ),
    .match_ok_o  ( wr_match_ok     )
  );

  // Read state machine.
  always_comb begin
    state_rd_d      = state_rd_q;
    tag_rd_d        = tag_rd_q;

    arb_rd.out_ack  = 0;
    master_sel_rd   = tag_rd_q.master;
    slave_sel_rd    = tag_rd_q.slave;
    rd_resolve_addr = master_araddr;

    slave_araddr    = master_araddr;
    slave_arvalid   = 0;
    master_arready  = 0;
    master_rdata    = slave_rdata;
    master_rresp    = slave_rresp;
    master_rvalid   = 0;
    slave_rready    = 0;

    case (state_rd_q)
      RD_IDLE: begin
        master_sel_rd = arb_rd.out_sel;
        if (arb_rd.out_req) begin
          arb_rd.out_ack  = 1;
          tag_rd_d.master = arb_rd.out_sel;
          state_rd_d      = RD_REQ;
        end
      end

      RD_REQ: begin
        slave_sel_rd   = rd_match_idx;
        tag_rd_d.slave = rd_match_idx;
        // If the address resolution was successful, propagate the request and
        // wait for a response. Otherwise immediately return an error.
        if (rd_match_ok) begin
          slave_arvalid = 1;
          if (slave_arready) begin
            state_rd_d     = RD_RESP;
            master_arready = 1;
          end
        end else begin
          state_rd_d     = RD_ERR_RESP;
          master_arready = 1;
        end
      end

      RD_RESP: begin
        master_rvalid = slave_rvalid;
        slave_rready = master_rready;
        if (slave_rvalid && master_rready) begin
          state_rd_d = RD_IDLE;
        end
      end

      // Address resolution failed. Return an error response.
      RD_ERR_RESP: begin
        master_rresp  = axi_pkg::RESP_DECERR;
        master_rvalid = 1;
        if (master_rready) begin
          state_rd_d = RD_IDLE;
        end
      end

      default: state_rd_d = RD_IDLE;
    endcase
  end

  // Write state machine.
  always_comb begin
    state_wr_d = state_wr_q;
    tag_wr_d   = tag_wr_q;

    arb_wr.out_ack  = 0;
    master_sel_wr   = tag_wr_q.master;
    slave_sel_wr    = tag_wr_q.slave;
    wr_resolve_addr = master_awaddr;

    slave_awaddr    = master_awaddr;
    slave_awvalid   = 0;
    master_awready  = 0;
    slave_wdata     = master_wdata;
    slave_wstrb     = master_wstrb;
    slave_wvalid    = 0;
    master_wready   = 0;
    master_bresp    = slave_bresp;
    master_bvalid   = 0;
    slave_bready    = 0;

    case (state_wr_q)
      WR_IDLE: begin
        master_sel_wr = arb_wr.out_sel;
        if (arb_wr.out_req) begin
          arb_wr.out_ack  = 1;
          tag_wr_d.master = arb_wr.out_sel;
          state_wr_d      = WR_REQ;
        end
      end

      WR_REQ: begin
        slave_sel_wr   = wr_match_idx;
        tag_wr_d.slave = wr_match_idx;
        // If the address resolution was successful, propagate the request and
        // wait for a response. Otherwise immediately return an error.
        if (wr_match_ok) begin
          slave_awvalid = 1;
          if (slave_awready) begin
            state_wr_d     = WR_DATA;
            master_awready = 1;
          end
        end else begin
          state_wr_d     = WR_ERR_DATA;
          master_awready = 1;
        end
      end

      WR_DATA: begin
        master_wready = slave_wready;
        slave_wvalid = master_wvalid;
        if (slave_wvalid && master_wready) begin
          state_wr_d = WR_RESP;
        end
      end

      WR_RESP: begin
        master_bvalid = slave_bvalid;
        slave_bready = master_bready;
        if (slave_bvalid && master_bready) begin
          state_wr_d = WR_IDLE;
        end
      end

      // Address resolution failed. Discard the data transfer.
      WR_ERR_DATA: begin
        master_wready = 1;
        if (master_wvalid) begin
          state_wr_d = WR_ERR_RESP;
        end
      end

      // Address resolution failed. Return an error response.
      WR_ERR_RESP: begin
        master_bresp  = axi_pkg::RESP_DECERR;
        master_bvalid = 1;
        if (master_bready) begin
          state_wr_d = WR_IDLE;
        end
      end

      default: state_wr_d = WR_IDLE;
    endcase
  end

endmodule
