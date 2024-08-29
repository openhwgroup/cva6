//-----------------------------------------------------------------------------
// Copyright 2024 Robert Bosch GmbH
//
// SPDX-License-Identifier: SHL-0.51
//
// Original Author: Coralie Allioux - Robert Bosch France SAS
//-----------------------------------------------------------------------------

module dscr_controller
  import scratchpad_pkg::*;
#(
    parameter config_pkg::cva6_cfg_t CVA6Cfg = config_pkg::cva6_cfg_empty,
    parameter int unsigned DATA_WIDTH = 64,
    parameter int unsigned NUM_WORDS = 1024,
    parameter type dcache_req_i_t = logic,
    parameter type dcache_req_o_t = logic,
    parameter type scratchpad_req_i_t = logic,
    parameter type ahb_resp_t = logic,
    parameter type ahb_req_t = logic
) (
    input logic clk_i,
    input logic rst_ni,

    // Load req interface
    input  scratchpad_req_i_t ld_req_port_i,
    output dcache_req_o_t     ld_req_port_o,
    output logic              ld_ex_o,
    // Store req interface
    input  scratchpad_req_i_t st_req_port_i,
    output logic              st_ready_o,
    output logic              st_ex_o,
    // AHB slave req interface
    input  ahb_req_t          ahb_s_req_i,
    output ahb_resp_t         ahb_s_resp_o,

    // SRAM Interface
    output logic                         sram_req_o,
    output logic                         sram_we_o,
    output logic [$clog2(NUM_WORDS)-1:0] sram_addr_o,
    output logic [       DATA_WIDTH-1:0] sram_wdata_o,
    output logic [ (DATA_WIDTH+7)/8-1:0] sram_be_o,
    input  logic [       DATA_WIDTH-1:0] sram_rdata_i
);

  // Arbitrer signals
  logic [DSCR_ARBIT_NUM_IN-1:0] arb_req;
  logic                         arb_gnt;
  dscr_arbit_e                  arb_idx;
  logic                         arb_idx_valid;
  logic ahb_read_ongoing, load_ongoing;
  logic ahb_ack, ahb_store_ready_o, ahb_burst;
  // AHB slave adapter signals
  scratchpad_req_i_t ahb_req_port_o;
  dcache_req_o_t ahb_req_port_i;
  // SRAM signals
  logic sram_ctrl_req;
  logic sram_ctrl_we;
  logic [DATA_WIDTH-1:0] sram_ctrl_wdata;
  logic [(DATA_WIDTH+7)/8-1:0] sram_ctrl_be;
  logic [CVA6Cfg.VLEN-1:0] sram_ctrl_addr;
  logic [DATA_WIDTH-1:0] sram_resp_rdata;
  logic sram_resp_rdata_valid;
  logic sram_resp_gnt;
  logic [CVA6Cfg.VLEN-1:0] sram_resp_addr;
  logic [CVA6Cfg.DcacheIdWidth-1:0] sram_resp_rid, sram_req_id;
  logic st_req_sent;

  // -------------------------------
  // SRAM Controller
  // -------------------------------

  sram_controller #(
      .CVA6Cfg   (CVA6Cfg),
      .DATA_WIDTH(DATA_WIDTH),
      .NUM_WORDS (NUM_WORDS)
  ) i_sram_ctrl (
      .clk_i             (clk_i),
      .rst_ni            (rst_ni),
      // Req interface
      .req_data_req_i    (sram_ctrl_req),
      .req_data_we_i     (sram_ctrl_we),
      .req_data_wdata_i  (sram_ctrl_wdata),
      .req_data_be_i     (sram_ctrl_be),
      .req_address_i     (sram_ctrl_addr),
      .req_data_id_i     (sram_req_id),
      .resp_rdata_o      (sram_resp_rdata),
      .resp_rdata_valid_o(sram_resp_rdata_valid),
      .resp_data_gnt_o   (sram_resp_gnt),
      .resp_address_o    (sram_resp_addr),
      .resp_data_rid_o   (sram_resp_rid),
      // SRAM interface
      .sram_req_o        (sram_req_o),
      .sram_we_o         (sram_we_o),
      .sram_addr_o       (sram_addr_o),
      .sram_wdata_o      (sram_wdata_o),
      .sram_be_o         (sram_be_o),
      .sram_rdata_i      (sram_rdata_i)
  );

  // -------------------------------
  // AHB Slave adapter
  // -------------------------------

  ahb_slave_adapter #(
      .CVA6Cfg(CVA6Cfg),
      .dcache_req_i_t(dcache_req_i_t),
      .dcache_req_o_t(dcache_req_o_t),
      .scratchpad_req_i_t(scratchpad_req_i_t),
      .ahb_resp_t(ahb_resp_t),
      .ahb_req_t(ahb_req_t)
  ) i_ahb_slave_adapter (
      .clk_i       (clk_i),
      .rst_ni      (rst_ni),
      .ahb_s_req_i (ahb_s_req_i),
      .ahb_s_resp_o(ahb_s_resp_o),
      .req_ack_i   (ahb_ack),
      .ahb_burst_o (ahb_burst),
      .req_port_i  (ahb_req_port_i),
      .req_port_o  (ahb_req_port_o)
  );


  // -------------------------------
  // Store ready
  // -------------------------------

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) begin
      st_ready_o <= '0;
      ahb_store_ready_o <= '0;
    end else begin
      if ((arb_idx == DSCR_ARBIT_STORE) && arb_idx_valid && sram_resp_gnt) begin
        st_ready_o <= '1;
      end else begin
        st_ready_o <= '0;
      end
      if ((arb_idx == DSCR_ARBIT_AHB) && arb_idx_valid && sram_resp_gnt) begin
        ahb_store_ready_o <= '1;
      end else begin
        ahb_store_ready_o <= '0;
      end
    end
  end

  // -------------------------------
  // Load / Store / AHB arbit
  // -------------------------------

  assign ld_ex_o = 1'b0;
  assign st_ex_o = 1'b0;

  always_comb begin
    // arb_idx has only 3 possible values
    unique if (arb_idx == DSCR_ARBIT_LOAD && arb_idx_valid) begin
      sram_ctrl_req = ld_req_port_i.data_req && !load_ongoing && !ld_req_port_i.kill_req;
      sram_ctrl_addr            = ld_req_port_i.vaddr;
      sram_ctrl_we              = ld_req_port_i.data_we;
      sram_ctrl_be              = ld_req_port_i.data_be;
      sram_ctrl_wdata           = ld_req_port_i.data_wdata;
      sram_req_id               = ld_req_port_i.data_id;

      ld_req_port_o.data_rdata  = sram_resp_rdata;
      ld_req_port_o.data_gnt    = sram_resp_gnt;
      ld_req_port_o.data_rvalid = sram_resp_rdata_valid;
      ld_req_port_o.data_rid    = sram_resp_rid;
      ld_req_port_o.data_ruser  = '0;

      ahb_req_port_i            = '0;
    end else if (arb_idx == DSCR_ARBIT_STORE && arb_idx_valid) begin
      sram_ctrl_req = st_req_port_i.data_req && !st_req_sent && !st_req_port_i.kill_req;
      sram_ctrl_addr  = st_req_port_i.vaddr;
      sram_ctrl_we    = st_req_port_i.data_we;
      sram_ctrl_be    = st_req_port_i.data_be;
      sram_ctrl_wdata = st_req_port_i.data_wdata;
      sram_req_id     = '0;

      ld_req_port_o   = '0;
      ahb_req_port_i  = '0;
    end else if (arb_idx == DSCR_ARBIT_AHB && arb_idx_valid) begin
      sram_ctrl_req = ahb_req_port_o.data_req;
      sram_ctrl_addr             = ahb_req_port_o.vaddr;
      sram_ctrl_we               = ahb_req_port_o.data_we;
      sram_ctrl_be               = ahb_req_port_o.data_be;
      sram_ctrl_wdata            = ahb_req_port_o.data_wdata;
      sram_req_id                = '0;

      ahb_req_port_i.data_rdata  = sram_resp_rdata;
      ahb_req_port_i.data_gnt    = arb_gnt;
      ahb_req_port_i.data_rvalid = sram_resp_rdata_valid;
      ahb_req_port_i.data_rid    = sram_resp_rid;
      ahb_req_port_i.data_ruser  = '0;

      ld_req_port_o              = '0;
    end else begin
      ld_req_port_o   = '0;
      ahb_req_port_i  = '0;
      sram_ctrl_addr  = '0;
      sram_ctrl_req   = '0;
      sram_ctrl_we    = '0;
      sram_ctrl_be    = '0;
      sram_ctrl_wdata = '0;
      sram_req_id     = '0;
    end
  end

  // arb_idx must be stable when SRAM is sending the read_data, even if the data_req signal is low
  // Therefore the arb_req must stay high one cycle more
  // This concerns only read request, not write
  assign arb_req[DSCR_ARBIT_LOAD] = ld_req_port_i.data_req || load_ongoing;
  assign arb_req[DSCR_ARBIT_STORE] = st_req_port_i.data_req;
  assign arb_req[DSCR_ARBIT_AHB] = ahb_req_port_o.data_req || ahb_read_ongoing;
  assign arb_gnt = (st_ready_o || sram_resp_rdata_valid) && !(ahb_ack && ahb_burst);
  assign ahb_ack = ahb_store_ready_o || (sram_resp_rdata_valid && ahb_read_ongoing);

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) begin
      ahb_read_ongoing <= 1'b0;
      load_ongoing <= 1'b0;
      st_req_sent <= 1'b0;
    end else begin
      if (load_ongoing && sram_resp_rdata_valid) begin
        // End of the request one cycle later
        load_ongoing <= 1'b0;
      end else if (ld_req_port_i.data_req && (arb_idx == DSCR_ARBIT_LOAD)) begin
        // A load request is ongoing if the data_req is high and the load has been chosen by the arbiter
        load_ongoing <= ~ld_req_port_i.kill_req;
      end

      if (ahb_req_port_o.data_req && (arb_idx == DSCR_ARBIT_AHB) && !ahb_req_port_o.data_we) begin
        // A AHB read request is ongoing if the data_req is high and the AHB has been chosen by the arbiter
        ahb_read_ongoing <= 1'b1;
      end else if (ahb_read_ongoing && sram_resp_rdata_valid) begin// End of the request when sram sent the data
        ahb_read_ongoing <= 1'b0;
      end

      if (st_req_sent && st_ready_o) begin
        st_req_sent <= 1'b0;
      end else if (st_req_port_i.data_req && (arb_idx == DSCR_ARBIT_STORE) && sram_resp_gnt) begin
        st_req_sent <= 1'b1;
      end
    end
  end

  rr_arb_tree #(
      .NumIn    (3),
      .DataWidth(1),
      .LockIn   (1'b1)
  ) i_rr_arb_tree (
      .clk_i  (clk_i),
      .rst_ni (rst_ni),
      .flush_i('0),
      .rr_i   ('0),
      .req_i  (arb_req),
      .gnt_o  (),
      .data_i ('0),
      .gnt_i  (arb_gnt),
      .req_o  (arb_idx_valid),
      .data_o (),
      .idx_o  (arb_idx)
  );

endmodule
