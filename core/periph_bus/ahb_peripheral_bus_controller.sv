//-----------------------------------------------------------------------------
// Copyright 2024 Robert Bosch GmbH
//
// SPDX-License-Identifier: SHL-0.51
//
// Original Author: Coralie Allioux - Robert Bosch France SAS
//-----------------------------------------------------------------------------

module ahb_peripheral_bus_controller
  import ahb_pkg::*;
#(
    parameter config_pkg::cva6_cfg_t CVA6Cfg = config_pkg::cva6_cfg_empty,
    parameter type dcache_req_i_t = logic,
    parameter type dcache_req_o_t = logic,
    parameter type scratchpad_req_i_t = logic,
    parameter type ahb_resp_t = logic,
    parameter type ahb_req_t = logic
) (
    input logic clk_i,  // Clock
    input logic rst_ni,  // Asynchronous reset active low
    // AHB Master Interface
    input ahb_resp_t ahb_p_resp_i,
    output ahb_req_t ahb_p_req_o,

    // LSU (Load Unit) interface
    input  scratchpad_req_i_t ld_req_port_i,
    output dcache_req_o_t     ld_req_port_o,
    output logic              ld_ex_o,
    // LSU (Store Unit) interface
    input  scratchpad_req_i_t st_req_port_i,
    output logic              st_ready_o,
    output logic              st_ex_o
);
  // Arbitrer signals
  localparam int unsigned NumberArbiterInputs = 2;
  typedef enum logic {
    ARBIT_LOAD,
    ARBIT_STORE
  } ahb_arb_e;
  logic [1:0] arb_req, arb_gnt_o;
  ahb_arb_e                arb_idx;
  logic                    arb_req_done;
  logic                    arb_idx_valid;
  scratchpad_req_i_t [1:0] arb_data_i;
  logic load_ongoing, store_ongoing;

  // AHB adapter signals
  scratchpad_req_i_t adapter_req_port_i;
  dcache_req_o_t     adapter_req_port_o;
  logic              adapter_ex_o;
  logic              adapter_transfer_complete;


  // -------------------
  // AHB master adapter
  // -------------------

  ahb_master_adapter #(
      .CVA6Cfg(CVA6Cfg),
      .dcache_req_o_t(dcache_req_o_t),
      .scratchpad_req_i_t(scratchpad_req_i_t),
      .ahb_resp_t(ahb_resp_t),
      .ahb_req_t(ahb_req_t)
  ) i_ahb_master_adapter (
      .clk_i                    (clk_i),
      .rst_ni                   (rst_ni),
      .ahb_p_resp_i             (ahb_p_resp_i),
      .ahb_p_req_o              (ahb_p_req_o),
      .req_port_i               (adapter_req_port_i),
      .req_port_o               (adapter_req_port_o),
      .adapter_transfer_complete(adapter_transfer_complete),
      .ex_o                     (adapter_ex_o)
  );


  // -------------------
  // Load / Store arbit
  // -------------------
  // For both load and store, return data_gnt when command is accepted
  // (respectively as data_gnt and st_ready_o)
  // The load unit is stalled until the data come back (signaled with
  // data_rvalid)
  // The store unit does not wait for a signal to indicate transaction
  // completion, therefore the transaction is considered complete when
  // the command is granted
  // As implemented, no proper AHB pipelining can be achieved
  always_comb begin
    unique if (arb_idx == ARBIT_LOAD && arb_idx_valid) begin
      ld_req_port_o.data_rvalid = adapter_req_port_o.data_rvalid;
      ld_req_port_o.data_rdata  = adapter_req_port_o.data_rdata;
      ld_req_port_o.data_gnt    = adapter_req_port_o.data_gnt;
      ld_req_port_o.data_rid    = '0;
      ld_req_port_o.data_ruser  = '0;
      ld_ex_o                   = adapter_ex_o;
      st_ex_o                   = '0;
      st_ready_o                = '0;
    end else if (arb_idx == ARBIT_STORE && arb_idx_valid) begin
      st_ex_o       = adapter_ex_o;
      ld_req_port_o = '0;
      ld_ex_o       = '0;
      st_ready_o    = adapter_req_port_o.data_gnt;
    end else begin
      st_ex_o       = '0;
      ld_req_port_o = '0;
      ld_ex_o       = '0;
      st_ready_o    = '0;
    end
  end

  // the arbiter sent the grant back when command is accepted, but the arbiter
  // need the req to be active until full completion of the transaction.
  // Therefore ongoing signals needed to keep the arbiter in a known state

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) begin
      load_ongoing <= '0;
    end else begin
      if (ld_req_port_i.data_req && (arb_idx == ARBIT_LOAD)) begin
        // A load request is ongoing if the data_req is high and the load has been chosen by the arbiter
        load_ongoing <= '1;
      end else if (load_ongoing && adapter_transfer_complete) begin
        // End of the request one cycle later
        load_ongoing <= '0;
      end
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) begin
      store_ongoing <= '0;
    end else begin
      if (st_req_port_i.data_req && (arb_idx == ARBIT_STORE)) begin
        // A store request is ongoing if the data_req is high and the store has been chosen by the arbiter
        store_ongoing <= '1;
      end else if (store_ongoing && adapter_transfer_complete) begin
        // End of the request one cycle later
        store_ongoing <= '0;
      end
    end
  end

  assign arb_req[ARBIT_LOAD] = ld_req_port_i.data_req || load_ongoing;
  assign arb_req[ARBIT_STORE] = st_req_port_i.data_req || store_ongoing;
  assign arb_data_i[ARBIT_LOAD] = ld_req_port_i;
  assign arb_data_i[ARBIT_STORE] = st_req_port_i;
  assign arb_req_done = adapter_transfer_complete;

  rr_arb_tree #(
      .NumIn   (NumberArbiterInputs),
      .DataType(scratchpad_req_i_t),
      .LockIn  (1'b1)
  ) i_rr_arb_tree (
      .clk_i  (clk_i),
      .rst_ni (rst_ni),
      .flush_i('0),
      .rr_i   ('0),
      .req_i  (arb_req),
      .gnt_o  (arb_gnt_o),
      .data_i (arb_data_i),
      .gnt_i  (arb_req_done),
      .req_o  (arb_idx_valid),
      .data_o (adapter_req_port_i),
      .idx_o  (arb_idx)
  );

endmodule
