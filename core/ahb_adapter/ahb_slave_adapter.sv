//-----------------------------------------------------------------------------
// Copyright 2024 Robert Bosch GmbH
//
// SPDX-License-Identifier: SHL-0.51
//
// Original Author: Coralie Allioux - Robert Bosch France SAS
//-----------------------------------------------------------------------------

module ahb_slave_adapter
  import ariane_pkg::*;
  import ahb_pkg::*;
#(
    parameter config_pkg::cva6_cfg_t CVA6Cfg = config_pkg::cva6_cfg_empty,
    parameter type dcache_req_i_t = logic,
    parameter type dcache_req_o_t = logic,
    parameter type scratchpad_req_i_t = logic,
    parameter type ahb_resp_t = logic,
    parameter type ahb_req_t = logic
) (
    // AHB Slave Interface
    input  logic      clk_i,
    input  logic      rst_ni,
    output ahb_resp_t ahb_s_resp_o,
    input  ahb_req_t  ahb_s_req_i,

    // Request from AHB acknowledged
    input logic req_ack_i,
    output logic ahb_burst_o,

    // dreq Interface translation
    input  dcache_req_o_t    req_port_i,
    output scratchpad_req_i_t req_port_o
);

  // AHB signals
  logic hready_d;
  logic hresp_d;
  logic [CVA6Cfg.XLEN-1:0] hrdata_d;
  // Req port signals
  logic [CVA6Cfg.VLEN-1:0] vaddr_d, vaddr_q;
  logic [CVA6Cfg.XLEN-1:0] wdata_d, wdata_q;
  logic [1:0] size_d, size_q;
  logic data_be_d, data_we_d, data_req_d;

  // htrans values
  typedef enum logic [2:0] {
    S_IDLE,
    S_BUSY,
    S_NONSEQ_READ,
    S_NONSEQ_WRITE,
    S_SEQ_READ,
    S_SEQ_WRITE
  } ahb_ctrl_e;
  ahb_ctrl_e state_q, state_d;

  // -------------------
  // FSM: Current State
  // -------------------

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_next_state
    if (~rst_ni) begin
      state_q <= S_IDLE;
    end else begin
      state_q <= state_d;
    end
  end

  // --------------------
  // FSM: Next State
  // --------------------

  always_comb begin : p_current_state
    state_d = state_q;

    case (state_q)
      S_IDLE: begin
        state_d = S_IDLE;
        if (ahb_s_req_i.htrans == AHB_TRANS_NONSEQ) begin
          if (ahb_s_req_i.hwrite) state_d = S_NONSEQ_WRITE;
          else state_d = S_NONSEQ_READ;
        end
      end

      S_NONSEQ_READ, S_NONSEQ_WRITE: begin
        // BUSY should not happen when NONSEQ ongoing
        // Default is then IDLE (no transfer after current one)
        state_d = AHB_TRANS_IDLE;

        // If current request not served, should stay in NONSEQ
        if (~req_ack_i) state_d = state_q;
        // Stay in NONSEQ if one is following
        else if (ahb_s_req_i.htrans == AHB_TRANS_NONSEQ) begin
          if (ahb_s_req_i.hwrite) state_d = S_NONSEQ_WRITE;
          else state_d = S_NONSEQ_READ;
        end
        // Go to SEQ if this becomes a BURST
        else if (ahb_s_req_i.htrans == AHB_TRANS_SEQ) begin
          if (ahb_s_req_i.hwrite) state_d = S_SEQ_WRITE;
          else state_d = S_SEQ_READ;
        end
      end

      S_SEQ_READ, S_SEQ_WRITE: begin
        // BURST is conneced to every state
        // Change state accoding to next transfer type
        state_d = AHB_TRANS_IDLE;
        if (ahb_s_req_i.htrans == AHB_TRANS_SEQ) begin
          if (ahb_s_req_i.hwrite) state_d = S_SEQ_WRITE;
          else state_d = S_SEQ_READ;
        end
        else if (ahb_s_req_i.htrans == AHB_TRANS_BUSY) state_d = S_BUSY;
        else if (ahb_s_req_i.htrans == AHB_TRANS_NONSEQ) begin
          if (ahb_s_req_i.hwrite) state_d = S_NONSEQ_WRITE;
          else state_d = S_NONSEQ_READ;
        end
      end

      S_BUSY: begin
        // BUSY can then go IDLE and SINGLE only if the current burst size is undefined
        if (ahb_s_req_i.htrans == AHB_TRANS_BUSY) state_d = S_BUSY;
        else if (ahb_s_req_i.htrans == AHB_TRANS_SEQ) begin
          if (ahb_s_req_i.hwrite) state_d = S_SEQ_WRITE;
          else state_d = S_SEQ_READ;
        end
        else if (ahb_s_req_i.hburst == AHB_BURST_INCR) begin
          if (ahb_s_req_i.htrans == AHB_TRANS_IDLE) state_d = S_IDLE;
          else if (ahb_s_req_i.htrans == AHB_TRANS_NONSEQ) begin
          if (ahb_s_req_i.hwrite) state_d = S_NONSEQ_WRITE;
          else state_d = S_NONSEQ_READ;
        end
        end

        // TODO: Assert when IDLE or NONSEQ for a non undefined length burst
      end

      default: state_d = S_IDLE;
    endcase
  end

  // --------------------------------
  // FSM: Outputs for AHB interface
  // --------------------------------

  assign ahb_s_resp_o.hrdata = hrdata_d;
  assign ahb_s_resp_o.hready = hready_d;
  assign ahb_s_resp_o.hresp  = hresp_d;

  always_comb begin : p_ahb_outputs
    hready_d = 1'b1;
    hresp_d  = 1'b0; // Exception not yet supported, no errors are sent to AHB BUS
    hrdata_d = '0;

    case (state_q)
      S_NONSEQ_READ, S_SEQ_READ: begin
        if (req_port_i.data_rvalid) hrdata_d = req_port_i.data_rdata;
        else hready_d = 1'b0;
      end

      S_NONSEQ_WRITE, S_SEQ_WRITE: begin
        if (~req_ack_i) hready_d = 1'b0;
      end

      // IDLE and BUSY are in default
      default: ;
    endcase
  end

  // --------------------------------
  // FSM: Outputs for DREQ interface
  // --------------------------------

  always_comb begin : p_dreq_outputs
    vaddr_d    = vaddr_q;
    wdata_d    = wdata_q;
    data_req_d = 1'b0;
    data_we_d  = 1'b0;
    data_be_d  = '0; // TODO: Determine if should be set depending of size or not?
    size_d     = size_q;
    ahb_burst_o = 1'b0;

    case (state_q)
      S_IDLE: begin
        // Next state is NONSEQ, then a new request after IDLE juste arrived
        // Can send request to ask ARBITER
        // Nothing to do if request is write... should wait for wdata before sending)
        if (state_d == S_NONSEQ_READ) begin
          vaddr_d    = CVA6Cfg.VLEN'(ahb_s_req_i.haddr);
          data_req_d = 1'b1;
          size_d     = ahb_s_req_i.hsize[1:0];
        end
      end

      S_NONSEQ_READ, S_SEQ_READ: begin
        if (req_ack_i && (state_d == S_NONSEQ_READ || state_d == S_SEQ_READ)) begin
          vaddr_d    = CVA6Cfg.VLEN'(ahb_s_req_i.haddr);
          data_req_d = 1'b1;
          size_d     = ahb_s_req_i.hsize[1:0];
        end else if (~req_ack_i) data_req_d = 1'b1;

        if (state_d == S_SEQ_READ) ahb_burst_o = 1'b1;
      end

      S_NONSEQ_WRITE, S_SEQ_WRITE: begin
        data_we_d = 1'b1;
        if (req_ack_i && (state_d == S_NONSEQ_WRITE || state_d == S_SEQ_WRITE)) data_req_d = 1'b1;

        if (state_d == S_SEQ_WRITE) ahb_burst_o = 1'b1;
      end

      S_BUSY: begin
      end

      default: ;
    endcase
  end

  assign req_port_o.vaddr      = vaddr_d;
  assign req_port_o.data_wdata = wdata_d;
  assign req_port_o.data_req   = data_req_d;
  assign req_port_o.data_we    = data_we_d;
  assign req_port_o.data_be    = data_be_d;
  assign req_port_o.data_size  = size_d;
  assign req_port_o.data_id    = '0; // Not supported: next req is sent when previous one is done
  assign req_port_o.kill_req   = '0; // Not supported: AHB master cannot kill a req

  // ----------------------------
  // Req port register process
  // ----------------------------

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_req_port_regs
    if (~rst_ni) begin
      vaddr_q <= '0;
      wdata_q <= '0;
      size_q  <= '0;
    end else begin
      // TODO: Find enable
      if (req_ack_i || ((state_d == S_NONSEQ_READ || state_d == S_NONSEQ_WRITE) && state_q == S_IDLE)) begin
        vaddr_q <= vaddr_d;
        size_q  <= size_d;
      end
      if (state_q == S_NONSEQ_WRITE || state_q == S_SEQ_WRITE) wdata_q <= wdata_d;
    end
  end

endmodule
