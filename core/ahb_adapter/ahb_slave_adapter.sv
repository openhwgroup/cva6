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

    // dreq Interface translation
    input  dcache_req_o_t    req_port_i,
    output scratchpad_req_i_t req_port_o
);

  // AHB signals
  logic hready_d;
  logic [CVA6Cfg.XLEN-1:0] hrdata_d;
  // Req port signals
  logic [CVA6Cfg.VLEN-1:0] vaddr_d, vaddr_q;
  logic [1:0] size_q;
  logic data_we_d, data_req_d;
  logic [CVA6Cfg.XLEN/8-1:0] data_be_d;
  // helper signal
  logic ahb_transfer_req;

  // htrans values
  typedef enum logic [1:0] {
    S_IDLE,
    S_WRITE,
    S_READ,
    S_READ_DATA
  } ahb_ctrl_s_e;
  ahb_ctrl_s_e state_q, state_d;

  assign ahb_transfer_req = (hready_d && (ahb_s_req_i.htrans == AhbTransNonseq || ahb_s_req_i.htrans == AhbTransSeq)) ? 1'b1 : 1'b0;

  // -------------------
  // FSM: Current State
  // -------------------

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_fsm_state
    if (~rst_ni) begin
      state_q <= S_IDLE;
    end else begin
      state_q <= state_d;
    end
  end

  // --------------------
  // FSM: Next State
  // --------------------
  // Busy value of htrans is handled implicitely like an idle state
  //

  always_comb begin : p_fsm_next
    state_d = state_q;

    case (state_q)
      S_IDLE: begin
        state_d = S_IDLE;
        if (ahb_transfer_req) begin
          if (ahb_s_req_i.hwrite) state_d = S_WRITE;
          else state_d = S_READ;
        end
      end

      S_WRITE: begin
        if (req_port_i.data_gnt == 1'b1) state_d = S_IDLE;  // Write completed
      end

      S_READ: begin
        if (req_port_i.data_gnt == 1'b1) state_d = S_READ_DATA;  // Read command accepted
      end

      S_READ_DATA: begin
        if ((req_port_i.data_rvalid == 1'b1) && ahb_transfer_req) begin  // pipeline transfer
          if (ahb_s_req_i.hwrite) state_d = S_WRITE;
          else state_d = S_READ;
        end else if (req_port_i.data_rvalid == 1'b1) state_d = S_IDLE;  // no pipeline transfer
      end
      // TODO: Assert when IDLE or NONSEQ for a non undefined length burst
      default: state_d = S_IDLE;
    endcase
  end

  // --------------------------------
  // FSM: Outputs for AHB interface
  // --------------------------------

  assign ahb_s_resp_o.hrdata = hrdata_d;
  assign ahb_s_resp_o.hready = hready_d;
  assign ahb_s_resp_o.hresp  = 1'b0;  // Exception not yet supported, no errors are sent to AHB BUS

  always_comb begin : p_ahb_outputs
    hrdata_d = '0;

    case (state_q)
      S_IDLE: begin
        hready_d = 1'b1;
      end
      S_READ: begin
        hready_d = 1'b0;
      end
      S_READ_DATA: begin
        hready_d = req_port_i.data_rvalid;
        if (req_port_i.data_rvalid) hrdata_d = req_port_i.data_rdata;
      end
      S_WRITE: begin
        hready_d = 1'b0;
      end
      default: ;
    endcase
  end

  // --------------------------------
  // FSM: Outputs for DREQ interface
  // --------------------------------

  assign req_port_o.vaddr      = vaddr_q;
  assign req_port_o.data_wdata = ahb_s_req_i.hwdata;
  assign req_port_o.data_req   = data_req_d;
  assign req_port_o.data_we    = data_we_d;
  assign req_port_o.data_be    = data_be_d;
  assign req_port_o.data_size  = size_q;
  assign req_port_o.data_id    = '0;  // Not supported: next req is sent when previous one is done
  assign req_port_o.kill_req   = '0;  // Not supported: AHB master cannot kill a req

  always_comb begin : p_dreq_outputs
    data_req_d = 1'b0;
    data_we_d  = 1'b0;

    case (state_q)
      S_IDLE: ;

      S_WRITE: begin
        data_req_d = 1'b1;
        data_we_d  = 1'b1;
      end

      S_READ: begin
        data_req_d = 1'b1;
      end

      S_READ_DATA: begin
        data_req_d = 1'b0;
      end
      default: ;
    endcase
  end

  always_comb begin : p_data_be_gen
    if (ahb_s_req_i.hwrite) begin
      if (ahb_s_req_i.hsize[1:0] == 3'b000) data_be_d = 4'b0001;
      else if (ahb_s_req_i.hsize[1:0] == 3'b001) data_be_d = 4'b0011;
      else if (ahb_s_req_i.hsize[1:0] == 3'b010) data_be_d = 4'b1111;
      else data_be_d = 4'b1111;
    end else data_be_d = 4'h0;
  end

  // ----------------------------
  // Req port register process
  // ----------------------------

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_req_port_regs
    if (~rst_ni) begin
      vaddr_q <= '0;
      size_q  <= '0;
    end else begin
      if (ahb_transfer_req) begin
        vaddr_q <= ahb_s_req_i.haddr;
        size_q  <= ahb_s_req_i.hsize[1:0];
      end
    end
  end

endmodule
