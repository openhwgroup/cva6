//-----------------------------------------------------------------------------
// Copyright 2024 Robert Bosch GmbH
//
// SPDX-License-Identifier: SHL-0.51
//
// Original Author: Coralie Allioux - Robert Bosch France SAS
//-----------------------------------------------------------------------------

module ahb_master_adapter
  import ariane_pkg::*;
#(
    parameter config_pkg::cva6_cfg_t CVA6Cfg = config_pkg::cva6_cfg_empty,
    parameter type dcache_req_o_t = logic,
    parameter type scratchpad_req_i_t = logic,
    parameter type ahb_resp_t = logic,
    parameter type ahb_req_t = logic
) (
    // AHB Master Interface
    input  logic      clk_i,
    input  logic      rst_ni,
    input  ahb_resp_t ahb_p_resp_i,
    output ahb_req_t  ahb_p_req_o,

    // dreq Interface translation
    input  scratchpad_req_i_t req_port_i,
    output dcache_req_o_t     req_port_o,

    output logic adapter_transfer_complete,

    output logic ex_o
);

  logic read_req_ongoing;
  logic req_not_ready, new_req_not_ready_q;

  logic hwrite_d, hwrite_q;
  logic [CVA6Cfg.PLEN-1:0] haddr_d, haddr_q, req_addr_plen;
  ahb_pkg::size_t hsize_d, hsize_q;
  ahb_pkg::trans_t htrans_d;
  logic [CVA6Cfg.XLEN-1:0] hwdata_q, hwdata_q2;

  logic [CVA6Cfg.DcacheIdWidth-1:0] data_rid_q;

  logic kill_req, kill_req_q;

  logic transfer_req;

  typedef enum {
    IDLE,
    SINGLE,
    PIPELINE_STALL,
    SINGLE_STALL
  } ahb_ctrl_e;
  ahb_ctrl_e ahb_ctrl_fsm;

  // Not supported
  assign req_port_o.data_ruser = '0;

  if (CVA6Cfg.VLEN >= CVA6Cfg.PLEN) begin : gen_addr_plen_smaller_vlen
    assign req_addr_plen = req_port_i.vaddr[CVA6Cfg.PLEN-1:0];
  end else begin : gen_addr_plen_greater_vlen
    assign req_addr_plen = {{(CVA6Cfg.PLEN - CVA6Cfg.VLEN) {1'b0}}, req_port_i.vaddr};
  end

  assign req_not_ready = req_port_i.data_req && !ahb_p_resp_i.hready;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) begin
      new_req_not_ready_q <= 1'b0;
    end else begin
      if (req_not_ready && !new_req_not_ready_q) begin
        new_req_not_ready_q <= 1'b1;
      end else if (!req_not_ready && new_req_not_ready_q) begin
        new_req_not_ready_q <= '0;
      end
    end
  end

  // ---------------
  // AHB FSM
  // ---------------
  // TODO: need assert to check PIPELINE_STALL and data_req never happens at the
  // same time
  //
  assign transfer_req = req_port_i.data_req && req_port_o.data_gnt;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) begin
      ahb_ctrl_fsm <= IDLE;
    end else begin
      case (ahb_ctrl_fsm)
        IDLE: begin
          if (req_port_i.data_req) begin
            ahb_ctrl_fsm <= SINGLE;
          end
        end
        SINGLE: begin
          // ongoing transaction completed and got new command
          if (transfer_req && ahb_p_resp_i.hready) begin
            ahb_ctrl_fsm <= SINGLE;
            // new transaction but previous one still ongoing
          end else if (transfer_req && ~ahb_p_resp_i.hready) begin
            ahb_ctrl_fsm <= PIPELINE_STALL;
            // ongoing transaction completed, no new transaction
          end else if (!transfer_req && ahb_p_resp_i.hready) begin
            ahb_ctrl_fsm <= IDLE;
            // ongoing transaction stalling
          end else begin
            ahb_ctrl_fsm <= SINGLE_STALL;
          end
        end
        SINGLE_STALL: begin
          // ongoing transaction completed and got new command
          if (transfer_req && ahb_p_resp_i.hready) begin
            ahb_ctrl_fsm <= SINGLE;
            // new transaction but previous one still ongoing
          end else if (transfer_req && ~ahb_p_resp_i.hready) begin
            ahb_ctrl_fsm <= PIPELINE_STALL;
            // ongoing transaction completed, no new transaction
          end else if (!transfer_req && ahb_p_resp_i.hready) begin
            ahb_ctrl_fsm <= IDLE;
            // ongoing transaction stalling
          end else begin
            ahb_ctrl_fsm <= SINGLE_STALL;
          end
        end
        PIPELINE_STALL: begin
          // ongoing transaction completed
          if (ahb_p_resp_i.hready) begin
            ahb_ctrl_fsm <= SINGLE;
          end else begin
            ahb_ctrl_fsm <= PIPELINE_STALL;
          end
        end
        // should never occur
        default: begin
          ahb_ctrl_fsm <= IDLE;
        end
      endcase
    end
  end



  // ---------------
  // AHB Interface
  // ---------------
  // req_port to ahb: Directly mapped signals
  assign ahb_p_req_o.haddr  = haddr_d;
  assign ahb_p_req_o.hsize  = hsize_d;
  assign ahb_p_req_o.hwrite = hwrite_d;
  assign ahb_p_req_o.htrans = htrans_d;
  // The only one that is connected to q: cannot be sent in combinatorial
  assign ahb_p_req_o.hwdata = hwdata_q;
  // Set static values to Hburst and Hprot
  assign ahb_p_req_o.hburst = '0;
  assign ahb_p_req_o.hprot  = ahb_pkg::AHBProtWidth'('b0011);

  always_comb begin
    htrans_d = '0;
    haddr_d  = '0;
    hsize_d  = '0;
    hwrite_d = '0;
    if (ahb_ctrl_fsm == PIPELINE_STALL) begin  //send the registered value during stall
      htrans_d = ahb_pkg::AHB_TRANS_NONSEQ;
      haddr_d  = haddr_q;
      hsize_d  = hsize_q;
      hwrite_d = hwrite_q;
    end else begin  // send the value directly otherwise
      haddr_d  = req_port_i.vaddr;
      hsize_d  = {1'b0, req_port_i.data_size};
      hwrite_d = req_port_i.data_we;
      if (req_port_i.data_req) begin
        htrans_d = ahb_pkg::AHB_TRANS_NONSEQ;
      end else begin
        htrans_d = ahb_pkg::AHB_TRANS_IDLE;
      end
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) begin
      hwdata_q  <= '0;
      hwdata_q2 <= '0;
      haddr_q   <= '0;
      hsize_q   <= '0;
      hwrite_q  <= '0;
    end else begin
      if (req_port_i.data_we) begin
        hwdata_q  <= req_port_i.data_wdata;
        hwdata_q2 <= hwdata_q;
      end else if (ahb_p_resp_i.hready) begin
        hwdata_q  <= '0;
        hwdata_q2 <= hwdata_q;
      end
      if (ahb_ctrl_fsm == SINGLE_STALL || ahb_ctrl_fsm == PIPELINE_STALL) begin
        // If slave not ready, then save in registers request information, in case not stable
        haddr_q  <= req_port_i.vaddr;
        hsize_q  <= {1'b0, req_port_i.data_size};
        hwrite_q <= req_port_i.data_we;
      end else if (!req_not_ready && new_req_not_ready_q) begin
        // Request ended
        haddr_q  <= '0;
        hsize_q  <= '0;
        hwrite_q <= '0;
      end else begin
        haddr_q  <= '0;
        hsize_q  <= '0;
        hwrite_q <= '0;
      end
      if (req_not_ready && !new_req_not_ready_q) begin
        // If slave not ready, then save in registers request information, in case not stable
        haddr_q  <= req_port_i.vaddr;
        hsize_q  <= {1'b0, req_port_i.data_size};
        hwrite_q <= req_port_i.data_we;
      end else if (!req_not_ready && new_req_not_ready_q) begin
        // Request ended
        haddr_q  <= '0;
        hsize_q  <= '0;
        hwrite_q <= '0;
      end else begin
        haddr_q  <= '0;
        hsize_q  <= '0;
        hwrite_q <= '0;
      end
    end
  end

  // ----------------
  // DREQ Interface
  // ----------------
  assign req_port_o.data_rdata = ahb_p_resp_i.hrdata;
  assign req_port_o.data_rid   = data_rid_q;
  // data_gnt accept the command
  // only grant one command at a time
  // Note : this will prevent pipelining but is done to support kill signal
  // more complex logic needed to support pipeline and kill
  always_comb begin
    if (req_port_i.data_req && ahb_ctrl_fsm == IDLE) begin
      req_port_o.data_gnt = 1'b1;
    end else begin
      req_port_o.data_gnt = 1'b0;
    end
  end
  always_comb begin
    req_port_o.data_rvalid = 1'b0;
    adapter_transfer_complete = 1'b0;
    if (ahb_ctrl_fsm != IDLE) begin
      req_port_o.data_rvalid = ahb_p_resp_i.hready & !kill_req;
      adapter_transfer_complete = ahb_p_resp_i.hready;
    end
  end

  // data_rvalid ==> hready and hresp
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) begin
      read_req_ongoing <= 1'b0;
      data_rid_q       <= '0;
    end else begin
      if (read_req_ongoing && ahb_p_resp_i.hready && !ahb_p_resp_i.hresp) begin
        read_req_ongoing <= '0;
      end else if (req_port_i.data_req && !req_port_i.data_we) begin
        read_req_ongoing <= 1'b1;
      end

      if (req_port_i.data_req) begin
        data_rid_q <= req_port_i.data_id;
      end
    end
  end
  // ----------------
  // Kill signal
  // ----------------
  // when kill signal is received, must not send the rvalid signal back
  // kill_req is only high 1 cycle, thus must buffer in case the ongoing
  // request is not complete
  assign kill_req = req_port_i.kill_req | kill_req_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) begin
      kill_req_q <= 1'b0;
    end else begin
      // got kill and transfer completion at the same time, no need to buffer
      if (req_port_i.kill_req && adapter_transfer_complete) kill_req_q <= 1'b0;
      // got kill but transfer ongoing, must stay high
      else if (req_port_i.kill_req && !adapter_transfer_complete) kill_req_q <= 1'b1;
      // buffered kill is complete
      else if (kill_req_q && adapter_transfer_complete) kill_req_q <= 1'b0;
    end
  end

  // ----------------
  // Exception
  // ----------------
  // Bus error not yet supported by LSU, thus return 0 and rvalid even on
  // error, keeping the correct error signaling for later
  // assign ex_o = ahb_p_resp_i.hresp & ahb_p_resp_i.hready;
  assign ex_o = 1'b0;

endmodule
