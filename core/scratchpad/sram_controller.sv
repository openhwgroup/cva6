//-----------------------------------------------------------------------------
// Copyright 2024 Robert Bosch GmbH
//
// SPDX-License-Identifier: SHL-0.51
//
// Original Author: Coralie Allioux - Robert Bosch France SAS
//-----------------------------------------------------------------------------

module sram_controller
  import ariane_pkg::*;
#(
    parameter config_pkg::cva6_cfg_t CVA6Cfg = config_pkg::cva6_cfg_empty,
    parameter int unsigned DATA_WIDTH = 64,
    parameter int unsigned NUM_WORDS = 1024,  // Should not exceed the capacity of the CPU
    parameter int unsigned NUM_WAIT_STATE = 0  // between 0 and 7 cycles, NOT SUPPORTED YET
) (
    input logic clk_i,
    input logic rst_ni,

    // Req interface
    input logic                             req_data_req_i,
    input logic                             req_data_we_i,
    input logic [           DATA_WIDTH-1:0] req_data_wdata_i,
    input logic [     (CVA6Cfg.XLEN/8)-1:0] req_data_be_i,
    input logic [         CVA6Cfg.VLEN-1:0] req_address_i,
    input logic [CVA6Cfg.DcacheIdWidth-1:0] req_data_id_i,

    output logic [           DATA_WIDTH-1:0] resp_rdata_o,
    output logic                             resp_rdata_valid_o,
    output logic                             resp_data_gnt_o,
    output logic [         CVA6Cfg.VLEN-1:0] resp_address_o,
    output logic [CVA6Cfg.DcacheIdWidth-1:0] resp_data_rid_o,

    // SRAM Interface
    output logic                         sram_req_o,
    output logic                         sram_we_o,
    output logic [$clog2(NUM_WORDS)-1:0] sram_addr_o,
    output logic [       DATA_WIDTH-1:0] sram_wdata_o,
    output logic [ (DATA_WIDTH+7)/8-1:0] sram_be_o,
    input  logic [       DATA_WIDTH-1:0] sram_rdata_i
);

  typedef enum logic [1:0] {
    IDLE,
    WRITE,
    READ
  } state_e;

  state_e state_d, state_q;

  // Direct assign signals
  // CVA6Cfg.VLEN should not be lower than $clog2(NUM_WORDS)
  // Shift address: memory in word, not in byte
  assign sram_addr_o = $clog2(NUM_WORDS)'(req_address_i >> 2);

  // TODO: generalize for NUM_WAIT_STATE > 1
  if (NUM_WAIT_STATE == 1) begin : gen_fsm_wait_state

    always_ff @(posedge clk_i or negedge rst_ni) begin : next_state_p
      if (~rst_ni) begin
        state_q <= IDLE;
      end else begin
        state_q <= state_d;
      end
    end

    always_comb begin : transition_p
      state_d = state_q;

      case (state_q)
        IDLE: begin
          // If a new req and this req is not killed
          if (req_data_req_i) begin
            if (req_data_we_i) state_d = WRITE;
            else state_d = READ;
          end else begin
            state_d = IDLE;
          end
        end

        WRITE: state_d = IDLE;

        READ: state_d = IDLE;

        default: state_d = IDLE;
      endcase
    end

    always_comb begin : outputs_p
      resp_data_gnt_o = 1'b0;
      sram_req_o = 1'b0;
      sram_we_o = 1'b0;
      sram_wdata_o = '0;
      sram_be_o = '0;
      resp_rdata_o = '0;
      resp_rdata_valid_o = 1'b0;

      case (state_q)
        IDLE: begin
          if (req_data_req_i) begin
            resp_data_gnt_o = '1;
            sram_req_o = '1;
            sram_we_o = req_data_we_i;
            sram_be_o = req_data_be_i;

            if (req_data_we_i) sram_wdata_o = req_data_wdata_i;
          end
        end

        WRITE: ;

        READ: begin
          resp_rdata_valid_o = 1'b1;
          resp_rdata_o = sram_rdata_i;
        end

        default: ;
      endcase

    end
  end else begin : gen_no_wait_state
    assign sram_req_o   = req_data_req_i;
    assign sram_we_o    = req_data_we_i;
    assign sram_wdata_o = req_data_wdata_i;
    assign sram_be_o    = req_data_be_i;

    assign resp_rdata_o = sram_rdata_i;
    assign resp_data_gnt_o = req_data_req_i; // with no wait state gnt can be combinatorial

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (~rst_ni) begin
        resp_rdata_valid_o <= 1'b0;
      end else begin
        if (req_data_req_i && !req_data_we_i) begin
          resp_rdata_valid_o <= 1'b1;
        end else if ((~req_data_req_i || req_data_we_i) && resp_rdata_valid_o) begin
          resp_rdata_valid_o <= 1'b0;
        end
      end
    end
  end

  // Register VADDR given in input for branch prediction usage (in frontend)
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (~rst_ni) begin
      resp_address_o  <= 1'b0;
      resp_data_rid_o <= 1'b0;
    end else begin
      if (req_data_req_i & resp_data_gnt_o) begin
        resp_address_o  <= req_address_i;
        resp_data_rid_o <= req_data_id_i;
      end
    end
  end
endmodule
