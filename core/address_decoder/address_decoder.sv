//-----------------------------------------------------------------------------
// Copyright 2024 Robert Bosch GmbH
//
// SPDX-License-Identifier: SHL-0.51
//
// Original Author: Coralie Allioux - Robert Bosch France SAS
//-----------------------------------------------------------------------------

module address_decoder import address_decoder_pkg::*;#(
  parameter config_pkg::cva6_cfg_t CVA6Cfg = config_pkg::cva6_cfg_empty,
  parameter type exception_t = logic,
  parameter ADDR_WIDTH = 32
) (
  input  logic                   clk_i,
  input  logic                   rst_ni,

  input  logic                   addr_valid_i,    // Input address is valid
  input  logic [ADDR_WIDTH-1:0]  addr_i,          // Address to be decoded

  input  logic                   dscr_en_i,       // From CSR
  input  logic                   iscr_en_i,       // From CSR
  input  logic                   ahb_periph_en_i, // From CSR
  
  input  logic [CVA6Cfg.XLEN-1:0] exception_code_i,
  
  output exception_t             ex_o,
  output addr_dec_mode_e         select_mem_o
);

  logic match_any_ahbperiph_region;
  logic match_dscr_region;
  logic match_iscr_region;
  addr_dec_mode_e select_mem_n, select_mem_q;

  assign match_dscr_region          = config_pkg::is_inside_data_scratchpad(CVA6Cfg, {{64-ADDR_WIDTH{1'b0}}, addr_i});
  assign match_iscr_region          = config_pkg::is_inside_instruction_scratchpad(CVA6Cfg, {{64-ADDR_WIDTH{1'b0}}, addr_i});
  assign match_any_ahbperiph_region = config_pkg::is_inside_ahbperiph_regions(CVA6Cfg, {{64-ADDR_WIDTH{1'b0}}, addr_i});

  assign select_mem_o = select_mem_n;

  always_comb begin : select_mem_p
    ex_o = '0;
    select_mem_n = select_mem_q;
    if (addr_valid_i) begin
      unique if (match_dscr_region) begin
        // Equal to 0 only if DataScrPresent is set
        select_mem_n = DECODER_MODE_DSCR;
        if (!dscr_en_i) begin
          ex_o = {exception_code_i, CVA6Cfg.XLEN'(addr_i), 1'b1};
        end
      end else if (match_iscr_region) begin
        // Equal to 0 only if InstrScrPresent is set
        select_mem_n = DECODER_MODE_ISCR;
        if (!iscr_en_i) begin
          ex_o = {exception_code_i, CVA6Cfg.XLEN'(addr_i), 1'b1};
        end
      end else if (match_any_ahbperiph_region) begin
        select_mem_n = DECODER_MODE_AHB_PERIPH;
        if (!ahb_periph_en_i) begin
          ex_o = {exception_code_i, CVA6Cfg.XLEN'(addr_i), 1'b1};
        end
      end else begin
        select_mem_n = DECODER_MODE_CACHE;
      end
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : select_mem_q_p
    if (~rst_ni) begin
      select_mem_q <= DECODER_MODE_CACHE;
    end else begin
      select_mem_q <= select_mem_n;
    end
  end
  
endmodule