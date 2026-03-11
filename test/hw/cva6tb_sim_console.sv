// Copyright 2026 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Author: Enrico Zelioli <ezelioli@iis.ee.ethz.ch>
//
// Simulation console

`include "common_cells/registers.svh"

module cva6tb_sim_console #(
  parameter type reg_req_t = logic,
  parameter type reg_rsp_t = logic
) (
  input  logic     clk_i,
  input  logic     rst_ni,
  input  reg_req_t reg_req_i,
  output reg_rsp_t reg_rsp_o
);

  string buffer = "";

  assign reg_rsp_o = reg_rsp_t'{
    rdata: '0,
    error: 1'b0,
    ready: 1'b1
  };

  initial begin
    forever @(posedge clk_i) begin
      if (reg_req_i.valid && reg_req_i.write && (reg_req_i.addr[4:0] == 5'h0)) begin
        if (reg_req_i.wdata[7:0] == 8'h0A) begin
          $display("@%t | [CON] %s", $realtime, buffer);
          buffer = "";
        end else begin
          buffer = {buffer, string'(reg_req_i.wdata[7:0])};
        end
      end
    end
  end

endmodule
