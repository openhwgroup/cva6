// Copyright 2021 Thales DIS design services SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Guillaume Chauvon (guillaume.chauvon@thalesgroup.com)


module cvxif_example_coprocessor import cvxif_pkg::*;
                                 import instruction_pkg::*;(
    input   logic                   clk_i,                      // Clock
    input   logic                   rst_ni,                    // Asynchronous reset active low
    //Compressed interface
    input   logic                   x_compressed_valid_i,
    output  logic                   x_compressed_ready_o,
    input   x_compressed_req_t      x_compressed_req_i,
    output  x_compressed_resp_t     x_compressed_resp_o,
    //Issue interface
    input   logic                   x_issue_valid_i,
    output  logic                   x_issue_ready_o,
    input   x_issue_req_t           x_issue_req_i,
    output  x_issue_resp_t          x_issue_resp_o,
    //Commit interface
    input   logic                   x_commit_valid_i,
    input   x_commit_t              x_commit_i,
    //Memory interface
    output  logic                   x_mem_valid_o,
    input   logic                   x_mem_ready_i,
    output  x_mem_req_t             x_mem_req_o,
    input   x_mem_resp_t            x_mem_resp_i,
    //Memory result interface
    input   logic                   x_mem_result_valid_i,
    input   x_mem_result_t          x_mem_result_i,
    //Result interface
    output  logic                   x_result_valid_o,
    input   logic                   x_result_ready_i,
    output  x_result_t              x_result_o
);

  //Compressed interface
  assign x_compressed_ready_o       = '0;
  assign x_compressed_resp_o.instr  = '0;
  assign x_compressed_resp_o.mode   = '0;
  assign x_compressed_resp_o.accept = '0;
  
    
  predecoder #(
    .NumInstr     ( instruction_pkg::NumInstr      ),
    .OffloadInstr ( instruction_pkg::OffloadInstr  )
  ) predecoder_i (
    .x_issue_req_i    ( x_issue_req_i   ),
    .x_issue_resp_o   ( x_issue_resp_o  )
  );
  
 logic fifo_valid;
 logic instr_push, instr_pop;
  x_issue_req_t  req;


  assign instr_push = x_issue_resp_o.accept ? 1 : 0 ;
  assign instr_pop = (x_commit_i.x_commit_kill && x_commit_valid_i) || x_result_valid_o;
  assign x_issue_ready_o = ~fifo_valid; 


  stream_fifo #(
      .FALL_THROUGH  (1), //data_o ready and pop in the same cycle
      .DATA_WIDTH    (64),
      .DEPTH         (1),
      .T          (x_issue_req_t)
    ) fifo_commit_i (
    .clk_i     ( clk_i   ),
    .rst_ni    ( rst_ni  ),
    .flush_i   ( 1'b0    ),
    .testmode_i( 1'b0    ),
    .usage_o   (         ),

    .data_i   ( x_issue_req_i     ),
    .valid_i  ( instr_push        ),
    .ready_o  (    ),

    .data_o   ( req  ),
    .valid_o  ( fifo_valid        ),
    .ready_i  ( instr_pop         )
  );

  logic [3:0] c;
  counter #(
    .WIDTH(4)
  )counter_i(
    .clk_i      ( clk_i),
    .rst_ni     ( rst_ni),
    .clear_i    ( ~x_commit_i.x_commit_kill && x_commit_valid_i),
    .en_i       ( 1),
    .load_i     ( ),
    .down_i     ( ),
    .d_i        ( ),
    .q_o        ( c),
    .overflow_o ( )
  );

  always_comb begin
    x_result_valid_o    = (c == x_result_o.data[3:0]) && fifo_valid ? 1 : 0;
    x_result_o.id       = req.id;
    x_result_o.data     = req.rs[0] + req.rs[1] + req.rs[2];
    x_result_o.rd       = 17;
    x_result_o.we       = 0;
    x_result_o.exc      = 0;
    x_result_o.exccode  = 0;
  end

  endmodule
