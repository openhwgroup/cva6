/*
 *  Copyright 2023 CEA*
 *  *Commissariat a l'Energie Atomique et aux Energies Alternatives (CEA)
 *
 *  SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
 *
 *  Licensed under the Solderpad Hardware License v 2.1 (the “License”); you
 *  may not use this file except in compliance with the License, or, at your
 *  option, the Apache License version 2.0. You may obtain a copy of the
 *  License at
 *
 *  https://solderpad.org/licenses/SHL-2.1/
 *
 *  Unless required by applicable law or agreed to in writing, any work
 *  distributed under the License is distributed on an “AS IS” BASIS, WITHOUT
 *  WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
 *  License for the specific language governing permissions and limitations
 *  under the License.
 */
/*
 *  Authors       : Cesar Fuguet
 *  Creation Date : June, 2022
 *  Description   : Dcache Memory Reponse Demultiplexer
 *  History       :
 */
module hpdcache_mem_resp_demux
//  Parameters
//  {{{
#(
  parameter int         N  = 0,
  parameter type resp_t    = logic,
  parameter type resp_id_t = logic,

  localparam int RT_DEPTH  = (1 << $bits(resp_id_t)),
  localparam type rt_t     = resp_id_t [RT_DEPTH-1:0]
)
//  }}}

//  Ports
//  {{{
(
  input  logic           clk_i,
  input  logic           rst_ni,

  output logic           mem_resp_ready_o,
  input  logic           mem_resp_valid_i,
  input  resp_id_t       mem_resp_id_i,
  input  resp_t          mem_resp_i,

  input  logic           mem_resp_ready_i [N-1:0],
  output logic           mem_resp_valid_o [N-1:0],
  output resp_t          mem_resp_o       [N-1:0],

  input  rt_t            mem_resp_rt_i
);
//  }}}

  typedef logic [$clog2(N)-1:0] sel_t;

  logic    [N-1:0] mem_resp_demux_valid;
  resp_t   [N-1:0] mem_resp_demux;
  logic    [N-1:0] mem_resp_demux_ready;
  sel_t            mem_resp_demux_sel;

  //  Route the response according to the response ID and the routing table
  assign mem_resp_demux_sel = mem_resp_rt_i[int'(mem_resp_id_i)];

  //  Forward the response to the corresponding output port
  hpdcache_demux #(
      .NOUTPUT        (N),
      .DATA_WIDTH     (1),
      .ONE_HOT_SEL    (0)
  ) i_resp_valid_demux (
      .data_i         (mem_resp_valid_i),
      .sel_i          (mem_resp_demux_sel),
      .data_o         (mem_resp_demux_valid)
  );

  hpdcache_demux #(
      .NOUTPUT        (N),
      .DATA_WIDTH     ($bits(resp_t)),
      .ONE_HOT_SEL    (0)
  ) i_resp_demux (
      .data_i         (mem_resp_i),
      .sel_i          (mem_resp_demux_sel),
      .data_o         (mem_resp_demux)
  );

  hpdcache_mux #(
      .NINPUT         (N),
      .DATA_WIDTH     (1),
      .ONE_HOT_SEL    (0)
  ) i_resp_ready_mux (
      .data_i         (mem_resp_demux_ready),
      .sel_i          (mem_resp_demux_sel),
      .data_o         (mem_resp_ready_o)
  );

  //  Pack/unpack responses
  generate
      for (genvar gen_i = 0; gen_i < int'(N); gen_i++) begin : pack_unpack_resp_gen
        assign mem_resp_valid_o      [gen_i] = mem_resp_demux_valid [gen_i];
        assign mem_resp_o            [gen_i] = mem_resp_demux       [gen_i];
        assign mem_resp_demux_ready  [gen_i] = mem_resp_ready_i     [gen_i];
      end
  endgenerate

endmodule : hpdcache_mem_resp_demux
