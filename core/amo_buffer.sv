// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Florian Zaruba, ETH Zurich
// Date: 20.09.2018
// Description: Buffers AMO requests
// This unit buffers an atomic memory operations for the cache subsyste.
// Furthermore it handles interfacing with the commit stage

module amo_buffer #(
    parameter config_pkg::cva6_cfg_t CVA6Cfg = config_pkg::cva6_cfg_empty,
    parameter type obi_amo_req_t = logic,
    parameter type obi_amo_rsp_t = logic
) (
    input logic clk_i,   // Clock
    input logic rst_ni,  // Asynchronous reset active low
    input logic flush_i, // pipeline flush

    input logic valid_i,  // AMO is valid
    output logic ready_o,  // AMO unit is ready
    input ariane_pkg::amo_t amo_op_i,  // AMO Operation
    input  logic [CVA6Cfg.PLEN-1:0]      paddr_i,            // physical address of store which needs to be placed in the queue
    input logic [CVA6Cfg.XLEN-1:0] data_i,  // data which is placed in the queue
    input logic [1:0] data_size_i,  // type of request we are making (e.g.: bytes to write)
    // D$
    // AMO request - DCACHE
    output obi_amo_req_t obi_amo_req_o,
    // AMO response - DCACHE
    input obi_amo_rsp_t obi_amo_rsp_i,
    // Auxiliary signals
    input logic amo_valid_commit_i,  // We have a vaild AMO in the commit stage
    input logic no_st_pending_i  // there is currently no store pending anymore
);
  logic flush_amo_buffer;
  logic amo_valid;

  typedef struct packed {
    ariane_pkg::amo_t        op;
    logic [CVA6Cfg.PLEN-1:0] paddr;
    logic [CVA6Cfg.XLEN-1:0] data;
    logic [1:0]              size;
  } amo_op_t;

  amo_op_t amo_data_in, amo_data_out;

  assign amo_data_in.op = amo_op_i;
  assign amo_data_in.data = data_i;
  assign amo_data_in.paddr = paddr_i;
  assign amo_data_in.size = data_size_i;

  // validate this request as soon as all stores have drained and the AMO is in the commit stage
  assign obi_amo_req_o.req = no_st_pending_i & amo_valid_commit_i & amo_valid;
  assign obi_amo_req_o.reqpar = !obi_amo_req_o.req;
  assign obi_amo_req_o.a.addr = amo_data_out.paddr;
  assign obi_amo_req_o.a.we = 1'b1;
  assign obi_amo_req_o.a.be = CVA6Cfg.XLEN == 64 ? ariane_pkg::be_gen(
      amo_data_out.paddr[2:0], amo_data_out.size
  ) : ariane_pkg::be_gen_32(
      amo_data_out.paddr[1:0], amo_data_out.size
  );
  assign obi_amo_req_o.a.wdata = amo_data_out.data;
  assign obi_amo_req_o.a.aid = '0;
  assign obi_amo_req_o.a.a_optional.auser = '0;
  assign obi_amo_req_o.a.a_optional.wuser = '0;
  assign obi_amo_req_o.a.a_optional.atop = ariane_pkg::amo_cva6_to_obi(amo_data_out.op);
  assign obi_amo_req_o.a.a_optional.memtype[0] = '0;
  assign obi_amo_req_o.a.a_optional.memtype[1] = config_pkg::is_inside_cacheable_regions(
      CVA6Cfg, {{64 - CVA6Cfg.PLEN{1'b0}}, amo_data_out.paddr}  //TO DO CHECK GRANULARITY
  );
  assign obi_amo_req_o.a.a_optional.mid = '0;
  assign obi_amo_req_o.a.a_optional.prot[2:1] = '0;
  assign obi_amo_req_o.a.a_optional.prot[0] = 1'b1;  //data
  assign obi_amo_req_o.a.a_optional.dbg = '0;
  assign obi_amo_req_o.a.a_optional.achk = '0;

  //TODO check parity : store_obi_rsp_i.gntpar != store_obi_rsp_i.gnt

  assign obi_amo_req_o.rready = amo_valid_commit_i;

  // only flush if we are currently not committing the AMO
  // e.g.: it is not speculative anymore
  assign flush_amo_buffer = flush_i & !amo_valid_commit_i;

  cva6_fifo_v3 #(
      .DEPTH  (1),
      .dtype  (amo_op_t),
      .FPGA_EN(CVA6Cfg.FpgaEn)
  ) i_amo_fifo (
      .clk_i     (clk_i),
      .rst_ni    (rst_ni),
      .flush_i   (flush_amo_buffer),
      .testmode_i(1'b0),
      .full_o    (amo_valid),
      .empty_o   (ready_o),
      .usage_o   (),                  // left open
      .data_i    (amo_data_in),
      .push_i    (valid_i),
      .data_o    (amo_data_out),
      .pop_i     (obi_amo_rsp_i.gnt)
  );

endmodule
