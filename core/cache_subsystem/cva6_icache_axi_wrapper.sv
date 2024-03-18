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
// Author: Nils Wistoff <nwistoff@iis.ee.ethz.ch>, ETH Zurich
// Date: 07.09.2020
// Description: wrapper module to connect the L1I$ to a 64bit AXI bus.
//

module cva6_icache_axi_wrapper
  import ariane_pkg::*;
  import wt_cache_pkg::*;
#(
    parameter config_pkg::cva6_cfg_t CVA6Cfg = config_pkg::cva6_cfg_empty,
    parameter type icache_areq_t = logic,
    parameter type icache_arsp_t = logic,
    parameter type icache_dreq_t = logic,
    parameter type icache_drsp_t = logic,
    parameter type icache_req_t = logic,
    parameter type icache_rtrn_t = logic,
    parameter type axi_req_t = logic,
    parameter type axi_rsp_t = logic
) (
    input logic             clk_i,
    input logic             rst_ni,
    input riscv::priv_lvl_t priv_lvl_i,

    input logic flush_i,  // flush the icache, flush and kill have to be asserted together
    input logic en_i,  // enable icache
    output logic miss_o,  // to performance counter
    // address translation requests
    input icache_areq_t areq_i,
    output icache_arsp_t areq_o,
    // data requests
    input icache_dreq_t dreq_i,
    output icache_drsp_t dreq_o,
    // AXI refill port
    output axi_req_t axi_req_o,
    input axi_rsp_t axi_resp_i
);

  localparam AxiNumWords = (CVA6Cfg.ICACHE_LINE_WIDTH/CVA6Cfg.AxiDataWidth) * (CVA6Cfg.ICACHE_LINE_WIDTH  > CVA6Cfg.DCACHE_LINE_WIDTH)  +
                           (CVA6Cfg.DCACHE_LINE_WIDTH/CVA6Cfg.AxiDataWidth) * (CVA6Cfg.ICACHE_LINE_WIDTH <= CVA6Cfg.DCACHE_LINE_WIDTH) ;

  logic                                    icache_mem_rtrn_vld;
  icache_rtrn_t                            icache_mem_rtrn;
  logic                                    icache_mem_data_req;
  logic                                    icache_mem_data_ack;
  icache_req_t                             icache_mem_data;

  logic                                    axi_rd_req;
  logic                                    axi_rd_gnt;
  logic         [CVA6Cfg.AxiAddrWidth-1:0] axi_rd_addr;
  logic         [ $clog2(AxiNumWords)-1:0] axi_rd_blen;
  logic         [                     2:0] axi_rd_size;
  logic         [  CVA6Cfg.AxiIdWidth-1:0] axi_rd_id_in;
  logic                                    axi_rd_rdy;
  logic                                    axi_rd_lock;
  logic                                    axi_rd_last;
  logic                                    axi_rd_valid;
  logic         [CVA6Cfg.AxiDataWidth-1:0] axi_rd_data;
  logic         [  CVA6Cfg.AxiIdWidth-1:0] axi_rd_id_out;
  logic                                    axi_rd_exokay;

  logic req_valid_d, req_valid_q;
  icache_req_t req_data_d, req_data_q;
  logic first_d, first_q;
  logic [CVA6Cfg.ICACHE_LINE_WIDTH/CVA6Cfg.AxiDataWidth-1:0][CVA6Cfg.AxiDataWidth-1:0]
      rd_shift_d, rd_shift_q;

  // Keep read request asserted until we have an AXI grant. This is not guaranteed by icache (but
  // required by AXI).
  assign req_valid_d           = ~axi_rd_gnt & (icache_mem_data_req | req_valid_q);

  // Update read request information on a new request
  assign req_data_d            = (icache_mem_data_req) ? icache_mem_data : req_data_q;

  // We have a new or pending read request
  assign axi_rd_req            = icache_mem_data_req | req_valid_q;
  assign axi_rd_addr           = CVA6Cfg.AxiAddrWidth'(req_data_d.paddr);

  // Fetch a full cache line on a cache miss, or a single word on a bypassed access
  assign axi_rd_blen           = (req_data_d.nc) ? '0 : CVA6Cfg.ICACHE_LINE_WIDTH / 64 - 1;
  assign axi_rd_size           = $clog2(CVA6Cfg.AxiDataWidth / 8);  // Maximum
  assign axi_rd_id_in          = req_data_d.tid;
  assign axi_rd_rdy            = 1'b1;
  assign axi_rd_lock           = 1'b0;

  // Immediately acknowledge read request. This is an implicit requirement for the icache.
  assign icache_mem_data_ack   = icache_mem_data_req;

  // Return data as soon as last word arrives
  assign icache_mem_rtrn_vld   = axi_rd_valid & axi_rd_last;
  assign icache_mem_rtrn.data  = rd_shift_d;
  assign icache_mem_rtrn.tid   = req_data_q.tid;
  assign icache_mem_rtrn.rtype = wt_cache_pkg::ICACHE_IFILL_ACK;
  assign icache_mem_rtrn.inv   = '0;

  // -------
  // I-Cache
  // -------
  cva6_icache #(
      // use ID 0 for icache reads
      .CVA6Cfg(CVA6Cfg),
      .icache_areq_t(icache_areq_t),
      .icache_arsp_t(icache_arsp_t),
      .icache_dreq_t(icache_dreq_t),
      .icache_drsp_t(icache_drsp_t),
      .icache_req_t(icache_req_t),
      .icache_rtrn_t(icache_rtrn_t),
      .RdTxId(0)
  ) i_cva6_icache (
      .clk_i         (clk_i),
      .rst_ni        (rst_ni),
      .flush_i       (flush_i),
      .en_i          (en_i),
      .miss_o        (miss_o),
      .areq_i        (areq_i),
      .areq_o        (areq_o),
      .dreq_i        (dreq_i),
      .dreq_o        (dreq_o),
      .mem_rtrn_vld_i(icache_mem_rtrn_vld),
      .mem_rtrn_i    (icache_mem_rtrn),
      .mem_data_req_o(icache_mem_data_req),
      .mem_data_ack_i(icache_mem_data_ack),
      .mem_data_o    (icache_mem_data)
  );

  // --------
  // AXI shim
  // --------
  axi_shim #(
      .CVA6Cfg    (CVA6Cfg),
      .AxiNumWords(AxiNumWords),
      .axi_req_t  (axi_req_t),
      .axi_rsp_t  (axi_rsp_t)
  ) i_axi_shim (
      .clk_i      (clk_i),
      .rst_ni     (rst_ni),
      .rd_req_i   (axi_rd_req),
      .rd_gnt_o   (axi_rd_gnt),
      .rd_addr_i  (axi_rd_addr),
      .rd_blen_i  (axi_rd_blen),
      .rd_size_i  (axi_rd_size),
      .rd_id_i    (axi_rd_id_in),
      .rd_rdy_i   (axi_rd_rdy),
      .rd_lock_i  (axi_rd_lock),
      .rd_last_o  (axi_rd_last),
      .rd_valid_o (axi_rd_valid),
      .rd_data_o  (axi_rd_data),
      .rd_user_o  (),
      .rd_id_o    (axi_rd_id_out),
      .rd_exokay_o(axi_rd_exokay),
      .wr_req_i   ('0),
      .wr_gnt_o   (),
      .wr_addr_i  ('0),
      .wr_data_i  ('0),
      .wr_user_i  ('0),
      .wr_be_i    ('0),
      .wr_blen_i  ('0),
      .wr_size_i  ('0),
      .wr_id_i    ('0),
      .wr_lock_i  ('0),
      .wr_atop_i  ('0),
      .wr_rdy_i   ('0),
      .wr_valid_o (),
      .wr_id_o    (),
      .wr_exokay_o(),
      .axi_req_o  (axi_req_o),
      .axi_resp_i (axi_resp_i)
  );

  // Buffer burst data in shift register
  always_comb begin : p_axi_rtrn_shift
    first_d    = first_q;
    rd_shift_d = rd_shift_q;

    if (axi_rd_valid) begin
      first_d = axi_rd_last;
      if (CVA6Cfg.ICACHE_LINE_WIDTH == CVA6Cfg.AxiDataWidth) begin
        rd_shift_d = axi_rd_data;
      end else begin
        rd_shift_d = {axi_rd_data, rd_shift_q[CVA6Cfg.ICACHE_LINE_WIDTH/CVA6Cfg.AxiDataWidth-1:1]};
      end

      // If this is a single word transaction, we need to make sure that word is placed at offset 0
      if (first_q) begin
        rd_shift_d[0] = axi_rd_data;
      end
    end
  end

  // Registers
  always_ff @(posedge clk_i or negedge rst_ni) begin : p_rd_buf
    if (!rst_ni) begin
      req_valid_q <= 1'b0;
      req_data_q  <= '0;
      first_q     <= 1'b1;
      rd_shift_q  <= '0;
    end else begin
      req_valid_q <= req_valid_d;
      req_data_q  <= req_data_d;
      first_q     <= first_d;
      rd_shift_q  <= rd_shift_d;
    end
  end

endmodule  // cva6_icache_axi_wrapper
