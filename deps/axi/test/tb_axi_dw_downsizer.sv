// Copyright 2020 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// File          : tb_axi_dw_downsizer.sv
// Author        : Matheus Cavalcante <matheusd@iis.ee.ethz.ch>
// Created       : 09.02.2019

// Copyright (C) 2020 ETH Zurich, University of Bologna
// All rights reserved.

`include "axi/assign.svh"
`include "axi/typedef.svh"

module tb_axi_dw_downsizer;

  timeunit      1ns;
  timeprecision 10ps;

  parameter AW   = 64;
  parameter IW   = 4;
  parameter DW   = 32;
  parameter UW   = 8;
  parameter MULT = 8;

  // Clock

  localparam tCK = 1ns;

  logic clk  = 0;
  logic rst  = 1;
  logic done = 0;

  initial begin
    #tCK;
    rst <= 0;
    #tCK;
    rst <= 1;
    #tCK;
    while (!done) begin
      clk <= 1;
      #(tCK/2);
      clk <= 0;
      #(tCK/2);
    end
  end

  // AXI Buses

  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH (AW),
    .AXI_DATA_WIDTH (DW),
    .AXI_ID_WIDTH   (IW),
    .AXI_USER_WIDTH (UW)
  ) axi_master_dv (clk);

  axi_test::rand_axi_master #(
    .AW             (AW   ),
    .DW             (DW   ),
    .IW             (IW   ),
    .UW             (UW   ),
    .MAX_READ_TXNS  (8    ),
    .MAX_WRITE_TXNS (8    ),
    .TA             (200ps),
    .TT             (700ps)
  ) axi_master_drv = new (axi_master_dv);

  AXI_BUS_DV #(
    .AXI_ADDR_WIDTH (AW       ),
    .AXI_DATA_WIDTH (MULT * DW),
    .AXI_ID_WIDTH   (IW       ),
    .AXI_USER_WIDTH (UW       )
  ) axi_slave_dv ( clk );

  axi_test::rand_axi_slave #(
    .AW (AW       ),
    .DW (MULT * DW),
    .IW (IW       ),
    .UW (UW       ),
    .TA (200ps    ),
    .TT (700ps    )
  ) axi_slave_drv = new ( axi_slave_dv );

  // AXI channel types
  typedef logic [AW-1:0] addr_t           ;
  typedef logic [IW-1:0] id_t             ;
  typedef logic [UW-1:0] user_t           ;
  typedef logic [DW-1:0] mst_data_t       ;
  typedef logic [DW/8-1:0] mst_strb_t     ;
  typedef logic [MULT*DW-1:0] slv_data_t  ;
  typedef logic [MULT*DW/8-1:0] slv_strb_t;

  `AXI_TYPEDEF_AW_CHAN_T(aw_chan_t, addr_t, id_t, user_t)            ;
  `AXI_TYPEDEF_W_CHAN_T(mst_w_chan_t, mst_data_t, mst_strb_t, user_t);
  `AXI_TYPEDEF_W_CHAN_T(slv_w_chan_t, slv_data_t, slv_strb_t, user_t);
  `AXI_TYPEDEF_B_CHAN_T(b_chan_t, id_t, user_t)                      ;
  `AXI_TYPEDEF_AR_CHAN_T(ar_chan_t, addr_t, id_t, user_t)            ;
  `AXI_TYPEDEF_R_CHAN_T(mst_r_chan_t, mst_data_t, id_t, user_t)      ;
  `AXI_TYPEDEF_R_CHAN_T(slv_r_chan_t, slv_data_t, id_t, user_t)      ;

  `AXI_TYPEDEF_REQ_T(mst_req_t, aw_chan_t, mst_w_chan_t, ar_chan_t);
  `AXI_TYPEDEF_RESP_T(mst_resp_t, b_chan_t, mst_r_chan_t)          ;
  `AXI_TYPEDEF_REQ_T(slv_req_t, aw_chan_t, slv_w_chan_t, ar_chan_t);
  `AXI_TYPEDEF_RESP_T(slv_resp_t, b_chan_t, slv_r_chan_t)          ;

  mst_req_t  axi_mst_req;
  mst_resp_t axi_mst_resp;
  `AXI_ASSIGN_TO_REQ(axi_mst_req, axi_master_dv)    ;
  `AXI_ASSIGN_FROM_RESP(axi_master_dv, axi_mst_resp);

  slv_req_t  axi_slv_req;
  slv_resp_t axi_slv_resp;
  `AXI_ASSIGN_FROM_REQ(axi_slave_dv, axi_slv_req);
  `AXI_ASSIGN_TO_RESP(axi_slv_resp, axi_slave_dv);

  // DUT

  axi_dw_converter #(
    .AxiMaxReads    (4           ),
    .AxiMstDataWidth(MULT * DW   ),
    .AxiSlvDataWidth(DW          ),
    .AxiAddrWidth   (AW          ),
    .AxiIdWidth     (IW          ),
    .aw_chan_t      (aw_chan_t   ),
    .mst_w_chan_t   (slv_w_chan_t),
    .slv_w_chan_t   (mst_w_chan_t),
    .b_chan_t       (b_chan_t    ),
    .ar_chan_t      (ar_chan_t   ),
    .mst_r_chan_t   (slv_r_chan_t),
    .slv_r_chan_t   (mst_r_chan_t),
    .axi_mst_req_t  (slv_req_t   ),
    .axi_mst_resp_t (slv_resp_t  ),
    .axi_slv_req_t  (mst_req_t   ),
    .axi_slv_resp_t (mst_resp_t  )
  ) i_dw_converter (
    .clk_i     (clk         ),
    .rst_ni    (rst         ),
    .slv_req_i (axi_mst_req ),
    .slv_resp_o(axi_mst_resp),
    .mst_req_o (axi_slv_req ),
    .mst_resp_i(axi_slv_resp)
  );

  initial begin
    axi_master_drv.reset()                                                             ;
    axi_master_drv.add_memory_region({AW{1'b0}}, {AW{1'b1}}, axi_pkg::WTHRU_NOALLOCATE);
    axi_master_drv.run(50, 50)                                                         ;
    done = 1;
  end

  initial begin
    axi_slave_drv.reset();
    axi_slave_drv.run()  ;
  end

  // Terminate simulation after all transactions have completed.
  initial begin
    wait (done);
    #(10*tCK)  ;
    $finish(0) ;
  end

// vsim -voptargs=+acc work.tb_axi_dw_downsizer
endmodule : tb_axi_dw_downsizer
