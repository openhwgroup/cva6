// Copyright 2014-2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// AW Channel Allocator: Arbitrate AWs between `N_TARG_PORT` slave ports.
module axi_AW_allocator #(
  parameter AXI_ADDRESS_W = 32,
  parameter AXI_USER_W    = 6,
  parameter N_TARG_PORT   = 7,
  parameter LOG_N_TARG    = $clog2(N_TARG_PORT),
  parameter AXI_ID_IN     = 16,
  parameter AXI_ID_OUT    = AXI_ID_IN + $clog2(N_TARG_PORT)
) (
  input  logic                                        clk,
  input  logic                                        rst_n,

  input  logic [N_TARG_PORT-1:0][AXI_ID_IN-1:0]       awid_i,
  input  logic [N_TARG_PORT-1:0][AXI_ADDRESS_W-1:0]   awaddr_i,
  input  logic [N_TARG_PORT-1:0][7:0]                 awlen_i,
  input  logic [N_TARG_PORT-1:0][2:0]                 awsize_i,
  input  logic [N_TARG_PORT-1:0][1:0]                 awburst_i,
  input  logic [N_TARG_PORT-1:0]                      awlock_i,
  input  logic [N_TARG_PORT-1:0][3:0]                 awcache_i,
  input  logic [N_TARG_PORT-1:0][2:0]                 awprot_i,
  input  logic [N_TARG_PORT-1:0][3:0]                 awregion_i,
  input  logic [N_TARG_PORT-1:0][5:0]                 awatop_i,
  input  logic [N_TARG_PORT-1:0][AXI_USER_W-1:0]      awuser_i,
  input  logic [N_TARG_PORT-1:0][3:0]                 awqos_i,

  input  logic [N_TARG_PORT-1:0]                      awvalid_i,
  output logic [N_TARG_PORT-1:0]                      awready_o,


  output logic [AXI_ID_OUT-1:0]                       awid_o,
  output logic [AXI_ADDRESS_W-1:0]                    awaddr_o,
  output logic [7:0]                                  awlen_o,
  output logic [2:0]                                  awsize_o,
  output logic [1:0]                                  awburst_o,
  output logic                                        awlock_o,
  output logic [3:0]                                  awcache_o,
  output logic [2:0]                                  awprot_o,
  output logic [3:0]                                  awregion_o,
  output logic [5:0]                                  awatop_o,
  output logic [AXI_USER_W-1:0]                       awuser_o,
  output logic [3:0]                                  awqos_o,

  output logic                                        awvalid_o,
  input  logic                                        awready_i,

  // Push Interface to DW Allocator
  output logic                                        push_ID_o,
  output logic [LOG_N_TARG+N_TARG_PORT-1:0]           ID_o, // {binary ID, one-hot ID};
  input  logic                                        grant_FIFO_ID_i
);

  typedef struct packed {
    logic [AXI_ID_IN-1:0]     id;
    logic [AXI_ADDRESS_W-1:0] addr;
    logic [7:0]               len;
    logic [2:0]               size;
    logic [1:0]               burst;
    logic                     lock;
    logic [3:0]               cache;
    logic [2:0]               prot;
    logic [3:0]               region;
    logic [5:0]               atop;
    logic [AXI_USER_W-1:0]    user;
    logic [3:0]               qos;
  } aw_t;

  aw_t [N_TARG_PORT-1:0]  aw_inp;
  aw_t                    aw_oup;

  logic [N_TARG_PORT-1:0][LOG_N_TARG+N_TARG_PORT-1:0]   id_int;
  logic [N_TARG_PORT-1:0]                               awready_int;
  logic                                                 awvalid_int;

  assign awid_o     = {ID_o[LOG_N_TARG+N_TARG_PORT-1:N_TARG_PORT], aw_oup.id};
  assign awaddr_o   = aw_oup.addr;
  assign awlen_o    = aw_oup.len;
  assign awsize_o   = aw_oup.size;
  assign awburst_o  = aw_oup.burst;
  assign awlock_o   = aw_oup.lock;
  assign awcache_o  = aw_oup.cache;
  assign awprot_o   = aw_oup.prot;
  assign awregion_o = aw_oup.region;
  assign awatop_o   = aw_oup.atop;
  assign awuser_o   = aw_oup.user;
  assign awqos_o    = aw_oup.qos;

  for (genvar i = 0; i < N_TARG_PORT; i++) begin: gen_aw_inp
    assign aw_inp[i].id     = awid_i[i];
    assign aw_inp[i].addr   = awaddr_i[i];
    assign aw_inp[i].len    = awlen_i[i];
    assign aw_inp[i].size   = awsize_i[i];
    assign aw_inp[i].burst  = awburst_i[i];
    assign aw_inp[i].lock   = awlock_i[i];
    assign aw_inp[i].cache  = awcache_i[i];
    assign aw_inp[i].prot   = awprot_i[i];
    assign aw_inp[i].region = awregion_i[i];
    assign aw_inp[i].atop   = awatop_i[i];
    assign aw_inp[i].user   = awuser_i[i];
    assign aw_inp[i].qos    = awqos_i[i];
  end

  assign awready_o  = {N_TARG_PORT{grant_FIFO_ID_i}} & awready_int;
  assign awvalid_o  = awvalid_int & grant_FIFO_ID_i;
  assign push_ID_o  = awvalid_o & awready_i & grant_FIFO_ID_i;

  for (genvar i = 0; i < N_TARG_PORT; i++) begin: gen_id_int
    assign id_int[i][N_TARG_PORT-1:0] = 2**i;                     // one-hot encoding
    assign id_int[i][LOG_N_TARG+N_TARG_PORT-1:N_TARG_PORT] = i;   // binary encoding
  end

  axi_node_arbiter #(
    .AUX_WIDTH  ($bits(aw_t)),
    .ID_WIDTH   (LOG_N_TARG+N_TARG_PORT),
    .N_MASTER   (N_TARG_PORT)
  ) i_arbiter (
    .clk_i        (clk),
    .rst_ni       (rst_n),

    .inp_id_i     (id_int),
    .inp_aux_i    (aw_inp),
    .inp_valid_i  (awvalid_i),
    .inp_ready_o  (awready_int),

    .oup_id_o     (ID_o),
    .oup_aux_o    (aw_oup),
    .oup_valid_o  (awvalid_int),
    .oup_ready_i  (awready_i)
  );

endmodule
