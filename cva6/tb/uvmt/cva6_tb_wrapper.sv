///////////////////////////////////////////////////////////////////////////////
//
// Copyright 2021 OpenHW Group
// Copyright 2021 Thales DIS Design Services SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//    https://solderpad.org/licenses/
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
//
///////////////////////////////////////////////////////////////////////////////
//
// CVA6 "core_only" testbench wrapper.
//
///////////////////////////////////////////////////////////////////////////////

`define MAIN_MEM(P) uvmt_cva6_tb.cva6_dut_wrap.cva6_tb_wrapper_i.i_sram.gen_cut[0].gen_mem.i_tc_sram_wrapper.i_tc_sram.init_val[(``P``)]
`define USER_MEM(P) uvmt_cva6_tb.cva6_dut_wrap.cva6_tb_wrapper_i.i_sram.gen_cut[0].gen_mem.gen_mem_user.i_tc_sram_wrapper_user.i_tc_sram.init_val[(``P``)]

import uvm_pkg::*;

`include "uvm_macros.svh"

import "DPI-C" function read_elf(input string filename);
import "DPI-C" function byte get_section(output longint address, output longint len);
import "DPI-C" context function void read_section(input longint address, inout byte buffer[]);

module cva6_tb_wrapper #(
  parameter int unsigned AXI_USER_WIDTH    = 1,
  parameter int unsigned AXI_USER_EN       = 0,
  parameter int unsigned AXI_ADDRESS_WIDTH = 64,
  parameter int unsigned AXI_DATA_WIDTH    = 64,
  parameter int unsigned NUM_WORDS         = 2**25
) (
  input  logic                         clk_i,
  input  logic                         rst_ni,
  output wire                          tb_exit_o,
  output ariane_rvfi_pkg::rvfi_port_t  rvfi_o,
  input  cvxif_pkg::cvxif_resp_t       cvxif_resp,
  output cvxif_pkg::cvxif_req_t        cvxif_req,
  uvma_axi_intf                        axi_slave
);

  ariane_axi::req_t    axi_ariane_req;
  ariane_axi::resp_t   axi_ariane_resp;

  static uvm_cmdline_processor uvcl = uvm_cmdline_processor::get_inst();
  string binary = "";

  ariane_rvfi_pkg::rvfi_port_t  rvfi;
  assign rvfi_o = rvfi;

  cva6 #(
    .ArianeCfg  ( ariane_soc::ArianeSocCfg )
  ) i_cva6 (
    .clk_i                ( clk_i                     ),
    .rst_ni               ( rst_ni                    ),
    .boot_addr_i          ( 64'h0000_0000_8000_0000   ), //ariane_soc::ROMBase
    .hart_id_i            ( 64'h0000_0000_0000_0000   ),
    .irq_i                ( 2'b00 /*irqs*/            ),
    .ipi_i                ( 1'b0  /*ipi*/             ),
    .time_irq_i           ( 1'b0  /*timer_irq*/       ),
    .debug_req_i          ( 1'b0                      ),
    .rvfi_o               ( rvfi                      ),
    .cvxif_req_o          ( cvxif_req                 ),
    .cvxif_resp_i         ( cvxif_resp                ),
    .axi_req_o            ( axi_ariane_req            ),
    .axi_resp_i           ( axi_ariane_resp           )
  );

  //----------------------------------------------------------------------------
  // RVFI
  //----------------------------------------------------------------------------

  rvfi_tracer  #(
    .HART_ID(8'h0),
    .DEBUG_START(0),
    .DEBUG_STOP(0),
    .NR_COMMIT_PORTS(ariane_pkg::NR_COMMIT_PORTS)
  ) rvfi_tracer_i (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .rvfi_i(rvfi)
  ) ;

  //----------------------------------------------------------------------------
  // Memory
  //----------------------------------------------------------------------------

  logic                         req;
  logic                         we;
  logic [AXI_ADDRESS_WIDTH-1:0] addr;
  logic [AXI_DATA_WIDTH/8-1:0]  be;
  logic [AXI_DATA_WIDTH-1:0]    wdata;
  logic [AXI_USER_WIDTH-1:0]    wuser;
  logic [AXI_DATA_WIDTH-1:0]    rdata;
  logic [AXI_USER_WIDTH-1:0]    ruser;

  //Response structs
   assign axi_ariane_resp.aw_ready = axi_slave.aw_ready;
   assign axi_ariane_resp.ar_ready = axi_slave.ar_ready;
   assign axi_ariane_resp.w_ready  = axi_slave.w_ready;
   assign axi_ariane_resp.b_valid  = axi_slave.b_valid;
   assign axi_ariane_resp.r_valid  = axi_slave.r_valid;
   // B Channel
   assign axi_ariane_resp.b.id   = axi_slave.b_id;
   assign axi_ariane_resp.b.resp = axi_slave.b_resp;
   assign axi_ariane_resp.b.user = axi_slave.b_user;
   // R Channel
   assign axi_ariane_resp.r.id   = axi_slave.r_id;
   assign axi_ariane_resp.r.data = axi_slave.r_data;
   assign axi_ariane_resp.r.resp = axi_slave.r_resp;
   assign axi_ariane_resp.r.last = axi_slave.r_last;
   assign axi_ariane_resp.r.user = axi_slave.r_user;

   // Request structs
   assign axi_slave.aw_valid = axi_ariane_req.aw_valid;
   assign axi_slave.w_valid  = axi_ariane_req.w_valid;
   assign axi_slave.b_ready  = axi_ariane_req.b_ready;
   assign axi_slave.ar_valid = axi_ariane_req.ar_valid;
   assign axi_slave.r_ready  = axi_ariane_req.r_ready;
   // AW Channel
   assign axi_slave.aw_id     = axi_ariane_req.aw.id;
   assign axi_slave.aw_addr   = axi_ariane_req.aw.addr;
   assign axi_slave.aw_len    = axi_ariane_req.aw.len;
   assign axi_slave.aw_size   = axi_ariane_req.aw.size;
   assign axi_slave.aw_burst  = axi_ariane_req.aw.burst;
   assign axi_slave.aw_lock   = axi_ariane_req.aw.lock;
   assign axi_slave.aw_cache  = axi_ariane_req.aw.cache;
   assign axi_slave.aw_prot   = axi_ariane_req.aw.prot;
   assign axi_slave.aw_qos    = axi_ariane_req.aw.qos;
   assign axi_slave.aw_region = axi_ariane_req.aw.region;
   assign axi_slave.aw_user   = 0;
    // W Channel
   assign axi_slave.w_data = axi_ariane_req.w.data;
   assign axi_slave.w_strb = axi_ariane_req.w.strb;
   assign axi_slave.w_last = axi_ariane_req.w.last;
   assign axi_slave.w_user = 0;
   // AR Channel
   assign axi_slave.ar_id     = axi_ariane_req.ar.id;
   assign axi_slave.ar_addr   = axi_ariane_req.ar.addr;
   assign axi_slave.ar_len    = axi_ariane_req.ar.len;
   assign axi_slave.ar_size   = axi_ariane_req.ar.size;
   assign axi_slave.ar_burst  = axi_ariane_req.ar.burst;
   assign axi_slave.ar_lock   = axi_ariane_req.ar.lock;
   assign axi_slave.ar_cache  = axi_ariane_req.ar.cache;
   assign axi_slave.ar_prot   = axi_ariane_req.ar.prot;
   assign axi_slave.ar_qos    = axi_ariane_req.ar.qos;
   assign axi_slave.ar_region = axi_ariane_req.ar.region;
   assign axi_slave.ar_user   = 0;


endmodule
