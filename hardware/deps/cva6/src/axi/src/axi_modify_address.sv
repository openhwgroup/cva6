// Copyright (c) 2014-2018 ETH Zurich, University of Bologna
//
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Fabian Schuiki <fschuiki@iis.ee.ethz.ch>


/// A connector allows addresses of AXI requests to be changed.
module axi_modify_address #(
  parameter int ADDR_WIDTH_IN  = -1,
  parameter int ADDR_WIDTH_OUT = ADDR_WIDTH_IN
)(
  AXI_BUS.Slave   in,
  AXI_BUS.Master  out,
  output logic [ADDR_WIDTH_IN-1:0]  aw_addr_in,
  output logic [ADDR_WIDTH_IN-1:0]  ar_addr_in,
  input  logic [ADDR_WIDTH_OUT-1:0] aw_addr_out,
  input  logic [ADDR_WIDTH_OUT-1:0] ar_addr_out
);

  `ifndef SYNTHESIS
  initial begin
    assert(ADDR_WIDTH_IN > 0);
    assert(ADDR_WIDTH_OUT > 0);
  end
  `endif

  assign aw_addr_in = in.aw_addr;
  assign ar_addr_in = in.ar_addr;

  assign out.aw_id     = in.aw_id;
  assign out.aw_addr   = aw_addr_out;
  assign out.aw_len    = in.aw_len;
  assign out.aw_size   = in.aw_size;
  assign out.aw_burst  = in.aw_burst;
  assign out.aw_lock   = in.aw_lock;
  assign out.aw_cache  = in.aw_cache;
  assign out.aw_prot   = in.aw_prot;
  assign out.aw_qos    = in.aw_qos;
  assign out.aw_region = in.aw_region;
  assign out.aw_atop   = in.aw_atop;
  assign out.aw_user   = in.aw_user;
  assign out.aw_valid  = in.aw_valid;
  assign out.w_data    = in.w_data;
  assign out.w_strb    = in.w_strb;
  assign out.w_last    = in.w_last;
  assign out.w_user    = in.w_user;
  assign out.w_valid   = in.w_valid;
  assign out.b_ready   = in.b_ready;
  assign out.ar_id     = in.ar_id;
  assign out.ar_addr   = ar_addr_out;
  assign out.ar_len    = in.ar_len;
  assign out.ar_size   = in.ar_size;
  assign out.ar_burst  = in.ar_burst;
  assign out.ar_lock   = in.ar_lock;
  assign out.ar_cache  = in.ar_cache;
  assign out.ar_prot   = in.ar_prot;
  assign out.ar_qos    = in.ar_qos;
  assign out.ar_region = in.ar_region;
  assign out.ar_user   = in.ar_user;
  assign out.ar_valid  = in.ar_valid;
  assign out.r_ready   = in.r_ready;

  assign in.aw_ready = out.aw_ready;
  assign in.w_ready  = out.w_ready;
  assign in.b_id     = out.b_id;
  assign in.b_resp   = out.b_resp;
  assign in.b_user   = out.b_user;
  assign in.b_valid  = out.b_valid;
  assign in.ar_ready = out.ar_ready;
  assign in.r_id     = out.r_id;
  assign in.r_data   = out.r_data;
  assign in.r_resp   = out.r_resp;
  assign in.r_last   = out.r_last;
  assign in.r_user   = out.r_user;
  assign in.r_valid  = out.r_valid;

endmodule
