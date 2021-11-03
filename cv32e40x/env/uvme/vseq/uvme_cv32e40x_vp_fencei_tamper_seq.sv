// Copyright 2021 OpenHW Group
// Copyright 2021 Silicon Labs
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1
//
// Licensed under the Solderpad Hardware License v 2.1 (the "License"); you may
// not use this file except in compliance with the License, or, at your option,
// the Apache License version 2.0. You may obtain a copy of the License at
//
//     https://solderpad.org/licenses/SHL-2.1/
//
// Unless required by applicable law or agreed to in writing, any work
// distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
// WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
// License for the specific language governing permissions and limitations
// under the License.


`ifndef __UVME_CV32E40X_VP_FENCEI_TAMPER_SEQ_SV__
`define __UVME_CV32E40X_VP_FENCEI_TAMPER_SEQ_SV__


class uvme_cv32e40x_vp_fencei_tamper_seq_c extends uvma_obi_memory_vp_base_seq_c;

  uvme_cv32e40x_cntxt_c    cv32e40x_cntxt;
  uvma_rvvi_ovpsim_cntxt_c rvvi_ovpsim_cntxt;

  bit        enabled = 0;
  bit [31:0] addr;
  bit [31:0] data;

  `uvm_object_utils(uvme_cv32e40x_vp_fencei_tamper_seq_c)

  extern function new(string name="uvme_cv32e40x_vp_fencei_tamper_seq_c");
  extern virtual task vp_body(uvma_obi_memory_mon_trn_c mon_trn);
  extern virtual function int unsigned get_num_words();
  extern virtual task body();
  extern function void write_rtl_mem();
  extern function void write_iss_mem();

endclass : uvme_cv32e40x_vp_fencei_tamper_seq_c


function uvme_cv32e40x_vp_fencei_tamper_seq_c::new(string name="uvme_cv32e40x_vp_fencei_tamper_seq_c");

  super.new(name);

endfunction : new


task uvme_cv32e40x_vp_fencei_tamper_seq_c::vp_body(uvma_obi_memory_mon_trn_c mon_trn);

  uvma_obi_memory_slv_seq_item_c  slv_rsp;

  `uvm_create(slv_rsp)
  slv_rsp.orig_trn = mon_trn;
  slv_rsp.err = 1'b0;

  if (mon_trn.access_type == UVMA_OBI_MEMORY_ACCESS_WRITE) begin
    case (get_vp_index(mon_trn))
      0: enabled = | mon_trn.data;
      1: addr = mon_trn.data;
      2: data = mon_trn.data;
    endcase
  end

  add_r_fields(mon_trn, slv_rsp);
  slv_rsp.set_sequencer(p_sequencer);
  `uvm_send(slv_rsp)

endtask : vp_body


function int unsigned uvme_cv32e40x_vp_fencei_tamper_seq_c::get_num_words();

   return 3;

endfunction : get_num_words


task uvme_cv32e40x_vp_fencei_tamper_seq_c::body();

  if (cv32e40x_cntxt == null) begin
    `uvm_fatal("E40XVPSTATUS", "Must initialize cv32e40x_cntxt in virtual peripheral");
  end
  if (cv32e40x_cntxt.fencei_cntxt == null) begin
    `uvm_fatal("E40XVPSTATUS", "Must initialize fencei_cntxt in virtual peripheral");
  end
  if (cv32e40x_cntxt.fencei_cntxt.fencei_vif == null) begin
    `uvm_fatal("E40XVPSTATUS", "Must initialize fencei_vif in virtual peripheral");
  end
  if (cv32e40x_cntxt.rvvi_cntxt == null) begin
    `uvm_fatal("E40XVPSTATUS", "Must initialize rvvi_cntxt in virtual peripheral");
  end
  if (!$cast(rvvi_ovpsim_cntxt, cv32e40x_cntxt.rvvi_cntxt)) begin
    `uvm_fatal("E40XVPSTATUS", "Could not cast rvvi_cntxt to rvvi_ovpsim_cntxt");
  end

  fork
    while (1) begin
      @(posedge cv32e40x_cntxt.fencei_cntxt.fencei_vif.flush_req);
      if (enabled) begin
        write_rtl_mem();
        write_iss_mem();
      end
    end
  join_none

  super.body();

endtask : body


function void uvme_cv32e40x_vp_fencei_tamper_seq_c::write_rtl_mem();

  cntxt.mem.write((addr + 0), data[ 7: 0]);
  cntxt.mem.write((addr + 1), data[15: 8]);
  cntxt.mem.write((addr + 2), data[23:16]);
  cntxt.mem.write((addr + 3), data[31:24]);

endfunction : write_rtl_mem


function void uvme_cv32e40x_vp_fencei_tamper_seq_c::write_iss_mem();

  logic [31:0] addr_lo;
  logic [31:0] addr_hi;
  int          shamt_lo;
  int          shamt_hi;
  logic [31:0] shdata_lo;
  logic [31:0] shdata_hi;
  logic [31:0] issmask_lo;
  logic [31:0] issmask_hi;
  logic [31:0] issdata_lo;
  logic [31:0] issdata_hi;
  logic [31:0] data_lo;
  logic [31:0] data_hi;

  // Calculate iss ram addresses
  addr_lo = addr >> 2;
  addr_hi = (addr + 4) >> 2;

  // Shift the data to be written
  shamt_lo = addr[1:0] * 8;
  shamt_hi = (4 * 8) - shamt_lo;
  shdata_lo = data << shamt_lo;
  shdata_hi = data >> shamt_hi;

  // Mask the existing data
  issmask_lo = 32'h FFFF_FFFF >> shamt_hi;
  issmask_hi = 32'h FFFF_FFFF << shamt_lo;
  issdata_lo = rvvi_ovpsim_cntxt.ovpsim_mem_vif.mem[addr_lo] & issmask_lo;
  issdata_hi = rvvi_ovpsim_cntxt.ovpsim_mem_vif.mem[addr_hi] & issmask_hi;

  // Calculate iss ram data
  data_lo = shdata_lo | issdata_lo;
  data_hi = shdata_hi | issdata_hi;

  // Write to iss ram
  rvvi_ovpsim_cntxt.ovpsim_mem_vif.mem[addr_lo] = data_lo;
  rvvi_ovpsim_cntxt.ovpsim_mem_vif.mem[addr_hi] = data_hi;

endfunction : write_iss_mem


`endif // __UVME_OBI_MEMORY_VP_FENCEI_TAMPER_SEQ_SV__
