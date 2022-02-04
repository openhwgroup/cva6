// Copyright 2021 OpenHW Group
// Copyright 2021 Silicon Labs, Inc.
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://solderpad.org/licenses/
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0


module uvmt_cv32e40s_fencei_assert
  import cv32e40s_pkg::*;
  import uvm_pkg::*;
#(
  parameter int          PMA_NUM_REGIONS              = 0,
  parameter pma_region_t PMA_CFG[PMA_NUM_REGIONS-1:0] = '{default:'Z}
)(
  input clk_i,
  input rst_ni,

  input fencei_flush_req_o,
  input fencei_flush_ack_i,

  input        wb_valid,
  input        wb_instr_valid,
  input        wb_sys_en,
  input        wb_sys_fencei_insn,
  input [31:0] wb_pc,
  input [31:0] wb_rdata,
  input        wb_buffer_state,

  input        instr_req_o,
  input [31:0] instr_addr_o,
  input        instr_gnt_i,

  input        data_req_o,
  input        data_gnt_i,
  input        data_rvalid_i,

  input rvfi_valid,
  input rvfi_intr,
  input rvfi_dbg_mode
);

  localparam int CYCLE_COUNT = 6;
  default clocking @(posedge clk_i); endclocking
  default disable iff !rst_ni;
  string info_tag = "CV32E40S_FENCEI_ASSERT";

  logic is_fencei_in_wb;
  assign is_fencei_in_wb = wb_sys_fencei_insn && wb_sys_en && wb_instr_valid;

  int obi_outstanding;
  always @(posedge clk_i, negedge rst_ni) begin
    if (~rst_ni) begin
      obi_outstanding <= 0;
    end else if (data_req_o && data_gnt_i && !data_rvalid_i) begin
      obi_outstanding <= obi_outstanding + 1;
    end else if (data_rvalid_i && !(data_req_o && data_gnt_i)) begin
      obi_outstanding <= obi_outstanding - 1;
    end
  end

  function logic bufferable_in_config;
    bufferable_in_config = 0;
    foreach (PMA_CFG[i]) begin
      if (PMA_CFG[i].bufferable) begin
        bufferable_in_config = 1;
      end
    end
  endfunction

  a_req_stay_high: assert property (
    fencei_flush_req_o && !fencei_flush_ack_i
    |=>
    fencei_flush_req_o
  ) else `uvm_error(info_tag, "req must not drop before ack");

  a_req_drop_lo: assert property (
    fencei_flush_req_o && fencei_flush_ack_i
    |=>
    !fencei_flush_req_o
  ) else `uvm_error(info_tag, "req must drop after ack");

  a_req_rise_before_retire: assert property (
    $rose(is_fencei_in_wb)
    |->
    !wb_valid throughout (
      ($rose(fencei_flush_req_o) [->1])
      or
      ($fell(is_fencei_in_wb) [->1])
    )
  ) else `uvm_error(info_tag, "fencei shall not retire without seeing a rising flush req");

  a_req_must_retire: assert property (
    fencei_flush_req_o
    |->
    is_fencei_in_wb until_with wb_valid
  ) else `uvm_error(info_tag, "if there is no retire then there can't be a req");

  property p_fetch_after_retire;
    int pc_next;
    (is_fencei_in_wb && wb_valid, pc_next={wb_pc[31:2],2'b00}+4)
    |->
    (
      // Normal execution
      (instr_req_o && instr_gnt_i) [->1:2]  // next req-gnt (or second next, if ongoing req)
      ##0 (instr_addr_o == pc_next)
    ) or (
      // Exception execution
      rvfi_valid [->2:3]  // retire: fencei, (optionally "rvfi_trap"), interrupt/debug handler
      ##0 (rvfi_intr || rvfi_dbg_mode)
    );
  endproperty
  a_fetch_after_retire: assert property (
    p_fetch_after_retire
  ) else `uvm_error(info_tag, "after fencei, the next-pc fetching cannot be forgone");

  a_stall_until_ack: assert property (
    fencei_flush_req_o && !fencei_flush_ack_i
    |=>
    !$changed(wb_pc)
  ) else `uvm_error(info_tag, "WB stage must remain unchanged until the flush req is acked");

  property p_branch_after_retire;
    int pc_next;
    (fencei_flush_req_o, pc_next=wb_pc+4)
    ##1 !fencei_flush_req_o
    |=>
    (
      wb_valid [->1:2]
      ##0 (wb_pc == pc_next)
    ) or (
      rvfi_valid [->2]
      ##0 (rvfi_intr || rvfi_dbg_mode)
    );
  endproperty
  a_branch_after_retire: assert property (
    p_branch_after_retire
  ) else `uvm_error(info_tag, "the pc following fencei did not enter WB");

  a_supress_datareq: assert property (
    fencei_flush_req_o
    |->
    !data_req_o
  ) else `uvm_error(info_tag, "obi data req shall not happen while fencei is flushing");

  property p_fencei_quick_retire;
    $rose(is_fencei_in_wb)
    ##1 (fencei_flush_req_o && fencei_flush_ack_i);
  endproperty
  a_cycle_count_minimum: assert property (
    p_fencei_quick_retire
    implies
    (##1 !$rose(wb_instr_valid) [*CYCLE_COUNT-1])
  ) else `uvm_error(info_tag, "fencei shan't finish before the expected number of cycles");
  c_cycle_count_minimum: cover property (
    p_fencei_quick_retire
    and
    (s_nexttime [CYCLE_COUNT] $rose(wb_instr_valid))
  );

  property p_req_wait_bus;
    fencei_flush_req_o
    |->
    !data_rvalid_i throughout (
      $fell(wb_valid) [->1]
      ##1 (data_req_o && data_gnt_i) [->1]
    );
  endproperty
  a_req_wait_bus: assert property (p_req_wait_bus)
    else `uvm_error(info_tag, "flush req shall not come if rvalid is awaited");
  if (bufferable_in_config()) begin : gen_c_req_wait_bus
    c_req_wait_bus: cover property (
      $rose(is_fencei_in_wb)
      ##1 (
        is_fencei_in_wb throughout (
          ($rose(data_rvalid_i) [->1])
          ##0 ($rose(fencei_flush_req_o) [->1])
        )
      )
    );
  end

  property p_req_wait_outstanding;
    fencei_flush_req_o |-> (obi_outstanding == 0);
  endproperty
  a_req_wait_outstanding: assert property (p_req_wait_outstanding)
    else `uvm_error(info_tag, "flush req shall not come if obi has outstanding transactions");
  if (bufferable_in_config()) begin : gen_c_req_wait_outstanding_1
    c_req_wait_outstanding_1: cover property (
      is_fencei_in_wb throughout ((obi_outstanding >= 1) ##0 (fencei_flush_req_o [->1]))
    );
  end

  
  property p_req_wait_buffer;
    is_fencei_in_wb && (wb_buffer_state == WBUF_FULL) |->
      !fencei_flush_req_o throughout(
        (data_rvalid_i && (wb_buffer_state == WBUF_EMPTY)) [->1]
      );
  endproperty

  a_req_wait_buffer: assert property(p_req_wait_buffer) 
    else `uvm_error(info_tag, "fencei_flush_req_o should be held low until write buffer is empty");


  // TODO:ropeders assert fencei flush req explicitly vs X interface queue (not just vs rvalid)


  for (genvar i = 1; i <= 5; i++) begin: gen_ack_delayed
    // "5" is an appropriate arbitrary upper limit
    c_ack_delayed: cover property (
      $rose(fencei_flush_req_o)
      ##0 (!fencei_flush_ack_i) [*i]
      ##1 fencei_flush_ack_i
    );
  end

  covergroup cg_reqack(string name) @(posedge clk_i);
    option.per_instance = 1;
    option.name = name;

    cp_req: coverpoint fencei_flush_req_o {
      bins hi = {1};
      bins lo = {0};
      bins rose = (0 => 1);
      bins fell = (1 => 0);
    }
    cp_ack: coverpoint fencei_flush_ack_i {
      bins hi = {1};
      bins lo = {0};
      bins rose = (0 => 1);
      bins fell = (1 => 0);
    }
    cross_req_ack: cross cp_req, cp_ack {
      illegal_bins il = binsof(cp_req.fell) && binsof(cp_ack.rose);
    }
  endgroup
  cg_reqack reqack_cg = new("reqack");

  c_no_retire: cover property (
    $rose(is_fencei_in_wb)
    ##0 (!wb_valid throughout ($fell(is_fencei_in_wb) [->1]))
  );

  covergroup cg_reserved(string name) @(posedge clk_i);
    option.per_instance = 1;
    option.name = name;

    // Just a handfull of different values for reserved to-be-ignored fields
    cp_imm: coverpoint wb_rdata[31:20] iff (is_fencei_in_wb && wb_valid) {
      bins b[4] = {[0:$]};
    }
    cp_rs1: coverpoint wb_rdata[19:15] iff (is_fencei_in_wb && wb_valid) {
      bins b[4] = {[0:$]};
    }
    cp_rd: coverpoint wb_rdata[11:7] iff (is_fencei_in_wb && wb_valid) {
      bins b[4] = {[0:$]};
    }
  endgroup
  cg_reserved reserved_cg = new("reserved");

endmodule : uvmt_cv32e40s_fencei_assert
