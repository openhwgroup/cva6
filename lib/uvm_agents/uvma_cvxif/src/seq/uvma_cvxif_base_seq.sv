// Copyright 2021 Thales DIS design services SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Zineb EL KACIMI (zineb.el-kacimi@external.thalesgroup.com)


`ifndef __UVMA_CVXIF_BASE_SEQ_SV__
`define __UVMA_CVXIF_BASE_SEQ_SV__


class uvma_cvxif_base_seq_c extends uvm_sequence #(uvma_cvxif_resp_item_c);

   `uvm_object_utils (uvma_cvxif_base_seq_c)
   `uvm_declare_p_sequencer (uvma_cvxif_sqr_c)

   uvma_cvxif_resp_item_c   resp_item;
   uvma_cvxif_req_item_c    req_item;

   uvma_cvxif_cfg_c    cfg;

   string info_tag = "CVXIF_BASE_SEQ";

   extern function new(string name="uvma_cvxif_base_seq");

   extern virtual task pre_body();

   extern function string decode(input logic [31:0] instr);

endclass

function uvma_cvxif_base_seq_c::new(string name="uvma_cvxif_base_seq");

   super.new(name);

endfunction : new

task uvma_cvxif_base_seq_c::pre_body();

   req_item  = uvma_cvxif_req_item_c::type_id::create("req_item");
   resp_item = uvma_cvxif_resp_item_c::type_id::create("resp_item");

   cfg   = p_sequencer.cfg;

endtask

function string uvma_cvxif_base_seq_c::decode(input logic [31:0] instr);

   bit [6:0] opcode    = instr [6:0];
   bit [6:0] custom3   = 7'b1111011;
   bit [6:0] func7     = instr [31:25];
   bit [1:0] func2     = instr [26:25];
   bit [1:0] func3     = instr [14:12];
   bit [4:0] rd        = instr [11:7];
   bit [4:0] rs1       = instr [19:15];
   bit [4:0] rs2       = instr [24:20];

   if (opcode != custom3 ) begin
      return ("illegal");
   end
   else begin
      if (func3 == 0) begin
         if (rd == 0) begin
             if (func7 == 0 && rs1 == 0 && rs2 == 0) begin
                return ("CUS_NOP");
             end
             if (func7 == 7'b1000000 && rs2 == 0) begin
                return ("CUS_EXC");
             end
             if (func7 == 7'b0100000 && rs1 == 0 && rs2 == 0) begin
                return ("CUS_NOP_EXC");
             end
             if (func7 == 7'b1100000 && rs1 == 0 && rs2 == 0) begin
                return ("CUS_ISS_EXC");
             end
         end
         else begin
            if (func7 == 0) begin
              return ("CUS_ADD");
            end
            if (func2==2'b01) begin
               return ("CUS_ADD_RS3");
            end
            if (func7==7'b0001000) begin
               return ("CUS_ADD_MULTI");
            end
            if (func7==7'b0000010) begin
               return ("CUS_M_ADD");
            end
            if (func7==7'b0000110) begin
               return ("CUS_S_ADD");
            end
         end
      end
      else begin
        return ("illegal");
      end
   end

endfunction


`endif // __UVMA_CVXIF_BASE_SEQ_SV__
