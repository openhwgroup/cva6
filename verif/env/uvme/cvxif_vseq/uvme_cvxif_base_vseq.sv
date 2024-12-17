// Copyright 2021 Thales DIS design services SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Zineb EL KACIMI (zineb.el-kacimi@external.thalesgroup.com)


`ifndef __UVME_CVXIF_BASE_VSEQ_SV__
`define __UVME_CVXIF_BASE_VSEQ_SV__


class uvme_cvxif_base_vseq_c extends uvm_sequence #(uvma_cvxif_resp_item_c);

   `uvm_object_utils (uvme_cvxif_base_vseq_c)
   `uvm_declare_p_sequencer (uvma_cvxif_vsqr_c)

   uvma_cvxif_resp_item_c   resp_item;
   uvma_cvxif_req_item_c    req_item;

   uvma_cvxif_cfg_c    cfg;

   string info_tag = "CVXIF_BASE_VSEQ";

   extern function new(string name="uvme_cvxif_base_vseq");

   extern virtual task pre_body();

   extern virtual function string decode(input logic [31:0] instr);

   extern virtual function string compressed_decode(input logic [15:0] instr);

endclass

function uvme_cvxif_base_vseq_c::new(string name="uvme_cvxif_base_vseq");

   super.new(name);

endfunction : new

task uvme_cvxif_base_vseq_c::pre_body();

   req_item  = uvma_cvxif_req_item_c::type_id::create("req_item");
   resp_item = uvma_cvxif_resp_item_c::type_id::create("resp_item");

   cfg   = p_sequencer.cfg;

endtask

function string uvme_cvxif_base_vseq_c::compressed_decode(input logic [15:0] instr);

   bit [2:0] Cfunc3    = instr [15:13];
   bit [1:0] op        = instr [1:0];

   if (instr[1:0] != 2'b11) begin
      if (op == 2'b00 && Cfunc3 == 3'b111) begin
         if (!instr[12]) return ("CUS_CNOP");
         else return ("CUS_CADD");
      end
   end

   return ("ILLEGAL");

endfunction

function string uvme_cvxif_base_vseq_c::decode(input logic [31:0] instr);

   bit [6:0] opcode    = instr [6:0];
   bit [6:0] custom3   = 7'b1111011;
   bit [6:0] MADD      = 7'b1000011;
   bit [6:0] MSUB      = 7'b1000111;
   bit [6:0] NMADD     = 7'b1001111;
   bit [6:0] NMSUB     = 7'b1001011;
   bit [6:0] func7     = instr [31:25];
   bit [1:0] func2     = instr [26:25];
   bit [2:0] func3     = instr [14:12];
   bit [4:0] rd        = instr [11:7];
   bit [4:0] rs1       = instr [19:15];
   bit [4:0] rs2       = instr [24:20];

   if (opcode == custom3) begin
      if (func3 == 3'b001) begin
         if (func7 == 7'b0000011) begin
            return ("CUS_ADD_MULTI");
         end
         if (func7 == 7'b0000010) begin
            return ("CUS_DOUBLE_RS2");
         end
         if (func7 == 7'b0000001) begin
            return ("CUS_DOUBLE_RS1");
         end
         if (func7 == 7'b0000000) begin
            return ("CUS_ADD");
         end
      end
      if (func3 == 3'b000) begin
         if (func7 == 7'b0000000) begin
            return ("CUS_NOP");
         end
      end
   end
   else if (opcode == MADD) begin
      if (func3 == 3'b000 && func2 == 2'b00) begin
         return ("CUS_ADD_RS3_MADD");
      end
      if (func3 == 3'b001 && func7 == 7'b0000100) begin
         return ("CUS_ADD_RS3_RTYPE");
      end
   end
   else if (opcode == MSUB) begin
      if (func3 == 3'b000 && func2 == 2'b00) begin
         return ("CUS_ADD_RS3_MSUB");
      end
   end
   else if (opcode == NMADD) begin
      if (func3 == 3'b000 && func2 == 2'b00) begin
         return ("CUS_ADD_RS3_NMADD");
      end
   end
   else if (opcode == NMSUB) begin
      if (func3 == 3'b000 && func2 == 2'b00) begin
         return ("CUS_ADD_RS3_NMSUB");
      end
   end

   return ("ILLEGAL");

endfunction


`endif // __UVME_CVXIF_BASE_VSEQ_SV__
