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

   uvma_cvxif_resp_item_c        resp_item;
   uvma_cvxif_req_item_c         req_item;

   int instr_num;
   string info_tag = "CVXIF_BASE_SEQ";

   extern function new(string name="uvma_cvxif_base_seq");

   extern virtual task pre_body();

   extern function int decode(input logic [31:0] instr);

endclass

function uvma_cvxif_base_seq_c::new(string name="uvma_cvxif_base_seq");

   super.new(name);

endfunction : new

task uvma_cvxif_base_seq_c::pre_body();

    req_item= uvma_cvxif_req_item_c::type_id::create("req_item");
    resp_item= uvma_cvxif_resp_item_c::type_id::create("resp_item");

endtask

function int uvma_cvxif_base_seq_c::decode(input logic [31:0] instr);

   int instr_num = 0;
   logic [31:0] copro_instr = 0;

   for (int i=0; i<NumInstr; i++) begin
     copro_instr = instr & OffloadInstr[i].mask;
     if (OffloadInstr[i].instr == copro_instr) begin
         instr_num = i+1;
         return (instr_num);
     end
     else continue;
   end
   return (instr_num);
endfunction


`endif // __UVMA_CVXIF_BASE_SEQ_SV__
