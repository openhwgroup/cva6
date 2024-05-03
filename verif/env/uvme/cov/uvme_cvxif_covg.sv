//
// Copyright 2020 OpenHW Group
// Copyright 2021 Thales DIS Design Services SAS
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


`ifndef __UVMA_CVXIF_COVG_SV__
`define __UVMA_CVXIF_COVG_SV__

`ifdef UNSUPPORTED_WITH //TODO - Remove ifdef when the issue in VCS simulator is fixed
  `define WITH iff
`else
   `define WITH with
`endif


covergroup cg_executed(
    string name,
    bit seq_cus_instr_x2_enabled
    ) with function
    sample(uvma_cvxif_req_item_c req_item,
           uvma_cvxif_req_item_c prev_req_item);

    option.per_instance = 1;
    option.name = name;

   cp_instr : coverpoint req_item.issue_req.instr {
     wildcard bins CUS_ADD        = {32'b0000000??????????001?????1111011};
     wildcard bins CUS_ADD_RS3    = {32'b?????01??????????000?????1111011};
     wildcard bins CUS_ADD_MULTI  = {32'b0001000??????????000?????1111011};
     wildcard bins CUS_U_ADD      = {32'b0000010??????????000?????1111011};
     wildcard bins CUS_S_ADD      = {32'b0000110??????????000?????1111011};
     wildcard bins CUS_NOP        = {32'b00000000000000000000000001111011};
     wildcard bins CUS_EXC        = {32'b110000000000?????010000001111011};
   }

   cp_prev_instr : coverpoint prev_req_item.issue_req.instr iff (prev_req_item != null) {
     ignore_bins IGN_X2_OFF = {[0:$]} `WITH (!seq_cus_instr_x2_enabled);
     wildcard bins CUS_ADD        = {32'b0000000??????????001?????1111011};
     wildcard bins CUS_ADD_RS3    = {32'b?????01??????????000?????1111011};
     wildcard bins CUS_ADD_MULTI  = {32'b0001000??????????000?????1111011};
     wildcard bins CUS_U_ADD      = {32'b0000010??????????000?????1111011};
     wildcard bins CUS_S_ADD      = {32'b0000110??????????000?????1111011};
     wildcard bins CUS_NOP        = {32'b00000000000000000000000001111011};
     wildcard bins CUS_EXC        = {32'b110000000000?????010000001111011};
   }

   cross_seq_cus_instr_x2 : cross cp_instr, cp_prev_instr;

endgroup: cg_executed

covergroup cg_cus_add_instr(
    string name,
    bit reg_cus_crosses_enabled,
    bit rs3_valid
    ) with function sample(uvma_cvxif_req_item_c req_item);

   option.per_instance = 1;
   option.name = name;

   cp_rd : coverpoint req_item.issue_req.instr[11:7] {
    bins RD[] = {[0:31]};
   }

   cp_rs1 : coverpoint req_item.issue_req.instr[19:15] {
    bins RS1[] = {[0:31]};
   }

   cp_rs2 : coverpoint req_item.issue_req.instr[24:20] {
    bins RS2[] = {[0:31]};
   }

   cp_rs3 : coverpoint req_item.issue_req.instr[31:27] {
    ignore_bins IGN_RS3[] = {[0:31]} `WITH (!rs3_valid);
    bins RS3[] = {[0:31]};
   }

   cross_rd_rs1 : cross cp_rd, cp_rs1 {
    ignore_bins IGN_OFF = cross_rd_rs1 `WITH (!reg_cus_crosses_enabled);
   }

   cross_rd_rs2 : cross cp_rd, cp_rs2 {
    ignore_bins IGN_OFF = cross_rd_rs2 `WITH (!reg_cus_crosses_enabled);
   }

   cross_rd_rs3 : cross cp_rd, cp_rs3 {
    ignore_bins IGN_OFF = cross_rd_rs3 `WITH (!reg_cus_crosses_enabled || !rs3_valid);
   }

   `CVXIF_CP_BITWISE(cp_rs1_toggle, req_item.issue_req.rs[0], 1)
   `CVXIF_CP_BITWISE(cp_rs2_toggle, req_item.issue_req.rs[1], 1)
   `CVXIF_CP_BITWISE(cp_rs3_toggle, req_item.issue_req.rs[2], rs3_valid) //TODO : fix need more filtring

endgroup: cg_cus_add_instr

covergroup cg_cus_instr(
    string name
    ) with function sample(uvma_cvxif_req_item_c req_item);

   option.per_instance = 1;
   option.name = name;

   cp_rs1 : coverpoint req_item.issue_req.instr[19:15] {
    bins RS1[] = {[0:31]};
   }

endgroup: cg_cus_instr

class uvme_cvxif_covg_c extends uvm_component;

    /*
    * Class members
    */
   // Objects
   uvme_cva6_cfg_c         cfg      ;
   uvme_cva6_cntxt_c       cntxt    ;

   uvma_cvxif_req_item_c    req_item;
   uvma_cvxif_req_item_c    prev_req_item;

   // TLM
   uvm_tlm_analysis_fifo#(uvma_cvxif_req_item_c )  req_item_fifo;

   `uvm_component_utils_begin(uvme_cvxif_covg_c)
      `uvm_field_object(cfg  , UVM_DEFAULT)
      `uvm_field_object(cntxt, UVM_DEFAULT)
   `uvm_component_utils_end

      // Covergroups
   //ADD INSTRUCTIONS
   cg_cus_add_instr cus_add_cg;
   cg_cus_add_instr cus_add_rs3_cg;
   cg_cus_add_instr cus_add_multi_cg;
   cg_cus_add_instr cus_add_u_cg;
   cg_cus_add_instr cus_add_s_cg;
   cg_cus_instr cus_exc_cg;

   //Sequential instruction
   cg_executed cus_seq_cg;

   extern function new(string name = "cvxif_covg", uvm_component parent = null);
   extern function void build_phase(uvm_phase phase);
   extern task run_phase(uvm_phase phase);

   extern task sample_cvxif_req(uvma_cvxif_req_item_c req_item);

endclass : uvme_cvxif_covg_c

function uvme_cvxif_covg_c::new(string name = "cvxif_covg", uvm_component parent = null);

   super.new(name, parent);

endfunction : new

function void uvme_cvxif_covg_c::build_phase(uvm_phase phase);

   super.build_phase(phase);

   void'(uvm_config_db#(uvme_cva6_cfg_c)::get(this, "", "cfg", cfg));
   if (!cfg) begin
      `uvm_fatal("CFG", "Configuration handle is null")
   end

   void'(uvm_config_db#(uvme_cva6_cntxt_c)::get(this, "", "cntxt", cntxt));
   if (!cntxt) begin
      `uvm_fatal("CNTXT", "Context handle is null")
   end

   cus_add_cg = new("cus_add_cg",
                    .reg_cus_crosses_enabled(cfg.cvxif_cfg.reg_cus_crosses_enabled),
                    .rs3_valid(0));
   cus_add_rs3_cg = new("cus_add_rs3_cg",
                    .reg_cus_crosses_enabled(cfg.cvxif_cfg.reg_cus_crosses_enabled),
                    .rs3_valid(1));
   cus_add_multi_cg = new("cus_add_multi_cg",
                    .reg_cus_crosses_enabled(cfg.cvxif_cfg.reg_cus_crosses_enabled),
                    .rs3_valid(0));
   cus_add_u_cg = new("cus_add_u_cg",
                    .reg_cus_crosses_enabled(cfg.cvxif_cfg.reg_cus_crosses_enabled),
                    .rs3_valid(0));
   cus_add_s_cg = new("cus_add_s_cg",
                    .reg_cus_crosses_enabled(cfg.cvxif_cfg.reg_cus_crosses_enabled),
                    .rs3_valid(0));
   cus_exc_cg = new("cus_exc_cg");

   cus_seq_cg  = new("cus_seq_cg",
                     .seq_cus_instr_x2_enabled(cfg.cvxif_cfg.seq_cus_instr_x2_enabled));

   req_item_fifo   = new("req_item_fifo" , this);

endfunction : build_phase

task uvme_cvxif_covg_c::run_phase(uvm_phase phase);

   super.run_phase(phase);

   `uvm_info("CVXIFCOVG", "The CVXIF coverage model is running", UVM_LOW);
   forever begin
      req_item_fifo.get(req_item);
      sample_cvxif_req(req_item);
   end

endtask : run_phase

task uvme_cvxif_covg_c::sample_cvxif_req(uvma_cvxif_req_item_c req_item);

   logic                 have_sample = 0;
   bit [6:0] opcode    = req_item.issue_req.instr [6:0];
   bit [6:0] custom3   = 7'b1111011;
   bit [6:0] func7     = req_item.issue_req.instr [31:25];
   bit [1:0] func2     = req_item.issue_req.instr [26:25];
   bit [2:0] func3     = req_item.issue_req.instr [14:12];
   bit [4:0] rd        = req_item.issue_req.instr [11:7];
   bit [4:0] rs1       = req_item.issue_req.instr [19:15];
   bit [4:0] rs2       = req_item.issue_req.instr [24:20];

   if (opcode == custom3) begin
      if (func3 == 3'b000) begin
         if (func7 == 7'b0000000 && rd != 0) begin
            cus_add_cg.sample(req_item);
            cus_seq_cg.sample(req_item,
                              prev_req_item);
              // Move instructions down the pipeline
            prev_req_item  = req_item;
            have_sample = 1;
         end
         if (func7 == 7'b0001000) begin
            cus_add_multi_cg.sample(req_item);
            cus_seq_cg.sample(req_item,
                              prev_req_item);
              // Move instructions down the pipeline
            prev_req_item  = req_item;
            have_sample = 1;
         end
         if (func2 == 2'b01) begin
            cus_add_rs3_cg.sample(req_item);
            cus_seq_cg.sample(req_item,
                              prev_req_item);
              // Move instructions down the pipeline
            prev_req_item  = req_item;
            have_sample = 1;
         end
         if (func7 == 7'b0000010) begin
            cus_add_u_cg.sample(req_item);
            cus_seq_cg.sample(req_item,
                              prev_req_item);
              // Move instructions down the pipeline
            prev_req_item  = req_item;
            have_sample = 1;
         end
         if (func7 == 7'b0000110) begin
            cus_add_s_cg.sample(req_item);
            cus_seq_cg.sample(req_item,
                              prev_req_item);
              // Move instructions down the pipeline
            prev_req_item  = req_item;
            have_sample = 1;
         end
         if (func7 == 7'b0000000 && rd == 0 && rs1 == 0 && rs2 == 0) begin
            cus_seq_cg.sample(req_item,
                              prev_req_item);
              // Move instructions down the pipeline
            prev_req_item  = req_item;
            have_sample = 1;
         end
      end
      if (func3 == 3'b001) begin
         if (func7 == 7'b0000000) begin
            cus_add_cg.sample(req_item);
            cus_seq_cg.sample(req_item,
                              prev_req_item);
              // Move instructions down the pipeline
            prev_req_item  = req_item;
            have_sample = 1;
         end
      end
      if (func3 == 3'b010 && rd == 0 && rs2 == 0) begin
         if (func7 == 7'b1100000) begin
            cus_exc_cg.sample(req_item);
            cus_seq_cg.sample(req_item,
                              prev_req_item);
              // Move instructions down the pipeline
            prev_req_item  = req_item;
            have_sample = 1;
         end
      end
   end
   if (!have_sample) `uvm_warning("CVXIF", $sformatf("Could not sample instruction: %b", req_item.issue_req.instr));

endtask : sample_cvxif_req
`endif // __UVMA_CVXIF_COVG_SV__

