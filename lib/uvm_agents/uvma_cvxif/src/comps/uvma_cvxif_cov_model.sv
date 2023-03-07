// Copyright 2021 Thales DIS design services SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Zineb EL KACIMI (zineb.el-kacimi@external.thalesgroup.com)


`ifndef __UVMA_CVXIF_COV_MODEL_SV__
`define __UVMA_CVXIF_COV_MODEL_SV__


   /*
   * Covergroups
   * Decalred at package-level to enable mutliple instances per monitor class (e.g. read/write)
   */
   //covergroup instances

covergroup cg_executed(
    string name
    ) with function sample(uvma_cvxif_req_item_c req_item);

    option.per_instance = 1;
    option.name = name;

   cp_instr : coverpoint req_item.issue_req.instr {
     wildcard bins CUS_ADD        = {32'b0000000??????????000?????1111011};
     wildcard bins CUS_ADD_RS3    = {32'b?????01??????????000?????1111011};
     wildcard bins CUS_ADD_MULTI  = {32'b0001000??????????000?????1111011};
     wildcard bins CUS_M_ADD      = {32'b0000100??????????000?????1111011};
     wildcard bins CUS_S_ADD      = {32'b0000110??????????000?????1111011};
     wildcard bins CUS_NOP        = {32'b00000000000000000000000001111011};
     wildcard bins CUS_EXC        = {32'b10000000000000000000000001111011};
   }

endgroup: cg_executed

covergroup cg_cus_instr(
    string name,
    bit rs3_valid
    ) with function sample(uvma_cvxif_req_item_c req_item);

   option.per_instance = 1;
   option.name = name;

   cp_rd : coverpoint req_item.issue_req.instr[11:7] {
    bins RD[] = {[1:31]};
   }

   cp_rs1 : coverpoint req_item.issue_req.instr[19:15] {
    bins RS1[] = {[0:31]};
   }

   cp_rs2 : coverpoint req_item.issue_req.instr[24:20] {
    bins RS2[] = {[0:31]};
   }

   cp_rs3 : coverpoint req_item.issue_req.instr[31:27] {
    ignore_bins IGN_RS3[] = {[0:31]} iff (!rs3_valid);
    bins RS3[] = {[0:31]};
   }

   `CVXIF_CP_BITWISE(cp_rs1_toggle, req_item.issue_req.rs[0], 1)
   `CVXIF_CP_BITWISE(cp_rs2_toggle, req_item.issue_req.rs[1], 1)
   `CVXIF_CP_BITWISE(cp_rs3_toggle, req_item.issue_req.rs[2], rs3_valid) //TODO : fix need more filtring

endgroup: cg_cus_instr

covergroup cg_request(
    string name
    ) with function sample(uvma_cvxif_req_item_c req_item);

    option.per_instance = 1;
    option.name = name;

   cp_instr : coverpoint req_item.issue_req.instr {
    wildcard bins CUS_ADD        = {32'b0000000??????????000?????1111011};
    wildcard bins CUS_ADD_RS3    = {32'b?????01??????????000?????1111011};
    wildcard bins CUS_ADD_MULTI  = {32'b0001000??????????000?????1111011};
    wildcard bins CUS_M_ADD      = {32'b0000100??????????000?????1111011};
    wildcard bins CUS_S_ADD      = {32'b0000110??????????000?????1111011};
    wildcard bins CUS_NOP        = {32'b00000000000000000000000001111011};
    wildcard bins CUS_EXC        = {32'b10000000000000000000000001111011};
   }

   cp_valid : coverpoint req_item.issue_valid {
    bins ISSUE_VALID [] = {[0:$]};
   }

   cp_ready : coverpoint req_item.issue_ready {
    bins ISSUE_READY [] = {[0:$]};
   }

   cp_id : coverpoint req_item.issue_req.id {
    bins ID [] = {[0:$]};
   }

   cp_rs_valid : coverpoint req_item.issue_req.rs_valid {
    bins RS_VALID [] = {3,7};
   }

   cp_mode : coverpoint req_item.issue_req.mode {
    bins MODE [] = {[0:$]};
   }

   cp_commit_id : coverpoint req_item.commit_req.id {
    bins ID_COMMIT [] = {[0:$]};
   }

   cp_commit_kill : coverpoint req_item.commit_req.commit_kill {
    bins COMMIT_KILL [] = {[0:$]};
   }

   cp_commit_valid : coverpoint req_item.commit_valid {
    bins COMMIT_VALID [] = {[0:$]};
   }

   cross_req : cross cp_instr, cp_id, cp_rs_valid, cp_mode;
   cross_valid_ready : cross cp_valid, cp_ready;
   cross_commit : cross cp_commit_valid, cp_commit_kill, cp_commit_id;

endgroup: cg_request

covergroup cg_response(
    string name,
    bit dual_read_write_support,
    bit load_store_support
    ) with function sample(uvma_cvxif_resp_item_c resp_item);

    option.per_instance = 1;
    option.name = name;

   cp_accept : coverpoint resp_item.issue_resp.accept {
    bins ACCEPT [] = {[0:$]};
   }

   cp_writeback : coverpoint resp_item.issue_resp.writeback {
    bins WRITEBACK [] = {[0:$]};
   }

   cp_dualwrite : coverpoint resp_item.issue_resp.dualwrite {
    ignore_bins IGN_BINS = cp_dualwrite iff(!dual_read_write_support);
    bins DUALWRITE [] = {[0:$]};
   }

   cp_dualread : coverpoint resp_item.issue_resp.dualread {
    ignore_bins IGN_BINS = cp_dualread iff(!dual_read_write_support);
    bins DUALREAD [] = {[0:$]};
   }

   cp_loadstore : coverpoint resp_item.issue_resp.loadstore {
    ignore_bins IGN_BINS = cp_loadstore iff(!load_store_support);
    bins LOADSTORE [] = {[0:$]};
   }

   cp_exc : coverpoint resp_item.issue_resp.exc {
    bins EXC [] = {[0:$]};
   }

   cross_resp0 : cross cp_accept, cp_writeback, cp_dualwrite, cp_dualread, cp_loadstore, cp_exc {
   illegal_bins ILLEGAL_BINS = binsof(cp_accept) intersect{0} &&
                              (binsof(cp_writeback) intersect{1} ||
                               binsof(cp_dualwrite) intersect{1} ||
                               binsof(cp_dualread) intersect{1}  ||
                               binsof(cp_loadstore) intersect{1} ||
                               binsof(cp_exc) intersect{1});
   ignore_bins IGN_CROSS = cross_resp0 iff(!dual_read_write_support || !load_store_support);
   }

   cross_resp1 : cross cp_accept, cp_writeback, cp_dualwrite, cp_dualread, cp_exc {
   illegal_bins ILLEGAL_BINS = binsof(cp_accept) intersect{0} &&
                              (binsof(cp_writeback) intersect{1} ||
                               binsof(cp_dualwrite) intersect{1} ||
                               binsof(cp_dualread) intersect{1}  ||
                               binsof(cp_exc) intersect{1});
   ignore_bins IGN_CROSS = cross_resp1 iff(!dual_read_write_support && load_store_support);
   }

   cross_resp2 : cross cp_accept, cp_writeback, cp_loadstore, cp_exc {
   illegal_bins ILLEGAL_BINS = binsof(cp_accept) intersect{0} &&
                              (binsof(cp_writeback) intersect{1} ||
                               binsof(cp_loadstore) intersect{1} ||
                               binsof(cp_exc) intersect{1});
   ignore_bins IGN_CROSS = cross_resp2 iff(dual_read_write_support && !load_store_support);
   }

   cross_resp3 : cross cp_accept, cp_writeback, cp_exc {
   illegal_bins ILLEGAL_BINS = binsof(cp_accept) intersect{0} &&
                              (binsof(cp_writeback) intersect{1} || binsof(cp_exc) intersect{1});
   ignore_bins IGN_CROSS = cross_resp3 iff(dual_read_write_support || load_store_support);
   }

endgroup: cg_response

covergroup cg_result(
    string name
    ) with function sample(uvma_cvxif_resp_item_c resp_item);

    option.per_instance = 1;
    option.name = name;

   cp_id : coverpoint resp_item.result.id {
    bins ID [] = {[0:$]};
   }

   cp_rd : coverpoint resp_item.result.rd {
    bins RD [] = {[0:31]};
   }

   `CVXIF_CP_BITWISE(cp_data_toggle, resp_item.result.data, 1)

   cp_we : coverpoint resp_item.result.we {
    bins WE [] = {[0:$]};
   }

   cp_exc : coverpoint resp_item.result.exc {
    bins EXC [] = {[0:$]};
   }

   cp_exccode : coverpoint resp_item.result.exccode {
    bins EXCCODE [] = {[0:$]};
   }

   cp_result_valid : coverpoint resp_item.result_valid {
    bins RESULT_VALID [] = {[0:$]};
   }

   cp_result_ready : coverpoint resp_item.result_ready {
    bins RESULT_READY [] = {[0:$]};
   }

    cross_result : cross cp_id, cp_we, cp_exc, cp_exccode;
    cross_valid_ready : cross cp_result_valid, cp_result_ready;

endgroup: cg_result

class uvma_cvxif_cov_model_c extends uvm_component;

   // Objects
   uvma_cvxif_cfg_c         cfg      ;
   uvma_cvxif_cntxt_c       cntxt    ;
   uvma_cvxif_req_item_c    req_item ;
   uvma_cvxif_resp_item_c   resp_item;

   // TLM
   uvm_tlm_analysis_fifo#(uvma_cvxif_req_item_c )  req_item_fifo;
   uvm_tlm_analysis_fifo#(uvma_cvxif_resp_item_c)  resp_item_fifo;

   `uvm_component_utils_begin(uvma_cvxif_cov_model_c)
      `uvm_field_object(cfg  , UVM_DEFAULT)
      `uvm_field_object(cntxt, UVM_DEFAULT)
   `uvm_component_utils_end

   // Covergroups
   //ADD INSTRUCTIONS
   cg_cus_instr cus_add_cg;
   cg_cus_instr cus_add_rs3_cg;
   cg_cus_instr cus_add_multi_cg;
   cg_cus_instr cus_add_m_cg;
   cg_cus_instr cus_add_s_cg;

   //Sequential instruction
   cg_executed cus_seq_cg;
   cg_request request_cg;
   cg_response response_cg;
   cg_result result_cg;
   /**
    * Default constructor.
    */
   extern function new(string name="uvma_cvxif_cov_model", uvm_component parent=null);

   /**
    * 1. Ensures cfg & cntxt handles are not null.
    * 2. Builds fifos.
    */
   extern virtual function void build_phase(uvm_phase phase);

   /**
    * Forks all sampling loops
    */
   extern virtual task run_phase(uvm_phase phase);

   /**
    * TODO Describe uvma_cvxif_cov_model_c::sample_cfg()
    */
   extern function void sample_cfg();

   /**
    * TODO Describe uvma_cvxif_cov_model_c::sample_cntxt()
    */
   extern function void sample_cntxt();

   /**
    * TODO Describe uvma_cvxif_cov_model_c::sample_req_item()
    */
   extern function void sample_req_item(uvma_cvxif_req_item_c req_item);

   /**
    * TODO Describe uvma_cvxif_cov_model_c::sample_resp_item()
    */
   extern function void sample_resp_item(uvma_cvxif_resp_item_c resp_item);

endclass : uvma_cvxif_cov_model_c

function uvma_cvxif_cov_model_c::new(string name="uvma_cvxif_cov_model", uvm_component parent=null);

   super.new(name, parent);

endfunction : new


function void uvma_cvxif_cov_model_c::build_phase(uvm_phase phase);

   super.build_phase(phase);

   void'(uvm_config_db#(uvma_cvxif_cfg_c)::get(this, "", "cfg", cfg));
   if (!cfg) begin
      `uvm_fatal("CFG", "Configuration handle is null")
   end

   void'(uvm_config_db#(uvma_cvxif_cntxt_c)::get(this, "", "cntxt", cntxt));
   if (!cntxt) begin
      `uvm_fatal("CNTXT", "Context handle is null")
   end

   cus_add_cg = new("cus_add_cg",
                    .rs3_valid(0));
   cus_add_rs3_cg = new("cus_add_rs3_cg",
                    .rs3_valid(1));
   cus_add_multi_cg = new("cus_add_multi_cg",
                    .rs3_valid(0));
   cus_add_m_cg = new("cus_add_m_cg",
                    .rs3_valid(0));
   cus_add_s_cg = new("cus_add_s_cg",
                    .rs3_valid(0));

   cus_seq_cg  = new("cus_seq_cg");
   request_cg  = new("request_cg");
   response_cg = new("response_cg",
                    .dual_read_write_support(cfg.dual_read_write_support_x),
                    .load_store_support(cfg.load_store_support_x));
   result_cg   = new("result_cg");

   req_item_fifo   = new("req_item_fifo" , this);
   resp_item_fifo  = new("resp_item_fifo", this);

endfunction : build_phase


task uvma_cvxif_cov_model_c::run_phase(uvm_phase phase);

   super.run_phase(phase);
   if (cfg.enabled && cfg.cov_model_enabled) begin
      fork
         // Configuration
         forever begin
            cntxt.sample_cfg_e.wait_trigger();
            sample_cfg();
         end

         // Context
         forever begin
            cntxt.sample_cntxt_e.wait_trigger();
            sample_cntxt();
         end

         // 'mstr' sequence items
         forever begin
            req_item_fifo.get(req_item);
            sample_req_item(req_item);
         end

         // 'slv' sequence items
          forever begin
            resp_item_fifo.get(resp_item);
            sample_resp_item(resp_item);
         end
      join_none
   end

endtask : run_phase


function void uvma_cvxif_cov_model_c::sample_cfg();

   // TODO Implement uvma_cvxif_cov_model_c::sample_cfg();

endfunction : sample_cfg


function void uvma_cvxif_cov_model_c::sample_cntxt();

   // TODO Implement uvma_cvxif_cov_model_c::sample_cntxt();

endfunction : sample_cntxt


function void uvma_cvxif_cov_model_c::sample_req_item(uvma_cvxif_req_item_c req_item);

  // TODO Implement uvma_cvxif_cov_model_c::sample_req_item();
   bit [6:0] opcode    = req_item.issue_req.instr [6:0];
   bit [6:0] custom3   = 7'b1111011;
   bit [6:0] func7     = req_item.issue_req.instr [31:25];
   bit [1:0] func2     = req_item.issue_req.instr [26:25];
   bit [1:0] func3     = req_item.issue_req.instr [14:12];
   bit [4:0] rd        = req_item.issue_req.instr [11:7];
   bit [4:0] rs1       = req_item.issue_req.instr [19:15];
   bit [4:0] rs2       = req_item.issue_req.instr [24:20];

   if (opcode != custom3 ) begin
     `uvm_error("CVXIF", $sformatf("Could not sample instruction: %b", req_item.issue_req.instr));
   end
   else begin
      if (func3 == 0) begin
         if (rd != 0) begin
            if (func7 == 0) begin
              cus_add_cg.sample(req_item);
            end
            if (func2 == 2'b01) begin
               cus_add_rs3_cg.sample(req_item);
            end
            if (func7 == 7'b0001000) begin
               cus_add_multi_cg.sample(req_item);
            end
            if (func7 == 7'b0000010) begin
               cus_add_m_cg.sample(req_item);
            end
            if (func7 == 7'b0000110) begin
               cus_add_s_cg.sample(req_item);
            end
         end
      end
      else begin
        `uvm_error("CVXIF", $sformatf("Could not sample instruction: %b", req_item.issue_req.instr));
      end
   end
  cus_seq_cg.sample(req_item);
  request_cg.sample(req_item);

endfunction : sample_req_item

function void uvma_cvxif_cov_model_c::sample_resp_item(uvma_cvxif_resp_item_c resp_item);

   response_cg.sample(resp_item);
   result_cg.sample(resp_item);

endfunction : sample_resp_item

`endif // __UVMA_CVXIF_COV_MODEL_SV__
