

// Copyright 2021 Thales DIS design services SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Zineb EL KACIMI (zineb.el-kacimi@external.thalesgroup.com)

`ifndef __UVMA_CVXIF_MON_SV__
`define __UVMA_CVXIF_MON_SV__


class uvma_cvxif_mon_c extends uvm_monitor;

   localparam ID_WIDTH   = cvxif_pkg::X_ID_WIDTH;

   //objects
   uvma_cvxif_cfg_c    cfg;
   uvma_cvxif_cntxt_c  cntxt;

   // add to factory
   `uvm_component_utils_begin(uvma_cvxif_mon_c)
      `uvm_field_object(cfg,   UVM_DEFAULT)
      `uvm_field_object(cntxt, UVM_DEFAULT)
   `uvm_component_utils_end

   string info_tag = "CVXIF_MONITOR";

   int req_valid;
   int passed_id;

   int commit_id_lst[$];
   int issue_id_lst[int];
   int accepted_issue_id[int];
   int c;
   int r;

   uvm_analysis_port#(uvma_cvxif_req_item_c)  req_ap;
   uvm_analysis_port#(uvma_cvxif_resp_item_c) resp_ap;

   uvma_cvxif_req_item_c req_tr;
   uvma_cvxif_resp_item_c resp_tr;

   /**
    * Default constructor.
    */
   extern function new(string name="uvma_cvxif_mon", uvm_component parent=null);

   /**
    * 1. Ensures vif handle is not null.
    * 2. Builds ap.
   */
   extern virtual function void build_phase(uvm_phase phase);


   /**
    * Monitoring transaction
   */
   extern virtual task run_phase(uvm_phase phase);

   /**
    * Send transaction request to sequencer
   */
   extern task send_req_to_sqr(uvma_cvxif_req_item_c req);

   /**
    * Collect and send response items to coverage model
   */
   extern task collect_and_send_resp(uvma_cvxif_resp_item_c resp_tr);

   /**
    * Protocol checkers for id used in each interface
   */
   extern task chk_id_issue_commit(bit [ID_WIDTH-1:0] id);
   extern task chk_id_result();

endclass : uvma_cvxif_mon_c

function uvma_cvxif_mon_c::new(string name="uvma_cvxif_mon", uvm_component parent=null);

   super.new(name, parent);

endfunction : new

function void uvma_cvxif_mon_c::build_phase(uvm_phase phase);

   super.build_phase(phase);

   void'(uvm_config_db#(uvma_cvxif_cfg_c)::get(this, "", "cfg", cfg));
   if (cfg == null) begin
      `uvm_fatal("CFG", "Configuration handle is null")
   end

   void'(uvm_config_db#(uvma_cvxif_cntxt_c)::get(this, "", "cntxt", cntxt));
   if (cntxt == null) begin
      `uvm_fatal("CNTXT", "Context handle is null")
   end

   req_ap = new("req_ap", this);
   resp_ap = new("resp_ap", this);

endfunction : build_phase

task uvma_cvxif_mon_c::run_phase(uvm_phase phase);

   super.run_phase(phase);

   fork
      begin
         chk_id_result();
      end
      begin
         collect_and_send_resp(resp_tr);
      end
      begin
      forever begin
         // wait for a transaction
         wait (cntxt.vif.cvxif_req_i.x_issue_valid || cntxt.vif.cvxif_req_i.x_commit_valid);
         req_tr = uvma_cvxif_req_item_c::type_id::create("req_tr");
         `uvm_info(info_tag, $sformatf("New transaction received"), UVM_HIGH);

         fork
            begin
               //detect accepted issue
               if (cntxt.vif.cvxif_resp_o.x_issue_resp.accept) begin
                  accepted_issue_id[cntxt.vif.cvxif_req_i.x_issue_req.id] = (cntxt.vif.cvxif_req_i.x_issue_req.id);
               end
            end
            begin
               //Detect an issue_req transaction
               if (cntxt.vif.cvxif_req_i.x_issue_valid) begin
                  int i = cntxt.vif.cvxif_req_i.x_issue_req.id;
                  issue_id_lst[i] = i;
                  req_tr.issue_valid     = cntxt.vif.cvxif_req_i.x_issue_valid;
                  req_tr.issue_req.instr = cntxt.vif.cvxif_req_i.x_issue_req.instr;
                  req_tr.issue_req.rs_valid = cntxt.vif.cvxif_req_i.x_issue_req.rs_valid;
                  req_tr.issue_req.id    = cntxt.vif.cvxif_req_i.x_issue_req.id;
                  req_tr.issue_req.mode  = cntxt.vif.cvxif_req_i.x_issue_req.mode;
                  req_tr.issue_ready     = cntxt.vif.cvxif_resp_o.x_issue_ready;
                  for (int i=0; i<3; i++) begin
                     if (cntxt.vif.cvxif_req_i.x_issue_req.rs_valid[i]) begin
                       req_tr.issue_req.rs[i] = cntxt.vif.cvxif_req_i.x_issue_req.rs[i];
                     end
                     else req_tr.issue_req.rs[i] = 0;
                  end
                  //Publish request transaction
                  `uvm_info(info_tag, $sformatf("Monitor issue_req: instr = %b, id= %d, mode= %d, rs[0] = %h, rs[1] = %h, rs[2] = %h",
                    cntxt.vif.cvxif_req_i.x_issue_req.instr, cntxt.vif.cvxif_req_i.x_issue_req.id, cntxt.vif.cvxif_req_i.x_issue_req.mode, cntxt.vif.cvxif_req_i.x_issue_req.rs[0], cntxt.vif.cvxif_req_i.x_issue_req.rs[1], cntxt.vif.cvxif_req_i.x_issue_req.rs[2]), UVM_LOW);
                  req_valid=1;
               end
            end
            begin
               //detect commit transaction
               if (cntxt.vif.cvxif_req_i.x_commit_valid==1) begin
                  req_tr.commit_valid           = cntxt.vif.cvxif_req_i.x_commit_valid;
                  req_tr.commit_req.id          = cntxt.vif.cvxif_req_i.x_commit.id;
                  req_tr.commit_req.commit_kill = cntxt.vif.cvxif_req_i.x_commit.x_commit_kill;
                  req_tr.result_ready           = cntxt.vif.cvxif_req_i.x_result_ready;
                  //check id protocol
                  chk_id_issue_commit(cntxt.vif.cvxif_req_i.x_commit.id);
                  //Publish request transaction
                  `uvm_info(info_tag, $sformatf("Monitor commit_req: id = %d, commit_kill = %d",
                  cntxt.vif.cvxif_req_i.x_commit.id, cntxt.vif.cvxif_req_i.x_commit.x_commit_kill), UVM_LOW);
                  req_valid=1;
               end
            end
         join
         if (req_valid==1) begin
            `uvm_info(info_tag, $sformatf("Sending req to sqr"), UVM_HIGH);
            send_req_to_sqr(req_tr);
            req_valid=0;
         end
         //detect the new/end of transaction (id changed with issue valid==1 <=> new transaction)
         passed_id = req_tr.issue_req.id;
         do begin
            @(cntxt.vif.monitor_cb);
            end
         while ((cntxt.vif.cvxif_req_i.x_issue_valid) && (passed_id==cntxt.vif.cvxif_req_i.x_issue_req.id));
      end
   end
   join_any

endtask

task uvma_cvxif_mon_c::send_req_to_sqr(uvma_cvxif_req_item_c req);

   req_ap.write(req);

endtask : send_req_to_sqr

task uvma_cvxif_mon_c::collect_and_send_resp(uvma_cvxif_resp_item_c resp_tr);

   forever begin
      fork
         begin
            wait (cntxt.vif.cvxif_resp_o.x_issue_ready && cntxt.vif.cvxif_req_i.x_issue_valid);
               resp_tr = uvma_cvxif_resp_item_c::type_id::create("resp_tr");
               resp_tr.issue_resp.accept    = cntxt.vif.cvxif_resp_o.x_issue_resp.accept;
               resp_tr.issue_resp.writeback = cntxt.vif.cvxif_resp_o.x_issue_resp.writeback;
               resp_tr.issue_resp.exc       = cntxt.vif.cvxif_resp_o.x_issue_resp.exc;
               resp_tr.issue_resp.loadstore = cntxt.vif.cvxif_resp_o.x_issue_resp.loadstore;
               resp_tr.issue_resp.dualwrite = cntxt.vif.cvxif_resp_o.x_issue_resp.dualwrite;
               resp_tr.issue_resp.dualread  = cntxt.vif.cvxif_resp_o.x_issue_resp.dualread;
         end
         begin
            wait (cntxt.vif.cvxif_resp_o.x_result_valid && cntxt.vif.cvxif_req_i.x_result_ready);
               resp_tr.result_valid     = cntxt.vif.cvxif_resp_o.x_result_valid;
               resp_tr.result.id        = cntxt.vif.cvxif_resp_o.x_result.id;
               resp_tr.result.data      = cntxt.vif.cvxif_resp_o.x_result.data;
               resp_tr.result.rd        = cntxt.vif.cvxif_resp_o.x_result.rd;
               resp_tr.result.we        = cntxt.vif.cvxif_resp_o.x_result.we;
               resp_tr.result.exc       = cntxt.vif.cvxif_resp_o.x_result.exc;
               resp_tr.result.exccode   = cntxt.vif.cvxif_resp_o.x_result.exccode;
         end
      join_any
      resp_ap.write(resp_tr);
      @(cntxt.vif.monitor_cb);
   end

endtask

task uvma_cvxif_mon_c::chk_id_issue_commit(bit [ID_WIDTH-1:0] id);

   if (!issue_id_lst.exists(id)) begin
         `uvm_error("Protocol_chk", "Failure: Commit transaction without its corresponding issue transaction");
   end
   else begin
      issue_id_lst.delete(id); //id is no longer available for commit_intf until another issue with same id is sent
      if (!cntxt.vif.cvxif_req_i.x_commit.x_commit_kill) begin
         commit_id_lst.push_back(id);  //id available for result intf
      end
      if (accepted_issue_id.exists(id) && !cntxt.vif.cvxif_req_i.x_commit.x_commit_kill) begin
         `uvm_error("Protocol_chk", "Failure: Issue transaction uniqueness");
      end
      else begin
         accepted_issue_id.delete(id); ////id is now available for issue_intf
      end
   end

endtask

task uvma_cvxif_mon_c::chk_id_result();

   forever begin
     @(cntxt.vif.monitor_cb);
     if(cntxt.vif.cvxif_resp_o.x_result_valid) begin
        accepted_issue_id.delete(cntxt.vif.cvxif_resp_o.x_result.id);
        for (int i=0; i<commit_id_lst.size(); i++) begin
           r = 0;
           if (commit_id_lst[i] == cntxt.vif.cvxif_resp_o.x_result.id) begin
              commit_id_lst.delete(i); //id is now available for commit_intf
              r = 1;
              break;
            end
        end
        if (r==0) begin
           `uvm_error("Protocol_chk", "Result uniqueness or instruction already killed")
        end
     end
   end

endtask


`endif // __UVMA_CVXIF_MON_SV__
