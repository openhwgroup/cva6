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

    // add to factory
   `uvm_component_utils(uvma_cvxif_mon_c)

   virtual uvma_cvxif_intf cvxif_vif;

   string info_tag = "CVXIF_MONITOR";

   int req_valid,
       passed_id;

   uvm_analysis_port#(uvma_cvxif_req_item_c)  req_ap;

   uvma_cvxif_req_item_c req_tr;

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

endclass : uvma_cvxif_mon_c

function uvma_cvxif_mon_c::new(string name="uvma_cvxif_mon", uvm_component parent=null);

   super.new(name, parent);

endfunction : new

function void uvma_cvxif_mon_c::build_phase(uvm_phase phase);

   super.build_phase(phase);

   //Get the virtual interface handle from the configuration db
   if (! uvm_config_db#(virtual uvma_cvxif_intf)::get(this, "", "cvxif_vif", cvxif_vif)) begin
   `uvm_fatal (get_type_name (), "CVXIF VIF handle not found")
   end

   req_ap = new("req_ap", this);

endfunction : build_phase

task uvma_cvxif_mon_c::run_phase(uvm_phase phase);

   super.run_phase(phase);

   forever begin

    `uvm_info(info_tag, $sformatf("Waiting for a new transaction"), UVM_HIGH);
    // wait for a transaction
    wait (cvxif_vif.cvxif_req_i.x_issue_valid && cvxif_vif.cvxif_req_i.x_commit_valid);
    req_tr = uvma_cvxif_req_item_c::type_id::create("req_tr");
    `uvm_info(info_tag, $sformatf("New transaction received"), UVM_HIGH);

    fork
     begin
      //Detect an issue_req transaction
      if (cvxif_vif.cvxif_req_i.x_issue_valid) begin
        req_tr.issue_valid = cvxif_vif.cvxif_req_i.x_issue_valid;
        req_tr.issue_req.instr = cvxif_vif.cvxif_req_i.x_issue_req.instr;
        req_tr.issue_req.id = cvxif_vif.cvxif_req_i.x_issue_req.id;
        req_tr.issue_req.mode = cvxif_vif.cvxif_req_i.x_issue_req.mode;
        req_tr.issue_ready = cvxif_vif.cvxif_resp_o.x_issue_ready;
        for (int i=0; i<3; i++) begin
          if (cvxif_vif.cvxif_req_i.x_issue_req.rs_valid[i]) begin
            req_tr.issue_req.rs[i] = cvxif_vif.cvxif_req_i.x_issue_req.rs[i];
          end
          else req_tr.issue_req.rs[i] = 0;
        end
      //Publish request transaction
      `uvm_info(info_tag, $sformatf("Monitor issue_req: instr = %b, id= %d, mode= %d, rs[0] = %h, rs[1] = %h, rs[2] = %h",
        cvxif_vif.cvxif_req_i.x_issue_req.instr, cvxif_vif.cvxif_req_i.x_issue_req.id, cvxif_vif.cvxif_req_i.x_issue_req.mode, cvxif_vif.cvxif_req_i.x_issue_req.rs[0], cvxif_vif.cvxif_req_i.x_issue_req.rs[1], cvxif_vif.cvxif_req_i.x_issue_req.rs[2]), UVM_LOW);
      req_valid=1;
      end
     end
     begin
      //detect commit transaction
      if (cvxif_vif.cvxif_req_i.x_commit_valid==1) begin
        req_tr.commit_valid = cvxif_vif.cvxif_req_i.x_commit_valid;
        req_tr.commit_req.id=cvxif_vif.cvxif_req_i.x_commit.id;
        req_tr.commit_req.commit_kill=cvxif_vif.cvxif_req_i.x_commit.x_commit_kill;
        req_tr.result_ready = cvxif_vif.cvxif_req_i.x_result_ready;
        //Publish request transaction
        `uvm_info(info_tag, $sformatf("Monitor commit_req: id = %d, commit_kill = %d",
          cvxif_vif.cvxif_req_i.x_commit.id, cvxif_vif.cvxif_req_i.x_commit.x_commit_kill), UVM_LOW);
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
       @(cvxif_vif.monitor_cb);
       end
    while ((cvxif_vif.cvxif_req_i.x_issue_valid) && (passed_id==cvxif_vif.cvxif_req_i.x_issue_req.id));

   end

endtask

task uvma_cvxif_mon_c::send_req_to_sqr(uvma_cvxif_req_item_c req);
   req_ap.write(req);
endtask : send_req_to_sqr


`endif // __UVMA_CVXIF_MON_SV__
