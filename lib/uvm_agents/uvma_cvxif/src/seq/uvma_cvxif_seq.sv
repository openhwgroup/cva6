// Copyright 2021 Thales DIS design services SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Zineb EL KACIMI (zineb.el-kacimi@external.thalesgroup.com)

`ifndef __UVMA_CVXIF_SEQ_SV__
`define __UVMA_CVXIF_SEQ_SV__


class uvma_cvxif_seq_c extends uvma_cvxif_base_seq_c#(uvma_cvxif_resp_item_c);

   `uvm_object_utils (uvma_cvxif_seq_c)
   `uvm_declare_p_sequencer (uvma_cvxif_sqr_c)

   string info_tag = "CVXIF_SEQ_RESP";
   string instr;

   /**
    * Default constructor.
   */
   extern function new(string name="uvma_cvxif_seq");

   /**
    * Send the Sequence Response to the Sequencer.
   */
   extern task send_resp(uvma_cvxif_resp_item_c resp);

   /**
    * Default response in case of illegal/inaccepted instruction.
    * Or in case of an invalid issue_req
   */
   extern task do_default();

   /**
    * Generate an issue response depending on received request
   */
   extern task do_issue_resp();

   /**
    * Generate the result response independent of instruction received
   */
   extern task do_result_resp();

   /**
    * Generate the result response depending on instruction received
   */
   extern task do_instr_result();

   /**
    * Main sequence body
   */
   extern virtual task body();

endclass

task uvma_cvxif_seq_c::body();

   forever begin
      // wait for a transaction request (get is blocking)
      `uvm_info(info_tag, $sformatf("Waiting for the transaction request from monitor"), UVM_HIGH);
      p_sequencer.mm_req_fifo.get(req_item);

      //Decode the instruction received
      instr = decode(req_item.issue_req.instr);

      // generate response based on observed request, e.g:
      if (instr == "illegal" || instr == "") begin
         do_default();
      end
      else begin
         if (req_item.issue_valid && req_item.issue_ready) begin
            //issue_resp
            do_issue_resp();
            //result_resp
            do_result_resp();
            //send resp to sqr
            send_resp(resp_item);
         end
      end
   end

endtask

function uvma_cvxif_seq_c::new(string name="uvma_cvxif_seq");

   super.new(name);

endfunction : new

task uvma_cvxif_seq_c::do_default();

   resp_item.issue_resp.accept=0;
   resp_item.issue_resp.writeback=0;
   resp_item.issue_resp.dualwrite=0;
   resp_item.issue_resp.dualread=0;
   resp_item.issue_resp.exc=0;
   resp_item.result_valid=0;
   resp_item.result.id=0;
   resp_item.result.exc=0;
   resp_item.result.data=0;
   resp_item.result.rd=0;
   resp_item.result.we=0;
   resp_item.result.exccode=0;
   `uvm_info(info_tag, $sformatf("Sending default sequence response to sqr, accept = %d, result_valid = %d", resp_item.issue_resp.accept, resp_item.result_valid), UVM_HIGH);
   send_resp(resp_item);

endtask

task uvma_cvxif_seq_c::do_issue_resp();

   resp_item.issue_resp.dualwrite  = 0;
   resp_item.issue_resp.dualread   = 0;
   resp_item.issue_resp.exc        = 0;
   case (instr) inside
      "CUS_ADD", "CUS_ADD_MULTI", "CUS_ADD_RS3"   : begin
          resp_item.issue_resp.writeback  = 1;
          resp_item.issue_resp.accept     = 1;
        end
      "CUS_EXC", "CUS_NOP"            : begin
          resp_item.issue_resp.writeback  = 0;
          resp_item.issue_resp.accept     = 1;
        end
      "CUS_NOP_EXC", "CUS_ISS_EXC" : begin
          resp_item.issue_resp.writeback  = 0;
          resp_item.issue_resp.accept     = 1;
          resp_item.issue_resp.exc        = 1;
        end
      "CUS_M_ADD" : begin
          if (req_item.issue_req.mode == 2'b11) begin
             resp_item.issue_resp.writeback  = 1;
             resp_item.issue_resp.accept     = 1;
          end
          else begin
             resp_item.issue_resp.writeback  = 0;
             resp_item.issue_resp.accept     = 0;
          end
        end
      "CUS_S_ADD" : begin
          if (req_item.issue_req.mode == 2'b01) begin
             resp_item.issue_resp.writeback  = 1;
             resp_item.issue_resp.accept     = 1;
          end
          else begin
             resp_item.issue_resp.writeback  = 0;
             resp_item.issue_resp.accept     = 0;
          end
        end
   endcase
   `uvm_info(info_tag, $sformatf("instr =  %s", instr), UVM_LOW);

endtask

task uvma_cvxif_seq_c::do_result_resp();

   //result_resp
   if (!req_item.commit_req.commit_kill && req_item.commit_valid) begin
      resp_item.result_valid=1;
      resp_item.result.id=req_item.commit_req.id;
      resp_item.result.rd=req_item.issue_req.instr[11:7];
      resp_item.result.we=resp_item.issue_resp.writeback;
      resp_item.result.data=0;
      resp_item.result_ready=req_item.result_ready;
      do_instr_result();
      if (cfg.instr_delayed) begin
         cfg.randomize(rnd_delay);
         resp_item.rnd_delay = cfg.rnd_delay;
      end
      else begin
         resp_item.rnd_delay = 0;
      end
   end
   else begin
      resp_item.result_valid=0;
      resp_item.result.id=0;
      resp_item.result.exc=0;
      resp_item.result.data=0;
      resp_item.result.rd=0;
      resp_item.result.we=0;
      resp_item.result.exccode=0;
      resp_item.rnd_delay = 0;
   end

endtask

task uvma_cvxif_seq_c::do_instr_result();

   //result response depend on instruction
   resp_item.result.exc=0;
   resp_item.result.exccode=0;
   cfg.instr_delayed = 0;
   case (instr)
      "CUS_ADD": begin
         resp_item.result.data=req_item.issue_req.rs[0] + req_item.issue_req.rs[1];
        end
      "CUS_ADD_MULTI": begin
         resp_item.result.data=req_item.issue_req.rs[0] + req_item.issue_req.rs[1];
         cfg.instr_delayed = 1;
        end
      "CUS_NOP_EXC": begin
         cfg.instr_delayed = 1;
        end
      "CUS_EXC":  begin
         resp_item.result.exc=1;
         resp_item.result.exccode[4:0] = req_item.issue_req.instr[19:15];
         resp_item.result.exccode[5] = req_item.issue_req.instr[20];
         `uvm_info(info_tag, $sformatf("EXCCODE: %d", resp_item.result.exccode), UVM_HIGH);
        end
      "CUS_ISS_EXC":  begin
         cfg.instr_delayed    = 1;
         resp_item.result.exc = 1;
         resp_item.result.exccode[4:0] = req_item.issue_req.instr[19:15];
         resp_item.result.exccode[5]   = req_item.issue_req.instr[20];
         `uvm_info(info_tag, $sformatf("EXCCODE: %d", resp_item.result.exccode), UVM_HIGH);
        end
      "CUS_ADD_RS3": begin
         resp_item.result.data=req_item.issue_req.rs[0] + req_item.issue_req.rs[1] + ( cvxif_pkg::X_NUM_RS == 3 ? req_item.issue_req.rs[2] : 0);
        end
      "CUS_M_ADD": begin
          if (req_item.issue_req.mode == 2'b11) begin
             resp_item.result.data=req_item.issue_req.rs[0] + req_item.issue_req.rs[1];
          end
        end
      "CUS_S_ADD": begin
          if (req_item.issue_req.mode == 2'b01 || req_item.issue_req.mode == 2'b11) begin
             resp_item.result.data=req_item.issue_req.rs[0] + req_item.issue_req.rs[1];
          end
        end
   endcase

endtask

task uvma_cvxif_seq_c::send_resp(uvma_cvxif_resp_item_c resp);

   resp_item.set_sequencer(p_sequencer);
   `uvm_send(resp_item);

endtask : send_resp


`endif
