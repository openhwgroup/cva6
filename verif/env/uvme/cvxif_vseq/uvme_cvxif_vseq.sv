// Copyright 2021 Thales DIS design services SAS
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
// You may obtain a copy of the License at https://solderpad.org/licenses/
//
// Original Author: Zineb EL KACIMI (zineb.el-kacimi@external.thalesgroup.com)

`ifndef __UVME_CVXIF_VSEQ_SV__
`define __UVME_CVXIF_VSEQ_SV__


class uvme_cvxif_vseq_c extends uvme_cvxif_base_vseq_c;

   `uvm_object_utils (uvme_cvxif_vseq_c)
   `uvm_declare_p_sequencer (uvma_cvxif_vsqr_c)

   string info_tag = "CVXIF_VSEQ_RESP";
   string instr;

   /**
    * Default constructor.
   */
   extern function new(string name="uvme_cvxif_vseq");

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

task uvme_cvxif_vseq_c::body();

   forever begin
      // wait for a transaction request (get is blocking)
      `uvm_info(info_tag, $sformatf("Waiting for the transaction request from monitor"), UVM_HIGH);
      p_sequencer.mm_req_fifo.get(req_item);

      //Decode the instruction received
      instr = decode(req_item.issue_req.instr);

      // generate response based on observed request, e.g:
      if (instr == "") begin
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

function uvme_cvxif_vseq_c::new(string name="uvme_cvxif_vseq");

   super.new(name);

endfunction : new

task uvme_cvxif_vseq_c::do_default();

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

task uvme_cvxif_vseq_c::do_issue_resp();

   resp_item.issue_resp.dualwrite  = 0;
   resp_item.issue_resp.dualread   = 0;
   resp_item.issue_resp.exc        = 0;
   case (instr) inside
      "CUS_ADD", "CUS_ADD_MULTI" : begin
          if (req_item.issue_req.rs_valid == 2'b11 || req_item.issue_req.rs_valid == 3'b111) begin
             resp_item.issue_resp.writeback  = 1;
             resp_item.issue_resp.accept     = 1;
          end
        end
      "CUS_ADD_RS3" : begin
          if (req_item.issue_req.rs_valid == 3'b111) begin
             resp_item.issue_resp.writeback  = 1;
             resp_item.issue_resp.accept     = 1;
          end
          else begin
             resp_item.issue_resp.writeback  = 0;
             resp_item.issue_resp.accept     = 1;
             resp_item.issue_resp.exc        = 1;
          end
        end
      "CUS_NOP" : begin
          resp_item.issue_resp.writeback  = 0;
          resp_item.issue_resp.accept     = 1;
        end
      "CUS_EXC" : begin
          resp_item.issue_resp.writeback  = 0;
          resp_item.issue_resp.accept     = 1;
          resp_item.issue_resp.exc        = 1;
        end
      "CUS_U_ADD" : begin
          if (req_item.issue_req.mode == PRIV_LVL_U && req_item.issue_req.rs_valid == 2'b11 || req_item.issue_req.rs_valid == 3'b111) begin
             resp_item.issue_resp.writeback  = 1;
             resp_item.issue_resp.accept     = 1;
          end
          else begin
             resp_item.issue_resp.writeback  = 0;
             resp_item.issue_resp.accept     = 1;
             resp_item.issue_resp.exc        = 1;
          end
        end
      "CUS_S_ADD" : begin
          if (req_item.issue_req.mode == PRIV_LVL_S && req_item.issue_req.rs_valid == 2'b11 || req_item.issue_req.rs_valid == 3'b111) begin
             resp_item.issue_resp.writeback  = 1;
             resp_item.issue_resp.accept     = 1;
          end
          else begin
             resp_item.issue_resp.writeback  = 0;
             resp_item.issue_resp.accept     = 1;
             resp_item.issue_resp.exc        = 1;
          end
        end
      "ILLEGAL" : begin
          resp_item.issue_resp.writeback  = 0;
          resp_item.issue_resp.accept     = 1;
          resp_item.issue_resp.exc        = 1;
        end
   endcase
   `uvm_info(info_tag, $sformatf("instr =  %s", instr), UVM_LOW);
   `uvm_info(info_tag, $sformatf("Response :  accept = %h	writeback = %h	dualwrite = %h	dualread = %h	exc = %h",
				resp_item.issue_resp.accept, resp_item.issue_resp.writeback, resp_item.issue_resp.dualwrite, resp_item.issue_resp.dualread, resp_item.issue_resp.exc), UVM_LOW);

endtask

task uvme_cvxif_vseq_c::do_result_resp();

   //result_resp
   if (!req_item.commit_req.commit_kill && req_item.commit_valid) begin
      resp_item.result_valid = 1;
      resp_item.result.id = req_item.commit_req.id;
      resp_item.result.rd = req_item.issue_req.instr[11:7];
      resp_item.result.we = resp_item.issue_resp.writeback;
      resp_item.result.data = 0;
      resp_item.result_ready = req_item.result_ready;
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
      resp_item.result_valid = 0;
      resp_item.result.id = 0;
      resp_item.result.exc = 0;
      resp_item.result.data = 0;
      resp_item.result.rd = 0;
      resp_item.result.we = 0;
      resp_item.result.exccode = 0;
      resp_item.rnd_delay = 0;
   end

endtask

task uvme_cvxif_vseq_c::do_instr_result();

   //result response depend on instruction
   resp_item.result.exc = 0;
   resp_item.result.exccode = 0;
   cfg.instr_delayed = 0;
   case (instr)
      "CUS_ADD": begin
         if (req_item.issue_req.rs_valid == 2'b11 || req_item.issue_req.rs_valid == 3'b111)
            resp_item.result.data = req_item.issue_req.rs[0] + req_item.issue_req.rs[1];
         else begin
            resp_item.result.exc = 1;
            resp_item.result.exccode[5:0] = 6'b000010; //Exception Illegal instruction
            `uvm_info(info_tag, $sformatf("Exception Illegal instruction -> EXCCODE: %d", resp_item.result.exccode), UVM_LOW);
         end
        end
      "CUS_ADD_MULTI": begin
         if (req_item.issue_req.rs_valid == 2'b11 || req_item.issue_req.rs_valid == 3'b111) begin
            resp_item.result.data = req_item.issue_req.rs[0] + req_item.issue_req.rs[1];
            cfg.instr_delayed = 1;
         end
         else begin
            resp_item.result.exc = 1;
            resp_item.result.exccode[5:0] = 6'b000010; //Exception Illegal instruction
            `uvm_info(info_tag, $sformatf("Exception Illegal instruction -> EXCCODE: %d", resp_item.result.exccode), UVM_LOW);
         end
        end
      "CUS_EXC":  begin
         resp_item.result.exc = 1;
         resp_item.result.exccode[4:0] = req_item.issue_req.instr[19:15];
         resp_item.result.exccode[5] = 1'b0;
         `uvm_info(info_tag, $sformatf("EXCCODE: %d", resp_item.result.exccode), UVM_LOW);
        end
      "CUS_ADD_RS3": begin
         if (req_item.issue_req.rs_valid == 3'b111)
            resp_item.result.data = req_item.issue_req.rs[0] + req_item.issue_req.rs[1] + req_item.issue_req.rs[2];
         else begin
            resp_item.result.exc = 1;
            resp_item.result.exccode[5:0] = 6'b000010; //Exception Illegal instruction
            `uvm_info(info_tag, $sformatf("Exception Illegal instruction -> EXCCODE: %d", resp_item.result.exccode), UVM_LOW);
         end
        end
      "CUS_U_ADD": begin
          if (req_item.issue_req.mode == PRIV_LVL_U && req_item.issue_req.rs_valid == 2'b11 || req_item.issue_req.rs_valid == 3'b111)
             resp_item.result.data = req_item.issue_req.rs[0] + req_item.issue_req.rs[1];
          else begin
             resp_item.result.exc = 1;
             resp_item.result.exccode[5:0] = 6'b000010; //Exception Illegal instruction
             `uvm_info(info_tag, $sformatf("Exception Illegal instruction -> EXCCODE: %d", resp_item.result.exccode), UVM_LOW);
          end
        end
      "CUS_S_ADD": begin
          if (req_item.issue_req.mode == PRIV_LVL_S && req_item.issue_req.rs_valid == 2'b11 || req_item.issue_req.rs_valid == 3'b111)
             resp_item.result.data = req_item.issue_req.rs[0] + req_item.issue_req.rs[1];
          else begin
             resp_item.result.exc = 1;
             resp_item.result.exccode[5:0] = 6'b000010; //Exception Illegal instruction
             `uvm_info(info_tag, $sformatf("Exception Illegal instruction -> EXCCODE: %d", resp_item.result.exccode), UVM_LOW);
          end
        end
      "ILLEGAL": begin
          resp_item.result.exc = 1;
          resp_item.result.exccode[5:0] = 6'b000010; //Exception Illegal instruction
          `uvm_info(info_tag, $sformatf("Exception Illegal instruction -> EXCCODE: %d", resp_item.result.exccode), UVM_LOW);
        end
   endcase

endtask

task uvme_cvxif_vseq_c::send_resp(uvma_cvxif_resp_item_c resp);

   resp_item.set_sequencer(p_sequencer);
   `uvm_send(resp_item);

endtask : send_resp


`endif
