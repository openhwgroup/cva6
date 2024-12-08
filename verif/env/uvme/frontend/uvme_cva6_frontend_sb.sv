// Copyright 2024 Thales DIS SAS
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
//
// Original Author: Alae Eddine EZ ZEJJARI (alae-eddine.ez-zejjari@external.thalesgroup.com) – sub-contractor MU-Electronics for Thales group


`ifndef __UVME_CVA6_FRONTEND_SB_SV__
`define __UVME_CVA6_FRONTEND_SB_SV__


// Frontend Scoreboard
// The scoreboard contains a frontend model and monitor of the Frontend interface
// The scoreboard captures the decoded committed instructions using an analysis port and counts all instruction types.
// It also captures transactions monitored through an analysis port and counts all types of instructions sent to the decode stage, requests sent to the cache, and cache responses.
class uvme_cva6_frontend_sb_c extends uvm_scoreboard;

   // Objects
   uvme_cva6_cfg_c    cfg;

   uvm_tlm_analysis_fifo#(uvma_isacov_mon_trn_c)             isa_trn_fifo;
   uvm_tlm_analysis_fifo#(uvme_cva6_frontend_transaction_c)  frontend_trn_fifo;
   uvma_isacov_mon_trn_c#(ILEN,XLEN)      isa_instr;
   uvme_cva6_frontend_transaction_c       frontend_instr;

   uvme_cva6_frontend_model_c   frontend_model;
   uvme_cva6_frontend_mon_c     frontend_mon;

   int fetched_inst_count;
   int req_cache_inst_count;
   int cached_inst_count;
   int axi_inst_count;
   int mispredict_count;
   int branch_inst_count;
   int branch_mispredict_count;
   int ret_inst_count;
   int ret_mispredict_count;
   int jump_inst_count;
   int jump_mispredict_count;
   int isa_inst_count;

   `uvm_component_utils_begin(uvme_cva6_frontend_sb_c)
   `uvm_component_utils_end

   /**
    * Default constructor.
    */
   function new(string name="uvme_cva6_frontend_sb_c", uvm_component parent=null);
         super.new(name, parent);
   endfunction

   /**
    * Create and configures sub-scoreboards via:
    */
   virtual function void build_phase(uvm_phase phase);

      void'(uvm_config_db#(uvme_cva6_cfg_c)::get(this, "", "cfg", cfg));
      if (!cfg)
         `uvm_fatal("CFG", "Configuration handle is null")

      isa_trn_fifo          = new("isa_trn_fifo", this);
      frontend_trn_fifo     = new("frontend_trn_fifo", this);

      this.frontend_mon = uvme_cva6_frontend_mon_c::type_id::create("frontend_mon", this);
      if(cfg.enable_frontend_model) begin
         this.frontend_model = uvme_cva6_frontend_model_c::type_id::create("frontend_model", this);
      end

   endfunction

   /**
    * Connect the analysis port
    */
   function void connect_phase(uvm_phase phase);

      super.connect_phase(phase);

      //Establishing connections between monitor ports and scoreboard
      frontend_mon.frontend_packets_collected.connect(this.frontend_trn_fifo.analysis_export);
      if( cfg.enable_frontend_model) begin
         //Establishing connections between monitor ports and model if the model is enabled
         this.frontend_mon.frontend_packets_collected.connect(frontend_model.mon2mod_export);
         `uvm_info(get_type_name(), $sformatf("FRENTEND MODEL IS ACTIVE"), UVM_LOW)
      end

   endfunction

   /**
    * Frontend-scoreboard run phase.
    */
   task run_phase(uvm_phase phase);
      super.run_phase(phase);
      fork
         begin
            // Count the instruction coming from the isacove
            forever begin
               isa_trn_fifo.get(isa_instr);
               isa_inst_count++;
               if(isa_instr.instr.group == BRANCH_GROUP)
                  branch_inst_count++;
               else if(isa_instr.instr.group == RET_GROUP)
                  ret_inst_count++;
               else if(isa_instr.instr.group == JUMP_GROUP)
                  jump_inst_count++;
            end
         end
         begin
            // Count the instruction coming from the Frontend
            forever begin
               frontend_trn_fifo.get(frontend_instr);
               scoreboarding_frontend();
            end
         end
      join_any
   endtask


   function void scoreboarding_frontend();

      if(frontend_instr.icache_req.valid) cached_inst_count++;

      if(frontend_instr.icache_rsp.req && frontend_instr.icache_req.ready) req_cache_inst_count++;

      for(int i = 0; i < RTLCVA6Cfg.NrIssuePorts; i++) begin
         if(frontend_instr.fetch_valid[i] && frontend_instr.fetch_ready[i]) fetched_inst_count++;
      end

      if(frontend_instr.resolve_branch.is_mispredict) mispredict_count++;

      if(frontend_instr.resolve_branch.is_mispredict && frontend_instr.resolve_branch.cf_type == 1) branch_mispredict_count++;

      if(frontend_instr.resolve_branch.is_mispredict && frontend_instr.resolve_branch.cf_type == 4) ret_mispredict_count++;

      if(frontend_instr.resolve_branch.is_mispredict && (frontend_instr.resolve_branch.cf_type == 2 || frontend_instr.resolve_branch.cf_type == 3)) jump_mispredict_count++;

   endfunction : scoreboarding_frontend

   /**
    * Disply the final results of the scoreboarding
    */
   function void check_phase(uvm_phase phase);

      super.check_phase(phase);
      `uvm_info("Frontend scorboard checks", $sformatf("number of fetch requested by the frotend req_cache_inst_count = %d", req_cache_inst_count), UVM_NONE)
      `uvm_info("Frontend scorboard checks", $sformatf("number of fetch sent by the cache cached_inst_count = %d", cached_inst_count), UVM_NONE)
      `uvm_info("Frontend scorboard checks", $sformatf("number of instruction sent to decode fetched_inst_count = %d", fetched_inst_count), UVM_NONE)
      `uvm_info("Frontend scorboard checks", $sformatf("number of instruction seen in the isa isa_inst_count = %d", isa_inst_count), UVM_NONE)
      `uvm_info("Frontend scorboard checks", $sformatf("number of mispredict seen in the execut stage mispredict_count = %d", mispredict_count), UVM_NONE)
      `uvm_info("Frontend scorboard checks", $sformatf("number of branch instruction seen in the isa branch_inst_count = %d", branch_inst_count), UVM_NONE)
      `uvm_info("Frontend scorboard checks", $sformatf("number of branch mispredict seen in the execute stage branch_commit_count = %d", branch_mispredict_count), UVM_NONE)
      `uvm_info("Frontend scorboard checks", $sformatf("number of ret instruction seen in the isa ret_inst_count = %d", ret_inst_count), UVM_NONE)
      `uvm_info("Frontend scorboard checks", $sformatf("number of ret mispredict seen in the execute stage ret_commit_count = %d", ret_mispredict_count), UVM_NONE)
      `uvm_info("Frontend scorboard checks", $sformatf("number of ret instruction seen in the isa jump_inst_count = %d", jump_inst_count), UVM_NONE)
      `uvm_info("Frontend scorboard checks", $sformatf("number of jump mispredict seen in the execute stage jump_mispredict_count = %d", jump_mispredict_count), UVM_NONE)
   endfunction

endclass : uvme_cva6_frontend_sb_c
`endif // __UVME_CVA6_FRONTEND_SB_SV__
